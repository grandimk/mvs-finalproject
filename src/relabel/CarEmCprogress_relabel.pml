/* tipo di richiesta */
#define REQUEST 0
#define RELEASE 1

#define BUSY 0
#define FARAWAY 0
#define AVAILABLE 1


/* macro per testare se un servizio è non prenotato */
#define notBooked(v, n)	(!(v >> (n) & 1))
/* macro per prenotare e rilasciare un servizio */
#define Book(v, n)		v = v | (1 << (n))
#define Cancel(v, n)	v = v & ~(1 << (n))

/* macro per creare una variabile byte in cui sono ad uno
   i bit delle locazioni passate come argomento */
#define toByteLoc(l1, l2)	((1 << (l1)) | (1 << (l2)))
/* macro per testare se una locazione è coperta */
#define validLoc(z, l)  	(z >> (l) & 1)
#define oneValidLoc(z, l)	((z & l) != 0)


/* numero di garage */
#define NGARAGE 2


/* tipo locazione */
mtype = { Pisa, Livorno, Lucca, Firenze }


/* canale carta di credito */
chan creditcard_ch = [0] of {bit};

/* canali officine:
   il campo mtype serve ad inviare la locazione dell'officina */
chan garage_chs [NGARAGE] = [0] of {bit, mtype, byte};

/* canale carro attrezzi:
   i canali mype servono per indicare da dove a dove
   il carro attrezzi deve operare */
chan towtruck_ch = [0] of {bit, mtype, mtype, byte};

/* canale noleggio auto:
   il secondo campo byte rappresenta un array che
   contiene la locazione dove è avvenuto il guasto
   e dove è situata l'officina */
chan rentalcar_ch = [0] of {bit, byte, byte};


/* variabili globali accedute localmente all'interno dell'init
   indicano il pid dei servizi */
local byte ces_pid1 = 0;
local byte ces_pid2 = 0;
local byte g_pid1 = 0;
local byte g_pid2 = 0;
local byte tt_pid = 0;
local byte rc_pid = 0;


/* variabili che indicano se un ces ha prenotato un servizio;
   per le officine utilizziamo una variabile di tipo byte e
   il test è effettuato con la macro sopra definita
   NOTA: la scelta di avere una variabile di tipo byte limita
   		 il numero di servizi di una tipologia al più 8 */
byte garage_booked = 0;

bool towtruck_booked = false;

bool rentalcar_booked = false;


/* car emergency system */
proctype ces(mtype loc)
{
		/* ha un abbonamento? */
		bool subscribing;
		bool result;
		/* pid dei servizi prenotati:
		   se pid == 0 allora il servizio non è prenotato
		   altrimenti il pid è usato come ricevuta di prenotazione */
		byte pid_garage = 0, pid_towtruck = 0, pid_rentalcar = 0;
		/* indice del canale dei servizi prenotati (per servizi con più istanze) */
		byte idg = 0;
		/* indica la posizione dell'officina prenotata */
		mtype loc_garage = 0;

		/* scelta non-deterministica se è abbonato o meno */
start:	if
		:: subscribing = false
		:: subscribing = true
		fi;

damage:	if
		/* è abbonato */
		:: subscribing ->
sub:		skip
		/* non è abbonato, richiedo l'autorizzazione per la
	   	   prenotazione con carta di credito */
		:: !subscribing ->
			creditcard_ch ! REQUEST;
			creditcard_ch ? result;
			if
			/* autorizzazione ottenuta */
			:: result -> 
auth:			skip
			/* autorizzazione negata */
			:: !result -> goto fail
			fi
		fi;

		/* tentativo di prenotazione dell'officina */
reqG:	for(idg in garage_chs) {
			if
			/* se la idg-esima officina non è prenotata da un altro ces
			   ottengo il canala di comunicazione in mutua esclusione */
			:: atomic { notBooked(garage_booked, idg) ->
				Book(garage_booked, idg) };
				garage_chs[idg] ! REQUEST, 0, 0;
				garage_chs[idg] ? result, loc_garage, pid_garage;
				if
				/* officina prenotata */
				:: result -> goto reqTT
				/* officina occupata o locazione diversa, la rilascio e continuo ad iterare */
				:: !result -> Cancel(garage_booked, idg)
				fi
			/* altrimenti continuo ad iterare */
			:: else -> skip
			fi
		}
		loc_garage = 0;
		/* se viene raggiunto questo punto allora tutte le prenotazioni sono fallite */
		goto fail;
		
		/* tentativo di prenotazione del carro attrezzi */
reqTT:	if
		:: atomic { !towtruck_booked ->
			towtruck_booked = true };
			towtruck_ch ! REQUEST, loc, loc_garage, 0;
			towtruck_ch ? result, _, _, pid_towtruck;
			if
			/* carro attrezzi prenotato */
			:: result -> skip
			/* carro attrezzi occupato o locazione non coperta, prenotazione fallita */
			:: !result -> towtruck_booked = false;
				goto fail
			fi
		/* se il servizio è già prenotato, la richiesta è fallita */
		:: else -> goto fail
		fi;

		/* tentativo di prenotazione del noleggio auto */
reqRC:	if
		:: atomic { !rentalcar_booked ->
			rentalcar_booked = true };
			rentalcar_ch ! REQUEST, toByteLoc(loc_garage, loc), 0;
			rentalcar_ch ? result, _, pid_rentalcar;
			if
			:: result -> skip
			:: !result -> rentalcar_booked = false
			fi
			/* sia in caso di fallimento della prenotazione, sia in caso di successo
		   	   procedo con il workflow
		       nota: se result == true allora pid_rentalcar != 0, ovvero vale
		   	   assert(!result || (pid_rentalcar != 0)); */
	   	/* se il servizio è già prenotato, continuo con il workflow */
	   	:: else -> skip
	    fi;

	    /* workflow è terminato con successo */
succ:	goto rel;

fail:	skip;
		/* release dei servizi prenotati */
rel:	if
		:: pid_garage != 0 ->
			garage_chs[idg] ! RELEASE, loc_garage, pid_garage;
			garage_chs[idg] ? AVAILABLE, _, pid_garage;
			Cancel(garage_booked, idg);
			if
			:: pid_towtruck != 0 ->
				towtruck_ch ! RELEASE, loc, loc_garage, pid_towtruck;
				towtruck_ch ? AVAILABLE, _, _, pid_towtruck;
				towtruck_booked = false
			:: else -> skip
			fi;
			if
			:: pid_rentalcar != 0 ->
				rentalcar_ch ! RELEASE, toByteLoc(loc_garage, loc), pid_rentalcar;
				rentalcar_ch ? AVAILABLE, _, pid_rentalcar;
				rentalcar_booked = false
			:: else -> skip
			fi;
			loc_garage = 0
		:: else -> skip
		fi;
		goto damage
}


/* car emergency system con progress label */
proctype cesP(mtype loc)
{
		/* ha un abbonamento? */
		bool subscribing;
		bool result;
		/* pid dei servizi prenotati:
		   se pid == 0 allora il servizio non è prenotato
		   altrimenti il pid è usato come ricevuta di prenotazione */
		byte pid_garage = 0, pid_towtruck = 0, pid_rentalcar = 0;
		/* indice del canale dei servizi prenotati (per servizi con più istanze) */
		byte idg = 0;
		/* indica la posizione dell'officina prenotata */
		mtype loc_garage = 0;

		/* scelta non-deterministica se è abbonato o meno */
startP:	if
		:: subscribing = false
		:: subscribing = true
		fi;

damageP:if
		/* è abbonato */
		:: subscribing ->
subP:		skip
		/* non è abbonato, richiedo l'autorizzazione per la
	   	   prenotazione con carta di credito */
		:: !subscribing ->
			creditcard_ch ! REQUEST;
			creditcard_ch ? result;
			if
			/* autorizzazione ottenuta */
			:: result -> 
authP:			skip
			/* autorizzazione negata */
			:: !result -> goto failP
			fi
		fi;
#ifdef ALL
progressCC:	skip;
#endif

		/* tentativo di prenotazione dell'officina */
reqGP:	for(idg in garage_chs) {
			if
			/* se la idg-esima officina non è prenotata da un altro ces
			   ottengo il canala di comunicazione in mutua esclusione */
			:: atomic { notBooked(garage_booked, idg) ->
				Book(garage_booked, idg) };
				garage_chs[idg] ! REQUEST, 0, 0;
				garage_chs[idg] ? result, loc_garage, pid_garage;
				if
				/* officina prenotata */
				:: result ->
#ifdef ALL
progressG:			goto reqTTP
#else
					goto reqTTP
#endif
				/* officina occupata o locazione diversa, la rilascio e continuo ad iterare */
				:: !result -> Cancel(garage_booked, idg)
				fi
			/* altrimenti continuo ad iterare */
			:: else -> skip
			fi
		}
		loc_garage = 0;
		/* se viene raggiunto questo punto allora tutte le prenotazioni sono fallite */
		goto failP;
		
		/* tentativo di prenotazione del carro attrezzi */
reqTTP:	if
		:: atomic { !towtruck_booked ->
			towtruck_booked = true };
			towtruck_ch ! REQUEST, loc, loc_garage, 0;
			towtruck_ch ? result, _, _, pid_towtruck;
			if
			/* carro attrezzi prenotato */
			:: result ->
progressTT:		skip
			/* carro attrezzi occupato o locazione non coperta, prenotazione fallita */
			:: !result -> towtruck_booked = false;
				goto failP
			fi
		/* se il servizio è già prenotato, la richiesta è fallita */
		:: else -> goto failP
		fi;

		/* tentativo di prenotazione del noleggio auto */
reqRCP:	if
		:: atomic { !rentalcar_booked ->
			rentalcar_booked = true };
			rentalcar_ch ! REQUEST, toByteLoc(loc_garage, loc), 0;
			rentalcar_ch ? result, _, pid_rentalcar;
			if
			:: result -> skip
			:: !result -> rentalcar_booked = false
			fi
			/* sia in caso di fallimento della prenotazione, sia in caso di successo
		   	   procedo con il workflow
		       nota: se result == true allora pid_rentalcar != 0, ovvero vale
		   	   assert(!result || (pid_rentalcar != 0)); */
	   	/* se il servizio è già prenotato, continuo con il workflow */
	   	:: else -> skip
	    fi;

	    /* workflow è terminato con successo */
succP:	goto relP;

failP:	skip;
		/* release dei servizi prenotati */
relP:	if
		:: pid_garage != 0 ->
			garage_chs[idg] ! RELEASE, loc_garage, pid_garage;
			garage_chs[idg] ? AVAILABLE, _, pid_garage;
			Cancel(garage_booked, idg);
			if
			:: pid_towtruck != 0 ->
				towtruck_ch ! RELEASE, loc, loc_garage, pid_towtruck;
				towtruck_ch ? AVAILABLE, _, _, pid_towtruck;
				towtruck_booked = false
			:: else -> skip
			fi;
			if
			:: pid_rentalcar != 0 ->
				rentalcar_ch ! RELEASE, toByteLoc(loc_garage, loc), pid_rentalcar;
				rentalcar_ch ? AVAILABLE, _, pid_rentalcar;
				rentalcar_booked = false
			:: else -> skip
			fi;
			loc_garage = 0
		:: else -> skip
		fi;
		goto damageP
}


/* servizio carta di credito
   sempre disponibile e che ha sempre successo */
proctype creditcard(chan ch)
{
waitCC:	atomic { ch ? REQUEST;
		/* le richieste hanno sempre successo */
		ch ! AVAILABLE };
		goto waitCC
}


/* servizio officina, inizialmente disponibile
   con specifica locazione */
proctype garage(chan ch; mtype loc)
{		
start:	skip;
waitG:	ch ? REQUEST, _, _;
		ch ! AVAILABLE, loc, _pid;
		/* il messaggio di release deve avere la locazione ed il pid del servizio */
bookG:	ch ? RELEASE, eval(loc), eval(_pid);
		ch ! AVAILABLE, 0, 0;
		goto waitG
}


/* servizio carro attrezzi, inizialmente disponibile
   che può operare in una o più locazioni */
proctype towtruck(chan ch; byte locs)
{
		/* indica le locazioni della richiesta */
		mtype from = 0, to = 0;

waitTT:	ch ? REQUEST, from, to, _;
		if
		/* se le locazioni sono entrambe tra quelle su cui
		   il servizio opera, allora è prenotabile  */
		:: (validLoc(locs, from) && validLoc(locs, to)) ->
			ch ! AVAILABLE, from, to, _pid;
			/* il messaggio di release deve avere le locazioni specificate nella richiesta ed il pid del servizio */
bookTT:		ch ? RELEASE, eval(from), eval(to), eval(_pid);
			ch ! AVAILABLE, 0, 0, 0
		/* altrimenti la prenotazione è fallita */
		:: else -> 
			ch ! FARAWAY, 0, 0, 0
		fi;
		goto waitTT
}


/* servizio noleggio auto
   sceglie nondeterministicamente se è disponibile od occupato */
proctype rentalcar(chan ch; byte locs)
{
		/* indica se il servizio è disponibile o meno */
		bool state;
		/* indica le locazioni della richiesta:
		   dove si trova il veicolo e dove si trova l'offina */
		byte where = 0;
		
		/* scelta nonderminisica dello stato */
		if
		:: state = false
		:: state = true
		fi;
		
waitRC:	ch ? REQUEST, where, _;
		if
		/* se è disponibile allora potrebbe essere prenotato */
		:: state -> 
			if
			/* se almeno una delle locazioni è tra quelle su cui
		   	   il servizio opera, allora è prenotabile  */
			:: oneValidLoc(locs, where) ->
				ch ! AVAILABLE, where, _pid;
				/* il messaggio di release deve avere la locazioni specificate nella richiesta ed il pid del servizio */
bookRC:			ch ? RELEASE, eval(where), eval(_pid);
				ch ! AVAILABLE, 0, 0
			/* altrimenti la prenotazione è fallita */
			:: else ->
				ch ! FARAWAY, 0, 0
			fi
		/* altrimenti è occupato */
		:: !state -> ch ! BUSY, 0, 0
		fi;
		goto waitRC
}


/* inizializzazione */
init {
	/* variabili che contengono una delle posizioni dello scenario */
	mtype city0, city1, city2, city3;

	/* variabile che contiene una delle possibili combinazioni delle posizioni dello scenario;
	   la variabile è di tipo byte ed è usata come array di posizioni:
	   		indica quali posizioni sono servite
	   NOTA: deve essere diversa da zero perché vogliamo che almeno una posiziona sia servita
		traduzione locazione/numero -> valore intero
		Pisa = 4 		-> 16
		Livorno = 3 	-> 8
		Lucca = 2		-> 4
		Firenze = 1 	-> 2
	   Se l'i-esimo elemento dell'array vale 1, la relativa locazione è servita;
       per indicare più locazione basta farne la somma dei valori interi oppure operare bitwise */
	byte zone;

	atomic {
		city0 = 1;
		ces_pid1 = run ces(city0);
		
		/* scelta non-deterministica della locazione del secondo ces */
		select(city1 : 1 .. (city0 + 1));
		ces_pid2 = run cesP(city1);

		run creditcard(creditcard_ch);

		/* scelta non-deterministica della locazione della prima officina */
		select(city2 : 1 .. (city1 + 1));
		g_pid1 = run garage(garage_chs[0], city2);

		/* scelta non-deterministica della locazione della seconda officina */
		select(city3 : 1 .. (city1 > city2 -> city1 + 1 : city2 + 1));
		g_pid2 = run garage(garage_chs[1], city3);

		/* scelta non-deterministica delle locazioni servite dal carro attrezzi */
		zone = 2;
		do
		:: zone < 30 -> zone = zone + 2
		:: break
		od;
		tt_pid = run towtruck(towtruck_ch, zone);

		/* scelta non-deterministica delle locazioni servite dal noleggio auto */
		zone = 2;
		do
		:: zone < 30 -> zone = zone + 2
		:: break
		od;
		rc_pid = run rentalcar(rentalcar_ch, zone)
	}
}


/* proprietà LTL */
ltl prop_g { !<>[]np_ }
