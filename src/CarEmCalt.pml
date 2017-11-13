/* tipo di richiesta */
#define REQUEST 0
#define RELEASE 1

#define BUSY 0
#define FARAWAY 0
#define AVAILABLE 1


/* definizioni per formule LTL */
#define ces1_start 	(ces[ces_pid1]@start)
#define ces2_start 	(ces[ces_pid2]@start)
#define ces1_rel 	(ces[ces_pid1]@rel)
#define ces2_rel 	(ces[ces_pid2]@rel)

#define max_one_g1 (!(ces[ces_pid1]:pid_garage == g_pid1 && ces[ces_pid2]:pid_garage == g_pid1))
#define max_one_g2 (!(ces[ces_pid1]:pid_garage == g_pid2 && ces[ces_pid2]:pid_garage == g_pid2))
#define max_one_tt (!(ces[ces_pid1]:pid_towtruck == tt_pid && ces[ces_pid2]:pid_towtruck == tt_pid))
#define max_one_rc (!(ces[ces_pid1]:pid_rentalcar == rc_pid && ces[ces_pid2]:pid_rentalcar == rc_pid))

#define ces1_damage (ces[ces_pid1]@damage)
#define ces2_damage (ces[ces_pid2]@damage)

#define g1_start	(garage[g_pid1]@start)
#define	g2_start	(garage[g_pid2]@start)

#define g1_not_reach	(!(towtruck:locs >> (garage[g_pid1]:loc) & 1))
#define g2_not_reach	(!(towtruck:locs >> (garage[g_pid2]:loc) & 1))
#define ces1_not_reach	(!(towtruck:locs >> (ces[ces_pid1]:loc) & 1))
#define ces2_not_reach	(!(towtruck:locs >> (ces[ces_pid2]:loc) & 1))

#define ces1_succ	(ces[ces_pid1]@succ)
#define ces2_succ	(ces[ces_pid2]@succ)

#define ces1_no_book_tt	(ces[ces_pid1]:pid_towtruck != tt_pid)
#define ces2_no_book_tt	(ces[ces_pid2]:pid_towtruck != tt_pid)
#define ces1_no_book_rc	(ces[ces_pid1]:pid_rentalcar != rc_pid)
#define ces2_no_book_rc	(ces[ces_pid2]:pid_rentalcar != rc_pid)

#define ces1_tt 	((towtruck:locs >> (ces[ces_pid1]:loc) & 1) && (towtruck:locs >> (ces[ces_pid1]:loc_garage) & 1))
#define ces2_tt 	((towtruck:locs >> (ces[ces_pid2]:loc) & 1) && (towtruck:locs >> (ces[ces_pid2]:loc_garage) & 1))
#define ces1_rc 	((rentalcar:locs >> (ces[ces_pid1]:loc) & 1) || (rentalcar:locs >> (ces[ces_pid1]:loc_garage) & 1))
#define ces2_rc 	((rentalcar:locs >> (ces[ces_pid2]:loc) & 1) || (rentalcar:locs >> (ces[ces_pid2]:loc_garage) & 1))


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

/* canali officine */
chan garage_chs [NGARAGE] = [0] of {bit, mtype, byte, byte};

/* canale carro attrezzi */
chan towtruck_ch = [0] of {bit, mtype, mtype, byte, byte};

/* canale noleggio auto */
chan rentalcar_ch = [0] of {bit, byte, byte, byte};


/* variabili globali accedute localmente all'interno dell'init
   indicano il pid dei servizi */
local byte ces_pid1 = 0;
local byte ces_pid2 = 0;
local byte g_pid1 = 0;
local byte g_pid2 = 0;
local byte tt_pid = 0;
local byte rc_pid = 0;


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

		/* scelta non deterministica se è abbonato o meno */
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
			garage_chs[idg] ! REQUEST, 0, 0, _pid;
			garage_chs[idg] ? result, loc_garage, pid_garage, eval(_pid);
			if
			/* officina prenotata */
			:: result -> goto reqTT
			/* officina occupata, continuo ad iterare */
			:: !result -> skip
			fi
		}
		/* se viene raggiunto questo punto allora tutte le prenotazioni sono fallite */
		goto fail;
		
		/* tentativo di prenotazione del carro attrezzi */
reqTT:	towtruck_ch ! REQUEST, loc, loc_garage, 0, _pid;
		towtruck_ch ? result, _, _, pid_towtruck, eval(_pid);
		if
		/* carro attrezzi prenotato */
		:: result -> skip
		/* carro attrezzi occupato, prenotazione fallita */
		:: !result -> goto fail
		fi;

		/* tentativo di prenotazione del noleggio auto */
reqRC:	rentalcar_ch ! REQUEST, toByteLoc(loc_garage, loc), 0, _pid;
		rentalcar_ch ? result, _, pid_rentalcar, eval(_pid);
		/* sia in caso di fallimento della prenotazione, sia in caso di successo
	   	   procedo con la riparazione
	       nota: se result == true allora pid_rentalcar != 0, ovvero vale
	   	   assert(!result || (pid_rentalcar != 0)); */

	    /* workflow è terminato con successo */
succ:	goto rel;

fail:	skip;
		/* release dei servizi prenotati */
rel:	if
		:: pid_garage != 0 ->
			garage_chs[idg] ! RELEASE, loc_garage, pid_garage, _pid;
			garage_chs[idg] ? AVAILABLE, _, pid_garage, eval(_pid);
			if
			:: pid_towtruck != 0 ->
				towtruck_ch ! RELEASE, loc, loc_garage, pid_towtruck, _pid;
				towtruck_ch ? AVAILABLE, _, _, pid_towtruck, eval(_pid)
			:: else -> skip
			fi;
			if
			:: pid_rentalcar != 0 ->
				rentalcar_ch ! RELEASE, toByteLoc(loc_garage, loc), pid_rentalcar, _pid;
				rentalcar_ch ? AVAILABLE, _, pid_rentalcar, eval(_pid)
			:: else -> skip
			fi;
			loc_garage = 0
		:: else -> skip
		fi;
		goto damage
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
		/* indica la locazione della richiesta */
		mtype where = 0;
		/* indicano il pid del ces che fa la richiesta */
		byte who, bwho;
		
start:	skip;
waitG:	atomic { ch ? REQUEST, _, _, who;
		ch ! AVAILABLE, loc, _pid, who };

bookG:	do
		/* il messaggio di release deve avere la locazione ed il pid del servizio e il pid del ces*/
		:: atomic { ch ? RELEASE, eval(loc), eval(_pid), eval(who) ->
			ch ! AVAILABLE, 0, 0, who } ;
			goto waitG
		:: atomic { ch ? REQUEST, _, _, bwho ->
			ch ! BUSY, 0, 0, bwho }
		od
}



/* servizio carro attrezzi, inizialmente disponibile
   che può operare in una o più locazioni */
proctype towtruck(chan ch; byte locs)
{
		/* indica le locazioni della richiesta */
		mtype from = 0, to = 0;
		/* indicano il pid del ces che fa la richiesta */
		byte who, bwho;

waitTT:	atomic { ch ? REQUEST, from, to, _, who;
		/* utilizzo la conditional expression per mantenere l'atomicità */
		ch ! ((validLoc(locs, from) && validLoc(locs, to)) -> AVAILABLE : FARAWAY), 
			 ((validLoc(locs, from) && validLoc(locs, to)) -> from : 0),
			 ((validLoc(locs, from) && validLoc(locs, to)) -> to : 0),
			 ((validLoc(locs, from) && validLoc(locs, to)) -> _pid : 0), 
			  who };
		/* poi distinguo il comportamento in base alle locazioni */
		if
		/* se le locazioni sono entrambe tra quelle su cui
		   il servizio opera, allora è prenotabile  */
		:: (validLoc(locs, from) && validLoc(locs, to)) -> skip
			/* esce dall'if e procede all'etichetta bookTT */
		/* altrimenti la prenotazione è fallita */
		:: else -> goto waitTT
		fi;

bookTT:	do
		/* il messaggio di release deve avere le locazioni specificate nella, il pid del servizio e il pid del ces*/
		:: atomic { ch ? RELEASE, eval(from), eval(to), eval(_pid), eval(who) ->
			ch ! AVAILABLE, 0, 0, 0, who } ;
			goto waitTT
		:: atomic { ch ? REQUEST, _, _, _, bwho ->
			ch ! BUSY, 0, 0, 0, bwho }
		od
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
		/* indicano il pid del ces che fa la richiesta */
		byte who, bwho;
		
		/* scelta nonderminisica dello stato */
		if
		:: state = false
		:: state = true
		fi;
		
waitRC:	if
		/* se è disponibile allora potrebbe essere prenotato */
		:: state ->
			atomic { ch ? REQUEST, where, _, who;
			/* utilizzo la conditional expression per mantenere l'atomicità */
			ch ! (oneValidLoc(locs, where) -> AVAILABLE : FARAWAY),
				 (oneValidLoc(locs, where) -> where : 0),
				 (oneValidLoc(locs, where) -> _pid : 0),
				 who };
			/* poi distinguo il comportamento in base alle locazioni */
			if
			/* se almeno una delle locazioni è tra quelle su cui
		   	   il servizio opera, allora è prenotabile  */
			:: oneValidLoc(locs, where) -> skip
				/* esce dall'if annidato */
			/* altrimenti la prenotazione è fallita */
			:: else -> goto waitRC
			fi
			/* esce dall'if e procede all'etichetta bookRC */
		/* altrimenti è occupato */
		:: !state ->
busyRC:		atomic { ch ? REQUEST, _, _, who;
			ch ! BUSY, 0, 0, who };
			/* salto ed aspetto la prossima richiesta di servizio  */
			goto busyRC
		fi;

bookRC:	do
		/* il messaggio di release deve avere le locazioni specificate nella richiesta, il pid del servizio e il pid del ces*/
		:: atomic {ch ? RELEASE, eval(where), eval(_pid), eval(who) ->
			ch ! AVAILABLE, 0, 0, who } ;
			goto waitRC
		:: atomic { ch ? REQUEST, _, _, bwho ->
			ch ! BUSY, 0, 0, bwho }
		od
}


/* inizializzazione */
init {
	/* variabile che contiene una delle posizioni dello scenario */
	mtype city;

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
#ifdef CES1
		/* scelta non-deterministica della locazione del primo ces */
		select(city : 1 .. 4);
		ces_pid1 = run ces(city);	
#else
		ces_pid1 = run ces(Pisa);
#endif
#ifdef CES2
		/* scelta non-deterministica della locazione del secondo ces */
		select(city : 1 .. 4);
		ces_pid2 = run ces(city);
#else
		ces_pid2 = run ces(Livorno);
#endif
		run creditcard(creditcard_ch);
#ifdef GARAGE1
		/* scelta non-deterministica della locazione della prima officina */
		select(city : 1 .. 4);
		g_pid1 = run garage(garage_chs[0], city);
#else
		g_pid1 = run garage(garage_chs[0], Pisa);
#endif

#ifdef GARAGE2
		/* scelta non-deterministica della locazione della seconda officina */
		select(city : 1 .. 4);
		g_pid2 = run garage(garage_chs[1], city);
#else
		g_pid2 = run garage(garage_chs[1], Livorno);
#endif

/* se una delle due macro è definita testo una sola configurazione per evitare
   l'esplosione combinatoria */
#ifdef TOWTRUCK
		/* scelta non-deterministica delle locazioni servite dal carro attrezzi */
		zone = 2;
		do
		:: zone < 30 -> zone = zone + 2
		:: break
		od;
		tt_pid = run towtruck(towtruck_ch, zone);
#else
		/* 28 -> Pisa, Livorno e Lucca */
		tt_pid = run towtruck(towtruck_ch, 28);
#endif

#ifdef RENTALCAR
		/* scelta non-deterministica delle locazioni servite dal noleggio auto */
		zone = 2;
		do
		:: zone < 30 -> zone = zone + 2
		:: break
		od;
		rc_pid = run rentalcar(rentalcar_ch, zone)
#else
		/* 20 -> Pisa e Lucca */
		rc_pid = run rentalcar(rentalcar_ch, 20)
#endif
	}
}


/* proprietà LTL */
ltl prop_d0 { [](max_one_g1 && max_one_g2 && max_one_tt && max_one_rc) }
/* Absence, after (ces1_start && ces2_start) */
ltl prop_d { []((ces1_start && ces2_start) -> [](max_one_g1 && max_one_g2 && max_one_tt && max_one_rc)) }
ltl prop_e { []<>ces1_damage && []<>ces2_damage }
ltl prop_g { !<>[]np_ }

/* Absence, after : [](Q -> [](!P)) */
ltl prop_h { []((g1_start && g2_start && g1_not_reach && g2_not_reach) -> []!(ces1_succ || ces2_succ)) }
ltl prop_i { []((ces1_start && ces1_not_reach) -> []ces1_no_book_tt) && []((ces2_start && ces2_not_reach) -> []ces2_no_book_tt) }
ltl prop_j { []((ces1_start && ces1_not_reach) -> []!ces1_succ) && []((ces2_start && ces2_not_reach) -> []!ces2_succ) }
/*  Precedence, after Q until R: [](Q & !R -> (!P W (S | R))) */
ltl prop_k { []((ces1_damage && !ces1_rel) -> (ces1_no_book_tt W (ces1_tt || ces1_rel))) &&
			 []((ces2_damage && !ces2_rel) -> (ces2_no_book_tt W (ces2_tt || ces2_rel))) }
ltl prop_l { []((ces1_damage && !ces1_rel) -> (ces1_no_book_rc W (ces1_rc || ces1_rel))) &&
			 []((ces2_damage && !ces2_rel) -> (ces2_no_book_rc W (ces2_rc || ces2_rel))) }
