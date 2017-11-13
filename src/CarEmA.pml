/* tipo di richiesta */
#define REQUEST 0
#define RELEASE 1

#define BUSY 0
#define AVAILABLE 1


/* definizioni per formule LTL */
#define ces_sub   (ces@sub)
#define ces_auth  (ces@auth)
#define ces_req   (ces@reqG)

#define ces_succ  (ces@succ)
#define g1_state  (service[g_pid1]:state)
#define tt1_state (service[tt_pid1]:state)

/* se MULTI è definito considero anche il secondo servizio */
#ifdef MULTI
#define g2_state  (service[g_pid2]:state)
#define tt2_state (service[tt_pid2]:state)

#define g2_book   (service[g_pid2]@bookS)
#define tt2_book  (service[tt_pid2]@bookS)
#endif

#define ces_end   (ces@endCES)
#define g1_book   (service[g_pid1]@bookS)
#define tt1_book  (service[tt_pid1]@bookS)
#define rc_book   (service[rc_pid]@bookS)


/* macro per testare se un servizio è non prenotato */
#define notBooked(v, n)	(!(v >> (n) & 1))
/* macro per prenotare e rilasciare un servizio */
#define Book(v, n)		v = v | (1 << (n))
#define Cancel(v, n)	v = v & ~(1 << (n))


/* numero di processi attivi per le tipologie
   di servizio officina e carro attrezzi */
#ifdef MULTI
#define NPROC 2
#else
#define NPROC 1
#endif


/* canale carta di credito */
chan creditcard_ch = [0] of {bit};

/* canali officine */
chan garage_chs [NPROC] = [0] of {bit, byte};

/* canali carro attrezzi */
chan towtruck_chs [NPROC] = [0] of {bit, byte};

/* canale noleggio auto */
chan rentalcar_ch = [0] of {bit, byte};


/* variabili globali accedute localmente all'interno dell'init:
   indicano il pid dei servizi */
local byte g_pid1 = 0;
local byte tt_pid1 = 0;
local byte rc_pid = 0;

/* se MULTI è definito considero anche il secondo servizio */
#ifdef MULTI
local byte g_pid2 = 0;
local byte tt_pid2 = 0;
#endif


/* variabili che indicano se un ces ha prenotato un servizio;
   per officine e carro attrezzi utilizziamo una variabile di
   tipo byte e il test è effettuato con la macro sopra definita
   NOTA: la scelta di avere una variabile di tipo byte limita
   		 il numero di servizi di una tipologia al più 8 */
byte garage_booked = 0;

byte towtruck_booked = 0;

bool rentalcar_booked = false;


/* car emergency system */
proctype ces()
{
		/* ha un abbonamento? */
		bool subscribing;
		bool result;
		/* pid dei servizi prenotati:
		   se pid == 0 allora il servizio non è prenotato
		   altrimenti il pid è usato come ricevuta di prenotazione */
		byte pid_garage = 0, pid_towtruck = 0, pid_rentalcar = 0;
		/* indice del canale dei servizi prenotati (per servizi con più istanze) */
		byte idg = 0, idtt = 0;

		/* scelta non-deterministica se è abbonato o meno */
		if
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
				garage_chs[idg] ! REQUEST, 0;
				garage_chs[idg] ? result, pid_garage;
				if
				/* officina prenotata */
				:: result -> goto reqTT
				/* officina occupata, la rilascio e continuo ad iterare */
				:: !result -> Cancel(garage_booked, idg)
				fi
			/* altrimenti continuo ad iterare */
			:: else -> skip
			fi
		}
		/* se viene raggiunto questo punto allora tutte le prenotazioni sono fallite */
		goto fail;
		
		/* tentativo di prenotazione del carro attrezzi */
reqTT:	for(idtt in towtruck_chs) {
			if
			/* se il idt-esimo carro attrezzi non è prenotata da un altro ces
			   ottengo il canala di comunicazione in mutua esclusione */
			:: atomic { notBooked(towtruck_booked, idtt) ->
				Book(towtruck_booked, idtt) };
				towtruck_chs[idtt] ! REQUEST, 0;
				towtruck_chs[idtt] ? result, pid_towtruck;
				if
				/* carro attrezzi prenotato */
				:: result -> goto reqRC
				/* carro attrezzi occupato, continuo ad iterare */
				:: !result -> Cancel(towtruck_booked, idtt)
				fi
			/* altrimenti continuo ad iterare */
			:: else -> skip
			fi
		}
		/* se viene raggiunto questo punto allora tutte le prenotazioni sono fallite */
		goto fail;

		/* tentativo di prenotazione del noleggio auto */
reqRC:	if
		:: atomic { !rentalcar_booked ->
			rentalcar_booked = true };
			rentalcar_ch ! REQUEST, 0;
			rentalcar_ch ? result, pid_rentalcar;
			if
			:: result -> skip
			:: !result -> rentalcar_booked = false
			fi
			/* sia in caso di fallimento della prenotazione, sia in caso di successo
		   	   procedo con la riparazione
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
			garage_chs[idg] ! RELEASE, pid_garage;
			garage_chs[idg] ? AVAILABLE, pid_garage;
			Cancel(garage_booked, idg);
			if
			:: pid_towtruck != 0 ->
				towtruck_chs[idtt] ! RELEASE, pid_towtruck;
				towtruck_chs[idtt] ? AVAILABLE, pid_towtruck;
				Cancel(towtruck_booked, idtt)
			:: else -> skip
			fi;
			if
			:: pid_rentalcar != 0 ->
				rentalcar_ch ! RELEASE, pid_rentalcar;
				rentalcar_ch ? AVAILABLE, pid_rentalcar;
				rentalcar_booked = false
			:: else -> skip
			fi;
		:: else -> skip
		fi;
endCES:	skip
}


/* servizio carta di credito
   sempre disponibile e che ha sempre successo */
proctype creditcard(chan ch)
{
endCC:	atomic { ch ? REQUEST;
		/* le richieste hanno sempre successo */
		ch ! AVAILABLE };
		goto endCC
}


/* generico servizio
   sceglie nondeterministicamente se è disponibile od occupato */
proctype service(chan ch)
{
		/* indica se il servizio è disponibile o meno */
		bool state;
		
		/* scelta non-deterministica dello stato */
		if
		:: state = false
		:: state = true
		fi;
		
endS:	ch ? REQUEST, _;
		if
		/* se è disponibile allora viene prenotato */
		:: state ->
			ch ! AVAILABLE, _pid;
			/* il messaggio di release deve avere il pid del servizio:
			   ovvero il ticket di prenotazione */
bookS:		ch ? RELEASE, eval(_pid);
			/* annullo il ticket di prenotazione, inviando 0 */
			ch ! AVAILABLE, 0
		/* altrimenti è occupato */
		:: !state -> ch ! BUSY, 0
		fi;
		goto endS
}


/* inizializzazione */
init {
	atomic {
		run ces();
		run creditcard(creditcard_ch);
		g_pid1 = run service(garage_chs[0]);
		tt_pid1 = run service(towtruck_chs[0]);
/* se MULTI è definito considero anche il secondo servizio */
#ifdef MULTI
		g_pid2 = run service(garage_chs[1]);
		tt_pid2 = run service(towtruck_chs[1]);
#endif
		rc_pid = run service(rentalcar_ch)
	}
}


/* proprietà LTL */
ltl prop_a { !ces_req W (ces_sub || ces_auth) }

/* se MULTI vale 1 (true) allora considero anche il secondo servizio */
#ifdef MULTI
ltl prop_b0 { ((g1_state || g2_state) && (tt1_state || tt2_state)) -> <>ces_succ }
ltl prop_b { <>((g1_state || g2_state) && (tt1_state || tt2_state)) -> <>ces_succ }
/* Existence, after Q */
ltl prop_b1 { []!((g1_state || g2_state) && (tt1_state || tt2_state))
			  || 
			   <>((g1_state || g2_state) && (tt1_state || tt2_state) && <>ces_succ) }
ltl prop_c { []!(ces_end && (g1_book || g2_book || tt1_book || tt2_book || rc_book)) }

/* altrimenti considero solo il primo */
#else
ltl prop_b0 { (g1_state && tt1_state) -> <>ces_succ }
ltl prop_b { <>(g1_state && tt1_state) -> <>ces_succ }
/* Existence, after Q */
ltl prop_b1 { []!(g1_state && tt1_state) || <>((g1_state && tt1_state) && <>ces_succ) }
ltl prop_c { []!(ces_end && (g1_book || tt1_book || rc_book)) }
#endif
