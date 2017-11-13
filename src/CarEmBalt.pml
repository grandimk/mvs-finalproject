/* tipo di richiesta */
#define REQUEST 0
#define RELEASE 1

#define BUSY 0
#define AVAILABLE 1


/* definizioni per formule LTL */
#define ces1_start 	(ces[ces_pid1]@start)
#define ces2_start 	(ces[ces_pid2]@start)

#define max_one_g1 (!(ces[ces_pid1]:pid_garage == g_pid1 && ces[ces_pid2]:pid_garage == g_pid1))
#define max_one_g2 (!(ces[ces_pid1]:pid_garage == g_pid2 && ces[ces_pid2]:pid_garage == g_pid2))
#define max_one_tt (!(ces[ces_pid1]:pid_towtruck == tt_pid && ces[ces_pid2]:pid_towtruck == tt_pid))
#define max_one_rc (!(ces[ces_pid1]:pid_rentalcar == rc_pid && ces[ces_pid2]:pid_rentalcar == rc_pid))

#define ces1_damage (ces[ces_pid1]@damage)
#define ces2_damage (ces[ces_pid2]@damage)

#define ces1_no_book_g	(ces[ces_pid1]:pid_garage == 0)
#define ces2_no_book_g	(ces[ces_pid2]:pid_garage == 0)


/* numero di garage */
#define NGARAGE 2


/* canale carta di credito */
chan creditcard_ch = [0] of {bit};

/* canali officine */
chan garage_chs [NGARAGE] = [0] of {bit, byte, byte};

/* canale carro attrezzi */
chan towtruck_ch = [0] of {bit, byte, byte};

/* canale noleggio auto */
chan rentalcar_ch = [0] of {bit, byte, byte};


/* variabili globali accedute localmente all'interno dell'init
   indicano il pid dei servizi */
local byte ces_pid1 = 0;
local byte ces_pid2 = 0;
local byte g_pid1 = 0;
local byte g_pid2 = 0;
local byte tt_pid = 0;
local byte rc_pid = 0;


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
		byte idg = 0;

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
			garage_chs[idg] ! REQUEST, 0, _pid;
			garage_chs[idg] ? result, pid_garage, eval(_pid);
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
reqTT:	towtruck_ch ! REQUEST, 0, _pid;
		towtruck_ch ? result, pid_towtruck, eval(_pid);
		if
		/* carro attrezzi prenotato */
		:: result -> skip
		/* carro attrezzi occupato, prenotazione fallita */
		:: !result -> goto fail
		fi;

		/* tentativo di prenotazione del noleggio auto */
reqRC:	rentalcar_ch ! REQUEST, 0, _pid;
		rentalcar_ch ? result, pid_rentalcar, eval(_pid);
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
			garage_chs[idg] ! RELEASE, pid_garage, _pid;
			garage_chs[idg] ? AVAILABLE, pid_garage, eval(_pid);
			if
			:: pid_towtruck != 0 ->
				towtruck_ch ! RELEASE, pid_towtruck, _pid;
				towtruck_ch ? AVAILABLE, pid_towtruck, eval(_pid)
			:: else -> skip
			fi;
			if
			:: pid_rentalcar != 0 ->
				rentalcar_ch ! RELEASE, pid_rentalcar, _pid;
				rentalcar_ch ? AVAILABLE, pid_rentalcar, eval(_pid)
			:: else -> skip
			fi
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


/* generico servizio inizialmente disponibile */
proctype service(chan ch)
{		
		/* indicano il pid del ces che fa la richiesta */
		byte who, bwho;

waitS:	atomic { ch ? REQUEST, _, who;
		ch ! AVAILABLE, _pid, who };

bookS:	do
		/* il messaggio di release deve avere il pid del servizio ed il pid del ces */
		:: atomic { ch ? RELEASE, eval(_pid), eval(who) ->
			ch ! AVAILABLE, 0, who };
			goto waitS
		:: atomic { ch ? REQUEST, _, bwho ->
			ch ! BUSY, 0, bwho }
		od
}


/* servizio noleggio auto
   sceglie nondeterministicamente se è disponibile od occupato */
proctype rentalcar(chan ch)
{
		/* indica se il servizio è disponibile o meno */
		bool state;
		/* indicano il pid del ces che fa la richiesta */
		byte who, bwho;
		
		/* scelta nonderminisica dello stato */
		if
		:: state = false
		:: state = true
		fi;
		
waitRC:	if
		/* se è disponibile allora viene prenotato */
		:: state -> 
			atomic { ch ? REQUEST, _, who;
			ch ! AVAILABLE, _pid, who }
			/* esce dall'if e procede all'etichetta bookRC */
		/* altrimenti è occupato */
		:: !state ->
busyRC:		atomic { ch ? REQUEST, _, who;
			ch ! BUSY, 0, who };
			/* salto ed aspetto la prossima richiesta di servizio  */
			goto busyRC
		fi;

bookRC:	do
		/* il messaggio di release deve avere il pid del servizio ed il pid del ces */
		:: atomic { ch ? RELEASE, eval(_pid), eval(who) ->
			ch ! AVAILABLE, 0, who } ;
			goto waitRC
		:: atomic { ch ? REQUEST, _, bwho ->
			ch ! BUSY, 0, bwho}
		od
}


/* inizializzazione */
init {
	atomic {
		ces_pid1 = run ces();
		ces_pid2 = run ces();
		run creditcard(creditcard_ch);
		g_pid1 = run service(garage_chs[0]);
		g_pid2 = run service(garage_chs[1]);
		tt_pid = run service(towtruck_ch);
		rc_pid = run rentalcar(rentalcar_ch)
	}
}


/* proprietà LTL */
ltl prop_d0 { [](max_one_g1 && max_one_g2 && max_one_tt && max_one_rc) }
/* Absence, after Q */
ltl prop_d { []((ces1_start && ces2_start) -> [](max_one_g1 && max_one_g2 && max_one_tt && max_one_rc)) }
ltl prop_e { []<>ces1_damage && []<>ces2_damage }
ltl prop_g { !<>[]np_ }

/* assumendo weak fainessa a livello di processi la proprietà è verificata */
ltl non_book { !((<>[]ces1_no_book_g) || (<>[]ces2_no_book_g)) }
/* quindi, se entrambi i processi si muovono, riescono sempre a prenotare un'officina */
