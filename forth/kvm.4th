\ mini-kvm for yourforth
: putc ( n-  ) EMIT ;
: puts ( n-  ) TYPE ; 
: putn ( n-  ) <% %S %> puts ;
: esc  (  -  ) 27 putc ;
: cr   ( -   ) 10 putc ;
: fg   ( n-  ) esc "[38;5;" puts putn &m putc ;
: bg   ( n-  ) esc "[48;5;" puts putn &m putc ;
: clear esc "[H" puts esc "[J" puts ;

HEX \ helpers for the 16 ansi colors
: |k 0 fg ;  : |K 8 fg ; : |!k 0 bg ;  : |!K 8 bg ;
: |r 1 fg ;  : |R 9 fg ; : |!r 1 bg ;  : |!R 9 bg ;
: |g 2 fg ;  : |G A fg ; : |!g 2 bg ;  : |!G A bg ;
: |y 3 fg ;  : |Y B fg ; : |!y 3 bg ;  : |!Y B bg ;
: |b 4 fg ;  : |B C fg ; : |!b 4 bg ;  : |!B C bg ;
: |m 5 fg ;  : |M D fg ; : |!m 5 bg ;  : |!M D bg ;
: |c 6 fg ;  : |C E fg ; : |!c 6 bg ;  : |!C E bg ;
: |w 7 fg ;  : |W F fg ; : |!w 7 bg ;  : |!W F bg ;
DECIMAL

|r "hello world!" |w puts cr

: wdeas 0 CONTEXT @ BEGIN >LFA @ DUP DUP 0= UNTIL 2DROP ;
: id. DUP >FFA @ 0=
   IF |w ELSE |B THEN
   >NFA @ $@ TYPE SPACE SPACE ;
: words wdeas BEGIN id. DUP 0= UNTIL DROP CR ;
