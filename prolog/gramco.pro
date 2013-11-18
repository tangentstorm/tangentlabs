% gramco : grammar combinators (prolog implementation)
%
% note: some of these are redundant in prolog, but
% i will include all of them for easy comparison to
% the other implementations.

% -- simple matchers -------------------------------------------
% any/1 : treat string as a set and match any character.
any("") --> error.
any(Str) --> [Ch], { member(Ch, Str) } .

% lit/1 : match a string literal.
% In prolog, just use plain strings.
lit(Str) --> Str.


% -- grammar combinators ---------------------------------------
% alt/1 : match any alternative from the list.
% In prolog: use the ; operator directly.
alt([G|Gs]) --> G ; alt(Gs).

% seq/1 : match a sequence.
% In prolog: use the , operator.
seq([P|Ps]) --> P , seq(Ps).


% rep/1 : match n repetitions of a sequence.
rep(P) --> P, ([] ; P).
rep([P|Ps]) --> rep(seq([P|Ps])).

% die/0 : abort the matching process
die --> { fail }.

% die/0 : abort the matching process, showing a message first.
die(Msg) --> { writef(Msg), fail }.


digit  --> any("0123456789").
hexit --> (digit ; any("abcdefABCDEF")). % TODO: case insensitive.

int --> rep(digit) ; ("$", rep(hexit)).

binop -->
    ( any("+-*/")  
    ; ( [Op], die({append(["bad op:"],Op)} )) 
    ).
binex --> num, ([] ; (factor, binop)).


expect(rule, string).
test :-
    phrase(int, "0"),
    phrase(int, "$0"),
    phrase(int, "$F"),
    phrase(int, "$FF"),
    phrase(int, "123").

