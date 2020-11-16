------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
(*
--algorithm Euclid
  variables u = 24; v \in 1..N, init = <<u,v>>;
begin
  print <<u, v>>;
  while u # 0 do
    if u < v then u := v || v := u; end if
  end while;
  print <<init, "have GCD", v>>;
end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4d677ff4cf42783afe1cf889d5f2dfc4
VARIABLES u, v, init, pc

vars == << u, v, init, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ init = <<u,v>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(<<u, v>>)
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << u, v, init >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF u # 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<init, "have GCD", v>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ init' = init

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8d0865cba8f7e6f0ca2e09ccbc5c60d3

=============================================================================
\* Modification History
\* Last modified Wed Jul 15 16:15:27 EDT 2020 by tange
\* Created Wed Jul 15 16:07:21 EDT 2020 by tange
