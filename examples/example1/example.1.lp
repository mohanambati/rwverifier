number(1..n).

1 { q(R, C, V) : number(V) } 1 :- number(R), number(C).
%filter latin square.
:- q(R,C1,V1), q(R,C2,V2), C1 != C2, V1 == V2.
:- q(R1,C,V1), q(R2,C,V2), R1 != R2, V1 == V2.

% filter normalized latin square.
:- not q(1, C, C), number(C).
:- not q(R, 1, R), number(R).

