addn(X, 0, X).
addn(0, Y, Y).
addn(succ(X), succ(Y), succ(succ(Z))) :-  addn(X, Y, Z).

multn(0, X, 0).
multn(succ(X), Y, Z) :- multn(X, Y, T), addn(T, Y, Z).

eqi(int(A, B), int(C, D)) :- addn(A, D, AD), addn(B, C, AD).

addi(int(A, B), int(C, D), int(E, F)) :-
  addn(A, C, AC),
  addn(AC, F, ACF),
  addn(B, D, BD),
  addn(BD, E, ACF).

    
% all([sub(IX, IY, X), sub(JX, JY, Y), add(X, Y, Z), toInts(Z, K)]).

multi(int(A, B), int(C, D), int(E, F)) :-
  multn(A, C, AC),
  multn(B, D, BD),
  multn(A, D, AD),
  multn(B, C, BC),
  addn(AC, BD, EE),
  addn(AD, BC, FF), eqi(int(EE, FF), int(E, F)).


inverse(int(A, B), int(C, D)) :- eqi(int(A, B), int(D, C)). 