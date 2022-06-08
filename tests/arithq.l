unify(X, X).


or(X, Y) :- X.
or(X, Y) :- Y.


and(X, Y) :- X, Y.


all([]).
all([X|Xs]) :- and(X, all(Xs)).


any([]) :- unify(a, b).
any([X|Xs]) :- or(X, any(Xs)).

pNat(X) :- any([unify(X, zero), all([unify(X, succ(XX)), pNat(XX)])]).

addn(0, Y, Y).
addn(succ(X), Y, succ(Z)) :-  addn(X, Y, Z).

multn(X, Y, Z) :-
  any([all([unify(X, zero), unify(Z, zero)]), all([unify(X, succ(XX)), addn(Y, ZX, Z), multn(XX, Y, ZX)])]).

sub(X, Y, Z) :- 
  any([all([unify(X, zero), unify(Z, neg(Y))]), all([unify(Y, zero), unify(X, succ(SomeThing)), unify(pos(X), Z)]), all([unify(X, succ(XX)), unify(Y, succ(YX)), sub(XX, YX, Z)])]).

eqi(int(A, B), int(C, D)) :-
    all([sub(A, B, E), sub(C, D, E)]).

add(X, Y, Z) :-
    any([ all([unify(X, pos(XX)), unify(Y, pos(YX)), addn(XX, YX, ZX), unify(Z, pos(ZX))])
        , all([unify(X, pos(XX)), unify(Y, neg(YX)), sub(XX, YX, Z)])
        , all([unify(X, neg(XX)), unify(Y, pos(YX)), sub(YX, XX, Z)])
        , all([unify(X, neg(XX)), unify(Y, neg(YX)), addn(XX, YX, ZX), unify(Z, neg(ZX))])]).
mult(X, Y, Z) :-
    any([ all([unify(X, pos(XX)), unify(Y, pos(YX)), multn(XX, YX, ZX), unify(Z, pos(ZX))])
        , all([unify(X, pos(XX)), unify(Y, neg(YX)), multn(XX, YX, ZX), unify(Z, neg(ZX))])
        , all([unify(X, neg(XX)), unify(Y, pos(YX)), multn(XX, YX, ZX), unify(Z, neg(ZX))])
        , all([unify(X, neg(XX)), unify(Y, neg(YX)), multn(XX, YX, ZX), unify(Z, pos(ZX))])]).

toInts(X, Y) :-
    any([ all([unify(X, pos(XX)), addn(XX, Dx, XY), unify(Y, int(XY, Dx))])
        , all([unify(X, neg(XX)), addn(XX, Dx, XY), unify(Y, int(Dx, XY))])]).

addi(int(A, B), int(C, D), int(E, F)) :-
  addn(A, C, AC),
  addn(AC, F, ACF),
  addn(B, D, BD),
  addn(BD, E, ACF).
addi(int(A, B), int(C, D), int(succ(E), succ(F))) :-
  addi(int(A, B), int(C, D), int(E, F)).  

    
% all([sub(IX, IY, X), sub(JX, JY, Y), add(X, Y, Z), toInts(Z, K)]).

multi(int(IX, IY), int(JX, JY), K) :-
  all([sub(IX, IY, X), sub(JX, JY, Y), mult(X, Y, Z), toInts(Z, K)]).

inverse(int(IX, IY), int(JX, JY)) :- all([addi(int(IX, IY), int(zero, zero), int(JY, JX))]).