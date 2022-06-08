unify(X, X).

or(X, Y) :- X.
or(X, Y) :- Y.

and(X, Y) :- X, Y.

all([]).
all([X|Xs]) :- and(X, all(Xs)).

any([]) :- unify(a, b).
any([X|Xs]) :- or(X, any(Xs)).

elem(X, Xs) :- all([unify(Xs, [XX|XsX]), any([unify(X, XX), elem(X, XsX)])]).

elemall(Xs, Ys) :- any([unify(Xs, []), all([unify(Xs, [X|XsX]), elem(X, Ys), elemall(XsX, Ys)])]).

same(Xs, Ys) :- all([elemall(Xs, Ys), elemall(Ys, Xs)]).

length(Xs, N) :- 
  any([all([unify(Xs, []), unify(N, zero)]), all([unify(Xs, [X|XsX]), length(XsX, NX), unify(N, succ(NX))])]).

prefix(Xs, Ys) :-
  any([unify(Xs, []), all([unify(Ys, [Y|YsX]), prefix(XsX, YsX), unify(Xs, [Y|XsX])])]).

suffix(Xs, Ys) :-
  any([all([unify(Ys, [Y|YsX]), suffix(Xs, YsX)]), unify(Xs, Ys)]).

append(Xs, Ys, Zs) :- 
  any([all([unify(Xs, []), unify(Ys, Zs)]), all([unify(Xs, [X|XsX]), unify(Zs, [X|ZsX]), append(XsX, Ys, ZsX)])]).

reverse(Xs, Ys) :- rev(Xs, [], Ys).

rev(Xs, Acc, Ys) :- 
  any([all([unify(Xs, []), unify(Acc, Ys)]), all([unify(Xs, [X|XsX]), rev(XsX, [X|Acc], Ys)])]).

palindrome(Xs) :- 
  any([unify(Xs, []), unify(Xs, [X]), all([append([X|XsX], [X], Xs), palindrome(XsX)])]).
