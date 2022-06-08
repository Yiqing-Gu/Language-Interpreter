% a small arithmetic grammar

% variables, only 3 pre-defined ones allowed...
lang(v("x")).
lang(v("y")).
lang(v("z")).

% numbers
lang(n(zero)).
lang(n(succ(X))) :- lang(n(X)).

lang(X)?

% just addition/subtraction operators
op("+").
op("-").

% expressions
lang(e(X, O, Y)) :- lang(X), op(O), lang(Y).

lang(e(v("x"), O, e(n(succ(zero)), Oo, v(Y))))?
