% Make assertions about lambda calculus

env([assigned(X,V) | Rest], X, V).
env([First | Rest], X, V) :- env(Rest, X, V).

eval(H, const(I), int(I)).
eval(H, lam(X, Body), clos(H,X,Body)).
eval(H, var(X), V) :- env(H, X, E), eval(H, E, V).
eval(H, app(F,A), V) :- eval(H, F, clos(Hh, X, Body)), eval([assigned(X, A) | Hh], Body, V).

% Make assertions about lambda terms and their evaluation

eval([], const(1), int(1))?
eval([assigned("x", const(1)), assigned("y", const(2))], var("x"), int(1))?
eval([assigned("x", const(1)), assigned("y", const(2))], var("y"), int(2))?
eval([assigned("x", const(X)), assigned("y", const(2))], var("x"), int(14))?
eval([assigned("x", const(1)), assigned("y", const(2))], var("y"), V)?

eval([], app(lam("x", var("x")), const(1)), int(1))?
eval([], app(lam("x", var("x")), const(1)), int(2))?
eval([], app(lam("x", var("x")), const(1)), V)?

eval([], app(app(lam("x", lam("y", var("x"))), const(1)), const(2)), int(1))?
eval([], app(app(lam("x", lam("y", var("y"))), const(1)), const(2)), int(2))?
eval([], app(app(lam("x", lam("y", var("x"))), const(1)), const(2)), V)?
eval([], app(app(lam("x", lam("y", var("y"))), const(1)), const(2)), V)?

eval([], app(app(lam("f", lam("x", app(var("f"), var("x")))), lam("z", var("z"))), const(1)), V)?
