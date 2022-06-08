edge(a,b).
edge(a,c).
edge(b,d).
edge(c,d).
edge(c,e).
edge(d,e).

edge(a,c)?
edge(b,e)?
edge(a, X)?
edge(X, e)?
edge(a,X),edge(X,e)?
edge(e, X)?

path(X, Y) :- edge(X, Y).
path(X, Y) :- edge(X, Z), path(Z, Y).

path(a, e)?
path(a, X)?
path(X, Y)?
