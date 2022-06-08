p(X)?

p(c) :- p(a).
p(c) :- p(b).
p(e) :- p(c), p(d).
p(f) :- p(e), p(a).

p(X)?

p(b).

p(X)?

p(d).

p(X)?

p(a).

p(X)?
