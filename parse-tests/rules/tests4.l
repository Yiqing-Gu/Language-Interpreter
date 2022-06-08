% Let's set up a family tree.  Different AND exciting!

parent(lee, virginia).
parent(lee, bob).
parent(lee, suzy).
parent(virginia, garrett).
parent(bob, robby).
parent(suzy, chris).
parent(suzy, jamie).

% Let's introduce some MORE derived ideas

ancestor(X, Y) :- parent(X, Y).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).

ancestor(lee, virginia)?
ancestor(lee, garrett)?
ancestor(suzy, garrett)?
ancestor(lee, X)?
ancestor(suzy, X)?

% How about the generations thing?

generations(X, Y, 1) :- parent(X, Y).
generations(X, Z, succ(N)) :- parent(X, Y), generations(Y, Z, N).

generations(lee, virginia, X)?
generations(lee, garrett, X)?
generations(suzy, garrett, X)?
generations(lee, X, 2)?
generations(suzy, X, 1)?
