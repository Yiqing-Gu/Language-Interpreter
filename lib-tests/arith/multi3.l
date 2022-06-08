% assumes lib/arith.l

underfour(0).
underfour(1).
underfour(2).
underfour(3).

underfour(X),underfour(Y),multi(int(3,0), int(0,1), int(X,Y))?
underfour(X),underfour(Y),multi(int(0,4), int(2,4), int(X,Y))?
underfour(X),underfour(Y),multi(int(0,2), int(2,3), int(X,Y))?
