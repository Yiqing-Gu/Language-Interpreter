% assumes lib/arith.l

underfour(0).
underfour(1).
underfour(2).
underfour(3).

underfour(X),underfour(Y),addi(int(4,3), int(3,1), int(X,Y))?
underfour(X),addi(int(4,3), int(2,1), int(succ(succ(X)),X))?
