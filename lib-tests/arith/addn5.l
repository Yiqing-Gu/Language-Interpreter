% assumes lib/arith.l

addn(zero,Y,zero)?
addn(X,zero,zero)?
addn(succ(zero),Y,zero)?
addn(X,succ(zero),zero)?
addn(4,Y,0)?
addn(X,3,0)?
