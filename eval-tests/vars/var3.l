ntos(X,Y)?

ntos(zero, "zero").
ntos(zero, "nada").
ntos(succ(zero), "one").
ntos(1, "uno").
ntos(succ(succ(zero)), "two").
ntos(3, "three").
ntos(succ(succ(succ(succ(zero)))), "four").
ntos(5, "five").
ntos(succ(5), "six").

ntos(N,S)?
ntos(0,S)?
ntos(N,"uno")?

