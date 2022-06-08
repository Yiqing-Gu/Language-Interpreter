% assumes lib/list.l

length([],X)?
length([],succ(X))?
length([1,2,3],X)?
length([1,2],succ(X))?
length([1,2,4,5,6],X)?
