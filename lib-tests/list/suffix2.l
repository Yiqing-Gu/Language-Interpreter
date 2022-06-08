% assumes lib/list.l

suffix(X, [a,b,c])?
suffix([b | Y], [a,b,c])?
suffix([X | [b,c]], [a,b,c])?
