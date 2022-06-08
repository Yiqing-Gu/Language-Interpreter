% assumes lib/list.l

reverse([],[])?
reverse([1],[])?
reverse([1],[1])?
reverse([1,2],[1,2])?
reverse([1,2],[2,1])?
reverse([1,2,1],[1,2])?
reverse([1,2,1],[1,2,1])?
