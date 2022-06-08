% assumes lib/list.l

reverse([],X)?
reverse([a],[X])?
reverse([a,b],[b,X])?
reverse([a,b,a],[a,b,X])?
