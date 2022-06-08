reverse([],[])?
reverse([],[1])?
reverse([5,6],[6,5])?
reverse([5,6],[5,6])?

reverse([2,9], [9,2])?
reverse([9,9], [9,2])?

log(0,"debug 1"). log(0, X)?

append([9,9], [1], [9,2,1])?
append(Zs, [1], [9,2,1]), reverse([9,9], Zs)?

reverse([1,2,9], [9,2,1])?
reverse([1,9,9], [9,2,1])?

log(1,"debug 2"). log(1, X)?
append(Zs, [1], [3,2,1]), reverse([3,3], Zs)?


reverse([1,1,2,9], [9,2,1,1])?
reverse([1,1,9,9], [9,2,1,1])?


reverse([3,5,8,1,1,2,9], [9,2,1,1,8,5,3])?
reverse([3,5,8,1,1,9,9], [9,2,1,1,8,5,3])?
