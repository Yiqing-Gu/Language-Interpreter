

head(cons(zero, nil), zero)?
tail(cons(zero, nil), nil)?
head(cons(succ(zero), nil), succ(zero))?
tail(cons(succ(zero), nil), nil)?
head(cons(succ(zero), cons(zero, nil)), succ(zero))?
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil))?

head([0], zero)?
tail([0], [])?
head([1], succ(zero))?
tail([1], nil)?
head([1,0], succ(zero))?
tail([1,0], [0])?


head([0], zero).
tail([0], []).
head([1], succ(zero)).
tail([1], nil).
head([1,0], succ(zero)).
tail([1,0], [0]).

head(cons(zero, nil), zero)?
tail(cons(zero, nil), nil)?
head(cons(succ(zero), nil), succ(zero))?
tail(cons(succ(zero), nil), nil)?
head(cons(succ(zero), cons(zero, nil)), succ(zero))?
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil))?

head([0], zero)?
tail([0], [])?
head([1], succ(zero))?
tail([1], nil)?
head([1,0], succ(zero))?
tail([1,0], [0])?

