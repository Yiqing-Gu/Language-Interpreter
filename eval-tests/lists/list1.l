

head(cons(zero, nil), zero)?
head(cons(zero, nil), succ(zero))?
tail(cons(zero, nil), nil)?
tail(cons(zero, nil), cons(zero, nil))?
head(cons(succ(zero), nil), succ(zero))?
head(cons(succ(zero), nil), zero)?
tail(cons(succ(zero), nil), nil)?
tail(cons(succ(zero), nil), cons(zero, nil))?
head(cons(succ(zero), cons(zero, nil)), succ(zero))?
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil))?
head(cons(zero, cons(succ(zero), cons(zero, nil))), zero)?

head([0], zero)?
head([0], 1)?
tail([0], [])?
tail([0], [0])?
head([1], succ(zero))?
head([1], 0)?
tail([1], nil)?
tail([1], [0])?
head([1,0], succ(zero))?
tail([1,0], [0])?
head([0,1,0], 0)?

head([0], zero).
tail([0], []).
head([1], succ(zero)).
tail([1], nil).
head([1,0], succ(zero)).
tail([1,0], [0]).

head(cons(zero, nil), zero)?
head(cons(zero, nil), succ(zero))?
tail(cons(zero, nil), nil)?
tail(cons(zero, nil), cons(zero, nil))?
head(cons(succ(zero), nil), succ(zero))?
head(cons(succ(zero), nil), zero)?
tail(cons(succ(zero), nil), nil)?
tail(cons(succ(zero), nil), cons(zero, nil))?
head(cons(succ(zero), cons(zero, nil)), succ(zero))?
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil))?
head(cons(zero, cons(succ(zero), cons(zero, nil))), zero)?

head([0], zero)?
head([0], 1)?
tail([0], [])?
tail([0], [0])?
head([1], succ(zero))?
head([1], 0)?
tail([1], nil)?
tail([1], [0])?
head([1,0], succ(zero))?
tail([1,0], [0])?
head([0,1,0], 0)?
