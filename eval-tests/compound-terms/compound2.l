
head(cons(zero, nil), zero)?
tail(cons(zero, nil), nil)?
head(cons(succ(zero), nil), succ(zero))?
tail(cons(succ(zero), nil), nil)?
head(cons(succ(zero), cons(zero, nil)), succ(zero))?
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil))?


head(cons(zero, nil), zero).
tail(cons(zero, nil), nil).
head(cons(succ(zero), nil), succ(zero)).
tail(cons(succ(zero), nil), nil).
head(cons(succ(zero), cons(zero, nil)), succ(zero)).
tail(cons(succ(zero), cons(zero, nil)), cons(zero, nil)).

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
