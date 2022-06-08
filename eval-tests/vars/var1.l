p(X)?

p("a").p("B").
p("a").

p(X)?

p(zero)?
p(zero).
p(zero)?
p(X)?

p(one,two,three)?
p(zero), p(one,two,three)?
p(X,Y,Z)?
p(zero), p(one,two,X)?
p(one,two,three).
p(one,two,three)?
p(zero), p(one,two,three)?
p(X,Y,Z)?
p(zero), p(one,two,X)?

q(one,two,three)?
q(zero), q(one,two,three)?
q(one,two,three).
q(one,two,three)?
q(zero), q(one,two,three)?
q(zero), q(one,X,three)?


length(nil, zero)?
isalist(nil)?
length(X,Y)?
isalist(X)?

length(nil, zero).
isalist(nil).

length(nil, zero)?
isalist(nil)?
length(X,Y)?
isalist(X)?
