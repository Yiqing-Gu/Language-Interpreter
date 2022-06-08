elem(X, [X|Xs]).
elem(X, [Y|Xs]) :- elem(X, Xs).

elemall([], Ys).
elemall([X|XS], Ys) :- elem(X, Ys), elemall(XS, Ys).

same(Xs, Ys) :- elemall(Xs, Ys), elemall(Ys, Xs).

length([], 0).
length([X|XS], succ(L)) :- length(XS, L). 

prefix([], Ys).
prefix([X|Xs], [X|Ys]) :- prefix(Xs, Ys).

suffix(Xs, [Y|Ys]) :- suffix(Xs, Ys).
suffix(Xs, Xs).

append([], Ys, Ys).
append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

reverse([], []).
reverse([X|Xs], Ys) :- reverse(Xs, Zs), append(Zs, [X], Ys).

rev([], Acc, Acc).
rev([X|XS], ACC, R) :- rev(XS, [X|ACC], R).

unify(X, X).

palindrome(X) :- unify(X, []).
palindrome([X]).
palindrome(Xs) :- append([X|Ys], [X], Xs), palindrome(Ys).