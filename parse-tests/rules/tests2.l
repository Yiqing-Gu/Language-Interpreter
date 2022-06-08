% Let's set up a family tree

parent(lee, virginia).
parent(lee, bob).
parent(lee, suzy).
parent(virginia, garrett).
parent(bob, robby).
parent(suzy, chris).
parent(suzy, jamie).

% Some questions about the family tree, variables edition

parent(lee, X)?
        % Yes:
        % X = virginia;
        % X = bob;
        % X = suzy.
parent(X, virginia)?
        % Yes:
        % X = lee.
parent(robby, X)?
        % No.
parent(X, robby)?
        % Yes:
        % X = bob.

% Some natural number questions.

generations(lee, virginia, 1).
generations(lee, garrett, 2).
generations(lee, robby, 2).
generations(suzy, jamie, 1).

generations(lee, virginia, X)?
        % Yes:
        % X = 1.
generations(lee, X, 1)?
        % Yes:
        % X = virginia.
generations(lee, X, 2)?
        % Yes:
        % X = garrett;
        % X = robby.
generations(X, jamie, 1)?
        % Yes:
        % X = suzy.
generations(X, jamie, 2)?
        % No.

% Some questions about lists.

children(lee, [virginia, bob, suzy]).
children(suzy, [chris, jamie]).

children(lee, X)?
        % Yes:
        % X = cons(virginia, cons(bob, cons(suzy, nil))).
children(lee, [virginia | X])?
        % Yes:
        % X = cons(bob, cons(suzy, nil)).
children(suzy, [X, Y])?
        % Yes:
        % Y = jamie,
        % X = chris.
