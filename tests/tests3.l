% Let's set up a family tree

parent(lee, virginia).
parent(lee, bob).
parent(lee, suzy).
parent(virginia, garrett).
parent(bob, robby).
parent(suzy, chris).
parent(suzy, jamie).

% Let's introduce some derived ideas.

grandparent(X,Z) :- parent(X,Y), parent(Y,Z).

grandparent(lee, garrett)?
        % Yes.
grandparent(virginia, garrett)?
        % No.
grandparent(lee, X)?
        % Yes:
        % X = garrett;
        % X = robby;
        % X = chris;
        % X = jamie.
grandparent(X, garrett)?
        % Yes:
        % X = lee.
grandparent(suzy, X)?
        % No.

% Let's introduce another derived idea

sibling(Y, Z) :- parent(X, Y), parent(X, Z).

sibling(garrett, X)?
        % Yes:
        % X = garrett.
sibling(virginia, bob)?
        % Yes.
sibling(virginia, suzy)?
        % Yes.
sibling(garrett, jamie)?
        % No.
sibling(jamie, X)?
        % Yes:
        % X = chris;
        % X = jamie.
sibling(virginia, X)?
        % Yes:
        % X = virginia;
        % X = bob;
        % X = suzy.

% Note those last two sets of answers: we don't have a good way in
% Logic to rule *out* cases, only to rule *in* cases.. so the sibling
% relationship ends up being reflexive.
