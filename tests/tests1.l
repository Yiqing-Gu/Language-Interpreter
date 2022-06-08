% Let's set up a family tree

parent(lee, virginia).
parent(lee, bob).
parent(lee, suzy).
parent(virginia, garrett).
parent(bob, robby).
parent(suzy, chris).
parent(suzy, jamie).

% Some questions about said family tree

parent(lee, bob)?                         % Yes
parent(suzy, chris)?                      % Yes
parent(suzy, bob)?                        % No
parent(bob, garrett)?                     % No
parent(lee, jamie)?                       % No

% Some natural number unification

generations(lee, virginia, 1).
generations(lee, garrett, 2).
generations(lee, robby, 2).
generations(suzy, jamie, 1).

generations(lee, virginia, 0)?            % No.
generations(lee, virginia, 1)?            % Yes.
generations(lee, virginia, 2)?            % No.

% Some list unifications

children(lee, [virginia, bob, suze]).
children(suzy, [chris, jamie]).

children(lee, [virginia, bob])?           % No.
children(lee, [bob, suzy])?               % No.
children(lee, [bob, virginia, suzy])?     % No.
children(suzy, [chris, jamie])?           % Yes.
