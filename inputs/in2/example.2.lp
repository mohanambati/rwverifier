% Projection: 2 Variables
a(X) :- p(X,Y,Z).

% After Projection:

% a(X) :- p'(X), q(X).
% p'(X) :- p(X,Y,Z).