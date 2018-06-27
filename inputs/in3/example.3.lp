% Projection: 2 Variables
q(7).p(8,1,7).
a(X) :- p(X,Y,Z), q(X).

% After Projection:

% a(X) :- p'(X), q(X).
% p'(X) :- p(X,Y,Z).