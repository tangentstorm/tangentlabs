% iota from APL (i. in j), in matlab/octave

iota = @(A) reshape(0:prod(A)-1, A)';

% octave:xx> iota([3 3])
% ans =
% 
%    0   1   2
%    3   4   5
%    6   7   8

% @(A) → lambda
% x:y  → range (inclusive)
% A'   → transpose
% reshape is j's $
% prod is j's */
