module lib.

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).

foreach P nil.
foreach P (X::L) :- P X, foreach P L.

forsome P (X::L) :- P X; forsome P L.

mappred P nil nil.
mappred P (X::L) (Y::K) :- P X Y, mappred P L K.

foldr P nil    X X.
foldr P (Z::L) X Y :- foldr P L X W, P Z W Y.

split nil nil nil.
split (A::K) (A::L) R & split (A::K) L (A::R) :- split K L R.

if Cond Then Else :- Cond, !, Then.
if Cond Then Else :- Else.

mapfun F nil nil.
mapfun F (X::L) ((F X)::K) :- mapfun F L K.

memb A [A|_].
memb A [_|L] :- memb A L.

memb_and_rest A [A|L] L.
memb_and_rest A [B|L] [B|K] :- memb_and_rest A L K.

length []    0.
length [_|L] C :- length L C', C is C' + 1.

join nil K K.
join (X::L) K M :- join L K M', (memb X M', !, M = M' ; M = (X::M')).

% A more flexible increment predicate for non-negative integers.

inc M N :- P is (0 - 1), not (N = P), M is N - 1.
inc M N :- P is (0 - 1), not (M = P), N is M + 1.
