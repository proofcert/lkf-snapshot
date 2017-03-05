module polarize.

% nnf Conj Disj A B :- announce (nnf Conj Disj A B).

% nnf is one of many possible ways to polarize LK formulas.  You can select 
% polarity only for conj and disj (the polarity of their units is
% determined by that selection).  The polarity of atomic formulas is 
% fixed for all uses.  Other polarization predicates can easily be 
% written and used.

nnf _ _ A      L :- pred_pname A Name Args, lit+ (atom Name Args) L.
nnf _ _ (ng A) L :- pred_pname A Name Args, lit- (atom Name Args) L.

nnf conj+ _ tt A :- true+ A.
nnf conj- _ tt A :- true- A.
nnf _ disj+ ff A :- false+ A.
nnf _ disj- ff A :- false- A.

nnf Conj Disj (and B C)   A :- nnf Conj Disj B D, nnf Conj Disj C E, Conj D E A.
nnf Conj Disj (or  B C)   A :- nnf Conj Disj B D, nnf Conj Disj C E, Disj D E A.
nnf Conj Disj (imp B C)   A :- nnf Conj Disj (ng B) D, nnf Conj Disj C E, Disj D E A.
nnf Conj Disj (equiv B C) A :- nnf Conj Disj (imp B C) D, nnf Conj Disj (imp C B) E, Conj D E A.
nnf Conj Disj (forall B) A :- (pi x\ nnf Conj Disj (B x) (D x)), all-  D A.
nnf Conj Disj (exists B) A :- (pi x\ nnf Conj Disj (B x) (D x)), some+ D A.

nnf conj+ _ (ng ff) A :- true+ A.
nnf conj- _ (ng ff) A :- true- A.
nnf _ disj+ (ng tt) A :- false+ A.
nnf _ disj- (ng tt) A :- false- A.

nnf Conj Disj (ng (ng B)) C :- nnf Conj Disj B C.
nnf Conj Disj (ng (and B C)) A   :- nnf Conj Disj (ng B) D, nnf Conj Disj (ng C) E, Disj D E A.
nnf Conj Disj (ng (or  B C)) A   :- nnf Conj Disj (ng B) D, nnf Conj Disj (ng C) E, Conj D E A.
nnf Conj Disj (ng (imp B C)) A   :- nnf Conj Disj B D,      nnf Conj Disj (ng C) E, Conj D E A.
nnf Conj Disj (ng (equiv B C)) A :- nnf Conj Disj (ng (imp B C)) D, 
                                    nnf Conj Disj (ng (imp C B)) E, Disj D E A.
nnf Conj Disj (ng (forall B)) A :- (pi x\ nnf Conj Disj (ng (B x)) (D x)), some+ D A.
nnf Conj Disj (ng (exists B)) A :- (pi x\ nnf Conj Disj (ng (B x)) (D x)), all-  D A.
