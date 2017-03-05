module exp-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate exp-fpc.

example 1 (eC (eOr eLit eLit)) (or (ng q') q').
example 2 (eIntro x\ eC (eAll x (eOr eLit eLit)))
          (forall x\ or (r' x) (ng (r' x))).

% The drinker formula
example 3 (eIntro y\ eIntro z\ eC
          (eSome [(pr a' (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).


% Example 3 but with circular dependencies
example 4 (eIntro y\ eIntro z\ eC
          (eSome [(pr z  (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).


example 5 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' a') (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted (and fails to check).
example 6 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).


% The drinker formula with order
example 7 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr a' (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).


% Example 3 but with circular dependencies and order (fails)
example 8 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr z  (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% This is example 5 with order.
example 9 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' a') (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted but with order (fails).
example 10 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% DM: Zak reminded me that I should be careful with a block of
% existentials.  Delays are needed after each existential.

example 11 (eC
    (eOr eLit
         (eSomeOrd [(pr     a'  (eSomeOrd [(pr     (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
     (or (ng (r' (h'    a'  (f' a')))) (exists x\ exists y\ r' (h' x y))).

example 12 (eC
    (eOr eLit
         (eSomeOrd [(pr    a'  (eSomeOrd [(pr      (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
    (or (ng (r' (h' (f' a') (f' (f' a'))))) (exists x\ exists y\ r' (h' x y))).

delay-   B D :- polarize B C, false- False, disj- False C D.

pred_pname q'      "q'" [].
pred_pname (r' X)  "r'" [X].

fun_pname  a'      "a'" [].
fun_pname (f' X)   "f'" [X].
fun_pname (h' X Y) "h'" [X, Y].

% RB: pred_pname replaces bool_atm.
polarize A      L :- pred_pname A Name Args, lit+ (atom Name Args) L.
polarize (ng A) L :- pred_pname A Name Args, lit- (atom Name Args) L.
polarize tt     A :- true-  A.
polarize ff     A :- false- A.
polarize (and B C)   A :- polarize B D, polarize C E, conj- D E A.
polarize (or  B C)   A :- polarize B D, polarize C E, disj- D E A.
polarize (imp B C)   A :- polarize (ng B) D, polarize C E, disj- D E A.
polarize (equiv B C) A :- polarize (imp B C) D, polarize (imp C B) E, conj- D E A.
polarize (ng (ng B)) C :- polarize B C.
polarize (ng (and B C)) A   :- polarize (ng B) D, polarize (ng C) E, disj- D E A.
polarize (ng (or  B C)) A   :- polarize (ng B) D, polarize (ng C) E, conj- D E A.
polarize (ng (imp B C)) A   :- polarize B D,      polarize (ng C) E, conj- D E A.
polarize (ng (equiv B C)) A :- polarize (ng (imp B C)) D, 
                               polarize (ng (imp C B)) E, disj- D E A.
polarize (forall B)      A :- (pi x\ polarize (B x) (D x)),      all-  D A.
polarize (ng (exists B)) A :- (pi x\ polarize (ng (B x)) (D x)), all-  D A.
% The follow uses of delay- breaks up a sequence of existentials.
polarize (exists B)      A :- (pi x\ delay-       (B x)  (D x)), some+ D A.
polarize (ng (forall B)) A :- (pi x\ delay-   (ng (B x)) (D x)), some+ D A.

test I          :- example I Exp Form, polarize Form B, check_exp Exp B.

check_exp (eC Exp) B :- lkf_entry (astate nil nil [pr B Exp]) B.
check_exp (eIntro Exp) B :- pi x\ check_exp (Exp x) B.


test_all :- example I Exp Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_spec Exp B :- (check_exp Exp B, print "#", fail) ; true.
