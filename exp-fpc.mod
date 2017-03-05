/* Notes: There is a lot of non-determinism in the selection of an
   expansion term when one views the collection of expansion terms
   used to instantiate a quantifier as being a multiset.  This
   observation leads to at least three ways to present the expansion
   terms associated to an existential quantifier.

   (1) as a multiset
   (2) as a list (take the multiset in 1 and do a topological sort 
       using the dependency relation) 
   (3) as a list of multisets of element (take the dependency relation,
       and repeated collect together the minimal elements.  Notice that
       the multisets here can also be lists (the order there, however,
       is arbitrary.

 Notes: The Left component in the astate and sstate certificates
 should probably be split into two parts: one containing just
 literals and one containing just existentials.  This would help
 make the code cleaner and a bit faster.
*/
module exp-fpc.

% Used to translate "external" terms to "internal" terms (has to do
% with the different treatment of eigenvariables in expansion trees
% and in sequent calculus.

translate_term [] Term Term' :- copy Term Term'.
translate_term ((pr X Y)::As) Term Term' :- copy X Y => translate_term As Term Term'.

orC    (astate Vs Left ((pr B (eOr E1 E2))::Qs))
       (astate Vs Left ((pr B1 E1)::(pr B2 E2)::Qs))         :- disj- B1 B2 B.
andC   (astate Vs Left ((pr B (eAnd E1 E2))::Qs))
       (astate Vs Left ((pr B1 E1)::Qs))
       (astate Vs Left ((pr B2 E2)::Qs))                     :- conj- B1 B2 B.
allC   (astate Vs Left ((pr ForallB (eAll Uvar E))::Qs))
       (x\ astate ((pr Uvar x)::Vs) Left ((pr (B x) E)::Qs)) :- all- B ForallB.
falseC (astate Vs Left ((pr B eFalse)::Qs))
       (astate Vs Left Qs)                                   :- false- B.

% RB: Removing Form as inspecting formula.
storeC (astate Vs Left ((pr Form ET)::Qs))
       (astate Vs ((pr Form ET)::Left) Qs)
       (idx Form)                          :- lit- _ Form; lit+ _ Form; some+ _ Form.

% RB: From mdecide to decide.
decideE (astate Vs Left []) (sstate Vs Left (pr Plit eLit)) (idx Plit) :- 
 % Decide on a literal only if no existentials are present
  foreach (pair\ sigma Lit\ pair = (pr Lit eLit)) Left,
  memb (pr Plit eLit) Left.

decideE
  (astate Vs Left [])
  (sstate Vs Left' (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome [pr Term ExTree])) Left Left'.

decideE
  (astate Vs Left [])
  (sstate Vs   ((pr Exists (eSome SubExp'))::Left') (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSome SubExp)) Left Left',
  memb_and_rest (pr Term ExTree) SubExp SubExp', SubExp' = (_::_).

decideE
  (astate Vs Left [])
  (sstate Vs Left' (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd [pr Term ExTree])) Left Left'.

decideE
  (astate Vs Left [])
  (sstate Vs ((pr Exists (eSomeOrd SubExp'))::Left') (pr Exists (eSome [pr Term ExTree])))
  (idx Exists) :-
  memb_and_rest (pr Exists (eSomeOrd SubExp)) Left Left',
  SubExp = ((pr Term ExTree)::SubExp'), SubExp' = (_::_).

% After instantiating the existential, we are followed by a delay-.
% Thus, we introduce a new certificate constructor to guide us
% through this small detour.
someE (sstate Vs Left (pr Form (eSome [pr Term ExTree])))
      (dstate Vs Left [(pr (Body Term') ExTree)])
      Term' :-
  some+ Body Form, translate_term Vs Term Term'.

releaseE (sstate Vs Left Neg) (astate Vs Left [Neg]).

initialE _ _.

trueE _.

releaseE (dstate Vs Left Neg) (dstate Vs Left Neg).
% RB: B disappears here disappears as external formula, and (pr D E) becomes
% (pr B E).
orC      (dstate Vs Left ((pr B E)::nil))
         (dstate Vs Left ((pr B1 eFalse)::(pr B2 E)::nil)) :- disj- B1 B2 B.
falseC   (dstate Vs Left ((pr B eFalse)::(pr B2 E2)::nil))
         (astate Vs Left ((pr B2 E2)::nil))                :- false- B.
