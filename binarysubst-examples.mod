%% Binary resolution with subsitution terms
module binarysubst-examples.
accumulate lib.
accumulate classical.
accumulate test-constants.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate binarysubst-fpc.

test_all :- example N _ _ _,
  term_to_string N Str, print Str, print "  ", 
            test_resol' N, print "\n", fail.

test_resol' N :- (test_resol N, print "#", fail); true.

test_resol N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start 1 Resol) B).

test_reveal N :-
  example N Clauses Lemmas Resol, false- False,
  foldr (C\A\R\ sigma D\sigma D'\ 
                nnf conj+ disj- (ng C) D, ensure+ D D', disj- D' A R) 
        Clauses False B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start 1 Resol) B),
  term_to_string (start 1 Resol) String,
  print "Certificate = \n", print String, print "\n".

assume_lemmas C nil    G :- G.
assume_lemmas C [L|Ls] G :-
   C' is C + 1, nnf conj+ disj- L L', ensure- L' L'',
   (lemma C L'' => assume_lemmas C' Ls G).

% The following are example certificates from the client's point-of-view.
% There are three lists:
%  1. The list of clauses, which when taken as hypothesis, yields
%     a contradiction. 
%  2. A list of "lemma".  These are new clauses that are resolvants
%     of previous clauses.
% 3. The certificate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%   Propositional examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%  A single propositional letter

example 10 
  [a,
  (ng a)]
  [ff]
  [resolve 3 (res 1 (rex 2 done))].

example 20
  [(ng a),
   a]
  [ff]
  [resolve 3 (res 2 (rex 1 done))].

example 30 
  [(or a ff),
   (or (ng a) ff)]
  [ff]
  [resolve 3 (res 1 (rex 2 done))].

example 40   % This one fails.  One must factor explicitly to proceed.
  [(or a a),
   (or (ng a) (ng a))]
  [ff]
  [resolve 3 (res 1 (rex 2 done))].

example 41   % This variant works but leaves lots of backtrack points.
  [(or a a),            % 1
   (or (ng a) (ng a))]  % 2
  [a,                   % 3
   (ng a),              % 4
   ff]                  % 5
  [factor 1 3, 
   resolve 4 (res 3 (rex 2 done)),
   resolve 5 (res 3 (rex 4 done))].

example 42   % This variant is a "permutation" of above but with fewer backtrack points.
  [(or a a),            % 1
   (or (ng a) (ng a))]  % 2
  [a,                   % 3
   (ng a),              % 4
   ff]                  % 5
  [factor 1 3, 
   factor 2 4,
   resolve 5 (res 3 (rex 4 done))].

example 43
  [(or a a),           % 1
   (ng a)]             % 2
  [a,                  % 3
   ff]                 % 4
  [factor 1 3, 
   resolve 4 (res 3 (rex 2 done))].

example 44 % dual of 40
  [(or (ng a) (ng a)),      % 1
   a]                       % 2
  [(ng a),                  % 3
   ff]                      % 4
  [factor 1 3, 
   resolve 4 (res 2 (rex 3 done))].

example 45 % not checkable
  [a,                  % 1
   (ng a)]             % 2
  [(or a a),           % 3
   ff]                 % 4
  [factor 1 3, 
   resolve 4 (res 3 (rex 2 done))].

%%%%  Multiple propositional letters

example 70 
  [(or a b),           % 1
   (or (ng a) e),      % 2
   (ng b),             % 3
   (ng e)]             % 4
  [(or b e),           % 5
   e,                  % 6
   ff]                 % 7
  [resolve  5 (res 1 (rex 2 done)),
   resolve  6 (res 5 (rex 3 done)),
   resolve  7 (res 6 (rex 4 done))].

example 71
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (or (ng a) b),      % 3
   (or (ng a) (ng b))] % 4
  [(or a a),           % 5
   a,                  % 6
   (or (ng a) (ng a)), % 7
   (ng a),             % 8
   ff]                 % 9
  [resolve 5 (res 1 (rex 2 done)),
   factor 5 6, 
   resolve 7 (res 3 (rex 4 done)),
   factor 7 8,
   resolve 9 (res 6 (rex 8 done))].

example 72  % Just like 71 but factoring is moved into the resol method
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (or (ng a) b),      % 3
   (or (ng a) (ng b))] % 4
  [a,                  % 5
   (ng a),             % 6
   ff]                 % 7
  [resolve 5 (res 1 (rex 2 done)),
   resolve 6 (res 3 (rex 4 done)),
   resolve 7 (res 5 (rex 6 done))].

example 80
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [(or a a),           % 4
   a,                  % 5
   ff]                 % 6
  [resolve 4 (res 1 (rex 2 done)),
   factor 4 5,
   resolve 6 (res 5 (rex 3 done))].

example 81   % A variation on 80.  Permute the rules to eliminate "a" 
             % first so it is not appearring twice in the combined side formulas.
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [b,                  % 4
   (ng b),             % 5
   ff]                 % 6
  [resolve 4 (res 1 (rex 3 done)), 
   resolve 5 (res 2 (rex 3 done)),
   resolve 6 (res 4 (rex 5 done))].

example 82  % Another variation but the factoring is done internally.
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [a,                  % 4
   ff]                 % 5
  [resolve 4 (res 1 (rex 2 done)),
   resolve 5 (res 4 (rex 3 done))].

example 90
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [a,                  % 4
   ff]                 % 5
  [resolve 4 (res 1 (rex 2 done)), 
   resolve 5 (res 4 (rex 3 done))].

example 91
  [(or a b),           % 1
   (or a (ng b)),      % 2
   (ng a)]             % 3
  [(or (or a a) (or a a)),    % 4  It is repetition here that causes backtracking
   a,                  % 5
   ff]                 % 6
  [resolve 4 (res 1 (rex 2 done)), 
   factor 4 5,
   resolve 6 (res 5 (rex 3 done))].

% Conjectures: The following are for the propositional case.

%  (1) If there repeated literals in the resolvant, then there are
%      backtrack points that are not useful to have.
%  (2) If there are repeated literals in the combined side formulas,
%      then there are also backtrack points.

% The use of implicit factoring (write down the resolvant without
% repeats) can eliminate (1) backtracking.  Use of explicit factoring
% (as defined in this FPC) is too late to get rid of backtrack
% points.

% Eliminating (2) seems hard in this framework.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Simple quantificational examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

example 100 
  [(r z),                           % 1
   (forall x\ or (ng (r x)) (t x)), % 2
   (ng (t z))]                      % 3
  [(t z),                           % 4
   ff]                              % 5
  [resolve 4 (res 1 (rex 2 (subst z done))),
   resolve 5 (res 4 (rex 3 done))].

example 110 
 [(r z),                                            % 1
  (forall x\ or (ng (r x)) (r (k x))),              % 2
  (ng (r (k (k (k (k z))))))]                       % 3
 [(forall x\ or (ng (r x)) (r (k (k x)))),          % 4
  (forall x\ or (ng (r x)) (r (k (k (k (k x)))))),  % 5
  (r (k (k (k (k z))))),                            % 6
  ff]                                               % 7
[ resolve 4 (rquant x\ res 2 (subst x (rex 2 (subst (k x) done)))),
  resolve 5 (rquant x\ res 4 (subst x (rex 4 (subst (k (k x)) done)))),
  resolve 6 (res 1 (rex 5 (subst z done))),
  resolve 7 (res 6 (rex 3 done))].

example 111 % same a 110 but without explicit subterm
 [(r z),                                            % 1
  (forall x\ or (ng (r x)) (r (k x))),              % 2
  (ng (r (k (k (k (k z))))))]                       % 3
 [(forall x\ or (ng (r x)) (r (k (k x)))),          % 4
  (forall x\ or (ng (r x)) (r (k (k (k (k x)))))),  % 5
  (r (k (k (k (k z))))),                            % 6
  ff]                                               % 7
[ resolve 4 (rquant x\ res 2 (subst (M x) (rex 2 (subst (N x) done)))),
  resolve 5 (rquant x\ res 4 (subst (P x) (rex 4 (subst (Q x) done)))),
  resolve 6 (res 1 (rex 5 (subst R done))),
  resolve 7 (res 6 (rex 3 done))].

example 120
 [(r z),                                % 1
  (forall x\ or (ng (r x)) (r (k x))),  % 2
  (ng (r (k (k (k (k z))))))]           % 3
 [(r (k z)),                            % 4
  (r (k (k z))),                        % 5
  (r (k (k (k z)))),                    % 6
  (r (k (k (k (k z))))),                % 7
  ff]                                   % 8
[ resolve 4 (res 1 (rex 2 (subst z done))),
  resolve 5 (res 4 (rex 2 (subst  (k z) done))),
  resolve 6 (res 5 (rex 2 (subst  (k (k z)) done))),
  resolve 7 (res 6 (rex 2 (subst  (k (k (k z))) done))),
  resolve 8 (res 7 (rex 3 done))].

example 130
[ (is_wolf wi),                            % 1
  (forall x\ forall y\ or (ng (is_wolf  x)) (or (ng (is_fox y)) (ng (eats x y)))), % 2
  (is_fox fi),                             % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve 5 (res 1 (rex 2 (subst _ (subst _ done)))),
  resolve 6 (res 3 (rex 5 done)),
  resolve 7 (res 4 (rex 6 done))].

example 131
[ (is_wolf  wi),                           % 1
  (forall x\ forall y\ (or (ng (is_wolf  x)) (or (ng (is_fox y)) (ng (eats x y))))), % 2
  (is_fox   fi),                           % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve 5 (res 1 (rex 2 (subst wi (subst fi done)))),
  resolve 6 (res 3 (rex 5 done)),
  resolve 7 (res 4 (rex 6 done))].

example 132
[ (is_wolf  wi),                           % 1
  (or (ng (is_wolf  wi)) (or (ng (is_fox fi)) (ng (eats wi fi)))), % 2
  (is_fox   fi),                           % 3
  (eats wi fi)]                            % 4
[ (or (ng (is_fox fi)) (ng (eats wi fi))), % 5
  (ng (eats wi fi)),                       % 6
  ff]                                      % 7
[ resolve 5 (res 1 (rex 2 done)),
  resolve 6 (res 3 (rex 5 done)),
  resolve 7 (res 4 (rex 6 done))].

example 133
[ a,                              % 1
  (or (ng a) (or (ng b) (ng c))), % 2
  b,                              % 3
  c]                              % 4
[ (or (ng b) (ng c)),             % 5
  (ng c),                         % 6
  ff]                             % 7
[ resolve 5 (res 1 (rex 2 done)),
  resolve 6 (res 3 (rex 5 done)),
  resolve 7 (res 4 (rex 6 done))].

example 134
[ a,                              % 1
  (or (ng a) (ng b)),             % 2
  b]                              % 3
[ (ng b),                         % 4
  ff]                             % 5
[ resolve 4 (res 1 (rex 2 done)),
  resolve 5 (res 3 (rex 4 done))].
