module cnf-mating-elab.
accumulate lib.
accumulate classical.
accumulate test-constants.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate cnf-fpc.
accumulate mating-fpc.
accumulate pairing-fpc.

check_tautology B :- nnf conj- disj- B B', lkf_entry cnf B'.

test X :- 
   example X F, 
   (sigma Str\ term_to_string X Str, print Str, print " "),
   if (check_tautology F)
      (print "Success\n") 
      (print "Fail\n"), 
  fail.

test_all :-
  example X _,
  test X.

test_elab X :-
  example X F,
  % Inline check_tautology and adapt pairing
  nnf conj- disj- F F',
  lkf_entry (cnf <c> (mating zero nil Mating')) F',
  % Output results
  term_to_string (cnf <c> (mating zero nil Mating')) String,
  print "Certificate = \n",
  print String,
  print "\n".

example 1 (or a (ng a)).
example 2 (equiv (equiv b a) (equiv a b)).
example 3 (equiv (imp b a) (imp (ng a) (ng b))).
example 4 (equiv (equiv b a) (equiv (ng a) (ng b))).
example 5 (imp (imp (imp b a) b) b).
example 6 (imp (equiv b a) (equiv a b)).
example 7 (imp (equiv b a) (equiv (ng a) (ng b))).
example 8 (equiv b b).
example 9 (imp (imp b a) (imp b a)).
example 10 (imp (and b a) (and b a)).
example 11 (imp (and b a) a).
% The followineg are examples 8, 12, 17 (resp) from 
% Pelletier's article "Seventy-Five Problems for testineg Atomatic
% theorem Provers" (JAR 1986).
example 12 (imp (imp (imp b a) b) b). 
example 13 (equiv (equiv (equiv b a) c) (equiv b (equiv a c))).
example 14 (equiv (imp (and b (imp a c)) d)
                  (and (or (ng b) (or a d))
                       (or (ng b) (or (ng c) d)))).
example 15 (imp a (and a a)).

%/*  Not tautologies
example 20 (equiv (equiv b a) (equiv (ng c) (ng b))). 
example 21 (equiv b a).
example 22 (equiv (equiv b a) (equiv d c)).
example 23 (and Ex4 c) :- example 4 Ex4.
%*/
