module oracle-dd-elab.
accumulate lib.
accumulate classical.
accumulate test-constants.
accumulate lkf-formulas.
accumulate polarize.
accumulate lkf-kernel.
accumulate oracle-fpc.
accumulate dd-fpc.
accumulate pairing-fpc.

test_all :- example X Form Oracle,
            (sigma Str\ term_to_string X Str, print Str, print " "),
            if (nnf conj+ disj+ Form B, lkf_entry (start Oracle) B)
               (print "Success\n") (print "Fail\n"),
            fail.

test N :- example N Form Oracle, nnf conj+ disj+ Form B, lkf_entry (start Oracle) B.

test_elab N :-
  example N Form Oracle,
  nnf conj+ disj+ Form B,
  lkf_entry ((start Oracle) <c> (dd M)) B,
  term_to_string ((start Oracle) <c> (dd M)) String,
  print "Certificate = \n",
  print String,
  print "\n".

example 1 (or a (ng a)) (ro (lo emp)).

example 2 (or (ng b) (or (and b (ng a)) (or (and a (ng d)) d)))
          (lo
          (ro (lo (co emp
          (ro (ro (lo (co emp
          (ro (ro (ro emp))))))))))).

example 3 (imp (imp (imp a b) a) a) (lo (co (lo (ro emp)) (ro emp))).

% The following example should fail.
example 4 (imp (imp (imp a b) a) a) (lo (co (ro (ro emp)) (ro emp))).


