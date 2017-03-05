sig cnf-examples.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig cnf-fpc.

type test_all                  o.
type test                      int  -> o.
type example                   int  -> bool -> o.
type check_tautology           bool -> o.
