sig cnf-mating-elab.
accum_sig lib.
accum_sig classical, polarize.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig cnf-fpc.
accum_sig mating-fpc.
accum_sig pairing-fpc.

type test_all                  o.
type test                      int  -> o.
type example                   int  -> bool -> o.
type check_tautology           bool -> o.

type test_elab                 int  -> o.
