% Signature for first-order classical logic formulas.

sig classical.
accum_sig lib.

kind i                          type.
kind bool                       type.

type tt, ff                     bool.
type ng                     	bool -> bool.
type and, or, imp, equiv    	bool -> bool -> bool.
type forall, exists             (i -> bool) -> bool.

type pred_pname    bool -> string -> list i -> o.
type fun_pname     i    -> string -> list i -> o.

type copy          i -> i -> o.


