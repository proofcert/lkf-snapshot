sig canonical-inductive-fpc.
accum_sig lkf-certificates.
kind nat    type.
type zero   nat.
type succ   nat -> nat. % Successor
/* start */
kind can type.
type can          nat -> can -> cert.
type cani       index -> can -> can. 
type can1                can -> can.   
type can2         can -> can -> can. 
type canv         (A -> can) -> can. 
type cant           A -> can -> can. 
type cana              index -> can. 
type can0                       can.
type canf form -> can -> can -> can.
type canc      choice -> can -> can.
type ix                nat -> index.
/* end */
