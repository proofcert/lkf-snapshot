sig mating-fpc.
accum_sig lkf-certificates.
accum_sig lib.

/* start */
kind nat    type.
type zero   nat.
type succ   nat -> nat. % successor
kind pair   type.       % pair of numbers
type pr     nat -> nat -> pair.
type ind    nat -> index.
type aux    nat -> cert.
typeabbrev  mating list pair.
type mating nat -> mating -> mating -> cert.
/* end */

