sig lkf-kernel.
accum_sig lkf-certificates.
accum_sig lib.

type lkf_entry      cert -> form -> o.

/* sequents */
type async           cert -> list form -> o.
type sync            cert ->      form -> o.
type storage        index ->      form -> o.
/* end */
