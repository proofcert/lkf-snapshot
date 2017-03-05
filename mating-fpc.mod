module mating-fpc.

/* start */
andC     (mating C I O) (mating C I M) (mating C M O).
falseC   (mating C I O) (mating C I O).
releaseE (mating C I O) (mating C I O).
orC      (mating C I O) (mating C I O).
allC     (mating C I O) (x\ mating C I O).
storeC   (mating C I O) (mating (succ C) I O) (ind C).
decideE  (mating C I ((pr Ix Jx)::I)) (aux Jx) (ind Ix).
initialE (aux Jx) (ind Jx).
/* end */
