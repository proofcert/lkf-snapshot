module oracle-fpc.

decideE  (start Oracle) (consume Oracle) root. 
storeC   (start Oracle) (start Oracle) root.

initialE (consume emp) lit.
trueE    (consume emp).
andE     (consume (co OracleL OracleR)) (consume OracleL) (consume OracleR).
orE      (consume (lo Oracle)) (consume Oracle) left.
orE      (consume (ro Oracle)) (consume Oracle) right.
releaseE (consume Oracle) (restart Oracle).

decideE  (restart Oracle) (consume Oracle) root.
storeC   (restart Oracle) (restart Oracle) lit.
