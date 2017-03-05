module pairing-fpc.

/* start */
allC     (A <c> B) (x\ (C x) <c> (D x))    :- allC A C,       allC B D. 
andC     (A <c> B) (C <c> D) (E <c> F)     :- andC A C E,     andC B D F.
andE     (A <c> B) (C <c> D) (E <c> F)     :- andE A C E,     andE B D F.
cutE     (A <c> B) (C <c> D) (E <c> F) Cut :- cutE A C E Cut, cutE B D F Cut. 
decideE  (A <c> B) (C <c> D) (I <i> J)     :- decideE A C I,  decideE B D J.
falseC   (A <c> B) (C <c> D)               :- falseC A C,     falseC B D.
initialE (C <c> B) (I <i> J)               :- initialE C I,   initialE B J.
orC      (A <c> B) (C <c> D)               :- orC A C,        orC B D.
orE      (A <c> B) (C <c> D) E             :- orE A C E,      orE B D E. 
releaseE (A <c> B) (C <c> D)               :- releaseE A C,   releaseE B D.
someE    (A <c> B) (C <c> D) W             :- someE A C W,    someE B D W.
storeC   (A <c> B) (C <c> D) (I <i> J)     :- storeC A C I,   storeC B D J.
trueE    (A <c> B)                         :- trueE A,        trueE B.
/* end */
