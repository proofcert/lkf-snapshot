module canonical-fpc.

/* start */
allC	 (can N (canv C ))    	 (x\ can N (C x)).
andC     (can N (can2 A B))   	 (can N A) (can N B).
andE     (can N (can2 A B))   	 (can N A) (can N B).
cutE 	 (can N (canf F A B)) 	 (can N A) (can N B) F.
decideE  (can N (cani I A))   	 (can N A) I.
storeC   (can N (cani (ix N) A)) (can M A) (ix N) :- M is N + 1.
falseC   (can N (can1 A))     	 (can N A).
orC      (can N (can1 A))     	 (can N A).
releaseE (can N (can1 A))     	 (can N A).
orE      (can N (canc C A))   	 (can N A) C.
someE	 (can N (cant T A))   	 (can N A) T.
trueE  	 (can N (can0)).
initialE (can N (cana I)) I.
/* end */
% When replaying: give a negative counter so that the store
% Does not use it.
% storeC   (can N (cani I A)) (can N A) I :- N < 0.

