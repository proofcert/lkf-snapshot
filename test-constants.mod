module test-constants.

pred_pname a "a" [] & pred_pname b "b" [].
pred_pname c "c" [] & pred_pname d "d" [].
pred_pname e "e" [] & pred_pname f "f" [].
pred_pname g "g" [] & pred_pname h "h" [].

pred_pname (r X) "r" [X].
pred_pname (t X) "t" [X].

pred_pname (q X Y) "q" [X,Y].
pred_pname (w X Y) "w" [X,Y].

fun_pname m "m" [] & fun_pname u "u" [] & fun_pname z "z" [].

fun_pname (s X) "s" [X].
fun_pname (k X) "k" [X].

fun_pname fi "fi" [].
fun_pname wi "wi" [].

pred_pname (is_fox  X) "is_fox" [X].
pred_pname (is_wolf X) "is_wolf" [X].
pred_pname (eats X Y) "eats" [X,Y].
