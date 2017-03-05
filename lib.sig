sig lib.

type announce, spy    o -> o.
type bracket          string -> o -> string -> o.

type foreach, forsome   (A -> o) -> list A -> o.
type mappred            (A -> B -> o) -> list A -> list B -> o.
type foldr              (A -> B -> B -> o) -> list A -> B -> B -> o.
type split              list A -> list A -> list A -> o.
type if                 o -> o -> o -> o.
type mapfun             (A -> B) -> list A -> list B -> o.
type memb               A -> list A -> o.
type memb_and_rest      A -> list A -> list A -> o.
type length             list A -> int -> o.

type join               list A -> list A -> list A -> o.
type inc                int -> int -> o.
