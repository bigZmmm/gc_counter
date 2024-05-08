(define (problem bomb-5-1)
   (:domain bomb)(:objects  bomb1  bomb2  bomb3  bomb4  bomb5   - bomb 
toilet1   - toilet)
   (:init 
      (oneof (armed bomb1) (narmed bomb1))
      (oneof (armed bomb2) (narmed bomb2))
      (oneof (armed bomb3) (narmed bomb3))
      (oneof (armed bomb4) (narmed bomb4))
      (oneof (armed bomb5) (narmed bomb5))
      (nclogged toilet1)       )
    (:goal (and
      (narmed bomb1)       (narmed bomb2)       (narmed bomb3)       (narmed bomb4)       (narmed bomb5)     )))
