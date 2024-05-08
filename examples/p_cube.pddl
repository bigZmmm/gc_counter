
(define (problem cube-3)
 (:domain cube)
 (:init
       
      (oneof  (x p1)  (x p2)  (x p3)  )
      (oneof  (y p1)  (y p2)  (y p3)  )
      (oneof  (z p1)  (z p2)  (z p3)  ))
 
 (:goal
       (and (x p2) (y p2) (z p2))))

