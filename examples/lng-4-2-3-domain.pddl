
(define (domain look-and-grab) 

   (:requirements :strips :typing)
   (:types pos obj)
   (:constants  o1 o2 o3 - obj     p1-1
    p1-2
    p1-3
    p1-4
    p2-1
    p2-2
    p2-3
    p2-4
    p3-1
    p3-2
    p3-3
    p3-4
    p4-1
    p4-2
    p4-3
    p4-4
 - pos) 
   (:predicates (adj ?i - pos ?j - pos) (at ?i - pos) (holding ?o - obj) (obj-at ?o - obj ?i - pos) (handempty))
   (:action move
      :parameters (?i - pos ?j - pos )
      :precondition (and (adj ?i ?j) (at ?i))
      :effect (and (not (at ?i)) (at ?j)))

   (:action pickup-1-1-look-2
      :precondition (at p1-1) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p1-1)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p1-1)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p1-1)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       ))

   (:action pickup-1-2-look-2
      :precondition (at p1-2) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p1-2)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p1-2)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p1-2)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       ))

   (:action pickup-1-3-look-2
      :precondition (at p1-3) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p1-3)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p1-3)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p1-3)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       ))

   (:action pickup-1-4-look-2
      :precondition (at p1-4) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p1-4)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p1-4)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p1-4)))
            
            ; X = 1
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       ))

   (:action pickup-2-1-look-2
      :precondition (at p2-1) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p2-1)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p2-1)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p2-1)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       ))

   (:action pickup-2-2-look-2
      :precondition (at p2-2) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p2-2)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p2-2)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p2-2)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-2-3-look-2
      :precondition (at p2-3) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p2-3)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p2-3)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p2-3)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-2-4-look-2
      :precondition (at p2-4) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p2-4)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p2-4)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p2-4)))
            
            ; X = 1
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-3-1-look-2
      :precondition (at p3-1) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p3-1)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p3-1)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p3-1)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       ))

   (:action pickup-3-2-look-2
      :precondition (at p3-2) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p3-2)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p3-2)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p3-2)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-3-3-look-2
      :precondition (at p3-3) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p3-3)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p3-3)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p3-3)))
            
            ; X = 1
                ; Y = 1
          (when (and (handempty) (obj-at o1 p1-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-1))))
                                       
          (when (and (handempty) (obj-at o2 p1-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-1))))
                                       
          (when (and (handempty) (obj-at o3 p1-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-3-4-look-2
      :precondition (at p3-4) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p3-4)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p3-4)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p3-4)))
            
            ; X = 1
                ; Y = 2
          (when (and (handempty) (obj-at o1 p1-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-2))))
                                       
          (when (and (handempty) (obj-at o2 p1-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-2))))
                                       
          (when (and (handempty) (obj-at o3 p1-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p1-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-3))))
                                       
          (when (and (handempty) (obj-at o2 p1-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-3))))
                                       
          (when (and (handempty) (obj-at o3 p1-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p1-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p1-4))))
                                       
          (when (and (handempty) (obj-at o2 p1-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p1-4))))
                                       
          (when (and (handempty) (obj-at o3 p1-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p1-4))))
                                       
            ; X = 2
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-4-1-look-2
      :precondition (at p4-1) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p4-1)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p4-1)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p4-1)))
            
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       ))

   (:action pickup-4-2-look-2
      :precondition (at p4-2) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p4-2)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p4-2)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p4-2)))
            
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-4-3-look-2
      :precondition (at p4-3) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p4-3)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p4-3)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p4-3)))
            
            ; X = 2
                ; Y = 1
          (when (and (handempty) (obj-at o1 p2-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-1))))
                                       
          (when (and (handempty) (obj-at o2 p2-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-1))))
                                       
          (when (and (handempty) (obj-at o3 p2-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 1
          (when (and (handempty) (obj-at o1 p3-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-1))))
                                       
          (when (and (handempty) (obj-at o2 p3-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-1))))
                                       
          (when (and (handempty) (obj-at o3 p3-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 1
          (when (and (handempty) (obj-at o1 p4-1))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-1))))
                                       
          (when (and (handempty) (obj-at o2 p4-1))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-1))))
                                       
          (when (and (handempty) (obj-at o3 p4-1))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-1))))
                                       
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action pickup-4-4-look-2
      :precondition (at p4-4) 
      :effect (and 
          (when (holding o1)
                (and (handempty) (not (holding o1)) (obj-at o1 p4-4)))
            
          (when (holding o2)
                (and (handempty) (not (holding o2)) (obj-at o2 p4-4)))
            
          (when (holding o3)
                (and (handempty) (not (holding o3)) (obj-at o3 p4-4)))
            
            ; X = 2
                ; Y = 2
          (when (and (handempty) (obj-at o1 p2-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-2))))
                                       
          (when (and (handempty) (obj-at o2 p2-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-2))))
                                       
          (when (and (handempty) (obj-at o3 p2-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p2-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-3))))
                                       
          (when (and (handempty) (obj-at o2 p2-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-3))))
                                       
          (when (and (handempty) (obj-at o3 p2-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p2-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p2-4))))
                                       
          (when (and (handempty) (obj-at o2 p2-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p2-4))))
                                       
          (when (and (handempty) (obj-at o3 p2-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p2-4))))
                                       
            ; X = 3
                ; Y = 2
          (when (and (handempty) (obj-at o1 p3-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-2))))
                                       
          (when (and (handempty) (obj-at o2 p3-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-2))))
                                       
          (when (and (handempty) (obj-at o3 p3-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p3-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-3))))
                                       
          (when (and (handempty) (obj-at o2 p3-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-3))))
                                       
          (when (and (handempty) (obj-at o3 p3-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p3-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p3-4))))
                                       
          (when (and (handempty) (obj-at o2 p3-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p3-4))))
                                       
          (when (and (handempty) (obj-at o3 p3-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p3-4))))
                                       
            ; X = 4
                ; Y = 2
          (when (and (handempty) (obj-at o1 p4-2))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-2))))
                                       
          (when (and (handempty) (obj-at o2 p4-2))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-2))))
                                       
          (when (and (handempty) (obj-at o3 p4-2))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-2))))
                                       
                ; Y = 3
          (when (and (handempty) (obj-at o1 p4-3))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-3))))
                                       
          (when (and (handempty) (obj-at o2 p4-3))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-3))))
                                       
          (when (and (handempty) (obj-at o3 p4-3))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-3))))
                                       
                ; Y = 4
          (when (and (handempty) (obj-at o1 p4-4))
                (and (not (handempty)) (holding o1) (not (obj-at o1 p4-4))))
                                       
          (when (and (handempty) (obj-at o2 p4-4))
                (and (not (handempty)) (holding o2) (not (obj-at o2 p4-4))))
                                       
          (when (and (handempty) (obj-at o3 p4-4))
                (and (not (handempty)) (holding o3) (not (obj-at o3 p4-4))))
                                       ))

   (:action putdown
      :parameters (?p - pos)
      :precondition (at ?p)
      :effect (and 
                 (when (holding o1)
                       (and (handempty) (not (holding o1)) (obj-at o1 ?p)))
                       
                 (when (holding o2)
                       (and (handempty) (not (holding o2)) (obj-at o2 ?p)))
                       
                 (when (holding o3)
                       (and (handempty) (not (holding o3)) (obj-at o3 ?p)))
                       ))
      )

