(define (domain ring)

  (:predicates (position ?x) (closed ?x) (locked ?x) (open ?x))

  (:action move-up
   :parameters ()
   :effect (and 
             (when (position pos1) 
		(and (not (position pos1)) (position pos2)))
             (when (position pos2) 
		(and (not (position pos2)) (position pos3)))
             (when (position pos3) 
		(and (not (position pos3)) (position pos4)))
             (when (position pos4) 
		(and (not (position pos4)) (position pos1)))))

  (:action move-down
   :parameters ()
   :effect (and 
             (when (position pos1) 
		(and (not (position pos1)) (position pos4)))
             (when (position pos2) 
		(and (not (position pos2)) (position pos1)))
             (when (position pos3) 
		(and (not (position pos3)) (position pos2)))
             (when (position pos4) 
		(and (not (position pos4)) (position pos3)))))

   (:action lock
    :parameters ()
    :effect (and (when (and (position pos1)(closed win1)) (and (locked win1) (not (locked win2))) )
	         (when (and (position pos2)(closed win2))(locked win2))
                 (when (and (position pos3)(closed win3))(locked win3))
                 (when (and (position pos4)(closed win4))(locked win4))))

   (:action close
    :parameters ()
    :effect (and (when (position pos1)(closed win1))
	         (when (position pos2)(closed win2))
                 (when (position pos3)(closed win3))
                 (when (position pos4)(closed win4))))

)
