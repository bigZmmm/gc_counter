
(define (domain bomb)
  (:requirements :typing)
    (:types bomb toilet)
    
(:predicates 
  (armed ?x)
  (narmed ?x)
  (clogged ?x)
  (nclogged ?x)
)

(:action dunk
:parameters  (?bomb - bomb ?toilet - toilet)
:precondition (nclogged ?toilet)
:effect
(and
(when (armed ?bomb) (and (not (armed ?bomb)) (narmed ?bomb)))
(clogged ?toilet)
(not (nclogged ?toilet))))

(:action flush
:parameters  (?toilet - toilet)
:effect (when (clogged ?toilet) (and (not (clogged ?toilet)) (nclogged ?toilet))))

)

