(define (square x)
  (* x x))

(define (triple-square-sum x y z)
  (cond ((= (min x y z) x) (+ (square y) (square z)))
        ((= (min x y z) y) (+ (square x) (square z)))
        ((= (min x y z) z) (+ (square y) (square x)))
  )
)