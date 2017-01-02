(define (square x)
  (* x x))

(define (triple-square-sum x y z)
  (cond ((and (< x y) (< y z)) (+ (square y) (square z)))
        ((and (< y x) (< x z)) (+ (square x) (square z)))
        ((and (< z y) (< y x)) (+ (square y) (square x)))
  )
)