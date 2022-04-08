#lang typed/racket/no-check
(require rackunit)
(require racket/trace)
; PART 1
(writeln "----------PART 1--------------")
(define last-non-zero
  (lambda (ls)
    (let/cc k
      (letrec
          ((last-non-zero
            (lambda (ls)
              (cond
                [(empty? ls) '()]
                [(zero? (car ls)) (k (last-non-zero (cdr ls)))]
                [else (cons (car ls) (last-non-zero (cdr ls)))]
                ))))

        (last-non-zero ls)))))

(last-non-zero '(0))
(last-non-zero '(1 2 3 4 0))
(last-non-zero '(1 2))
;()
(last-non-zero '(1 2 3 0 4 5))
;(4 5)
(last-non-zero '(1 0 2 3 0 4 5))
;(4 5)
(last-non-zero '(1 2 3 4 5))
;(1 2 3 4 5)

(writeln "----------BRAIN TEASER--------------")
(define-syntax cons$
  (syntax-rules ()
    ((cons$ x y) (cons x (delay y)))))
 
(define car$ car)
 
(define cdr$
  (lambda ($) (force (cdr $))))

(define take$
  (lambda (n $)
    (cond
      ((zero? n) '())
      (else (cons (car$ $) 
              (let ((n- (sub1 n)))
                (cond
                  ((zero? n-) '())
                  (else (take$ n- (cdr$ $))))))))))

(define inf-1s (cons$ 1 inf-1s))

; definitions from book
(define stream-apply-to-both
  (lambda (proc)
    (letrec
        ((str-app
           (lambda (s1 s2)
             (cons$
              (proc (car$ s1) (car$ s2))
              (str-app (cdr$ s1) (cdr$ s2))))))
      str-app)))
(define stream-plus (stream-apply-to-both +))

(define trib$
  (cons$ 0
         (cons$ 1
                (cons$ 1
                       (stream-plus
                        trib$
                        (stream-plus
                         (cdr$ trib$)
                         (cdr$ (cdr$ trib$))))))))
(take$ 10 trib$)
;2
(car$ trib$)
;0
(car$ (cdr$ trib$))
;1
(take$ 7 trib$)
;(0 1 1 2 4 7 13)


#|
(define trib$
  (letrec
      (
       [trib-builder
         (lambda (x)
           (cond
             [(<= x 1) (cons$ 0 (trib-builder (add1 x)))] 
             [(= x 2) (cons$ 1 (trib-builder (add1 x)))]
             [else (cons$ (+ (car trib$)) (trib-builder (add1 x)))]
       )
    (trib-builder 0))
         ])))
|#


#|
(define factorials
  (letrec
      ((stream-builder
         (lambda (x n)
           (cons$ x (stream-builder (* x n) (add1 n))))))
    (stream-builder 1 1)))

(define positive-integers
  (letrec
      ((stream-builder
         (lambda (x)
           (cons$ x (stream-builder (add1 x))))))
    (stream-builder 1)))
  
|#
  
(take$ 10 trib$)
;2
(car$ trib$)
;0
(car$ (cdr$ trib$))
;1
(take$ 7 trib$)
;(0 1 1 2 4 7 13)


  
(writeln "------PART 2--------")
; helper method for lex to calculate debruijn indices
(define debruijn
  (lambda (v s-env)
    (match s-env
      ;[`() (error "Invalid program. Unbound " v)]
      [`() v]
      [`(,a . ,d) #:when (eqv? a v) 0]
      [else
       (let ([debruijn-result (debruijn v (cdr s-env))]) 
             (cond
               [(symbol? debruijn-result) v]
               [else (add1 debruijn-result)]
               )
             )]
       )))

;(lex '(letcc k (k (lambda (x) x))) '())
;'(letcc (app (var 0) (lambda (var 0))))

(define lex
  (lambda (e acc)
    (match e
      [`(zero? ,nexp) `(zero ,(lex nexp acc))]
      [`,num #:when (number? num) `(const ,num)]
      [`(* ,nexp1 ,nexp2) `(mult ,(lex nexp1 acc) ,(lex nexp2 acc))]
      ;[`(sub1 ,nexp1) `(sub1 ,(lex nexp1 acc))]
      
      [`,y #:when (symbol? y) (let ([debruijn-result (debruijn y acc)])
                                (if (symbol? debruijn-result)
                                    debruijn-result
                                    (list 'var (debruijn y acc))))]
      
      
      [`(if ,test, conseq, body) `(if ,(lex test acc)
                                       ,(lex conseq acc)
                                       ,(lex body acc))]
      #;[`(let ((,x ,e)) ,body) `(let ,(lex body acc)
                                 ,(lex e `(,x . ,acc))
                                 )]
      [`(throw ,cexpr ,expr) `(throw ,(lex cexpr acc) ,(lex expr acc))]
      [`(let/cc ,k ,body) `(letcc ,(lex body `(,k . ,acc)))]

      [`(lambda (,x) ,body)
       #:when (symbol? x)
       `(lambda ,(lex body `(,x . ,acc)))]
      [`(,rator ,rand) `(app ,(lex rator acc) ,(lex rand acc))])))


#|
(lex '(* x y) '())
(lex '(lambda (x) (sub1 x)) '())
;(lex '(let ((x 6)) 4) '())
(lex '(let/cc k (* (* (throw k 1) 2) 3)) '())
(lex '(let/cc k (throw k 5)) '())

|#

;(let/cc k (+ k 2) ---> (letcc k (+ k 2))

; PART 3
(writeln "-----PART 3-------")

(define value-of-cps
  (lambda (expr env k)
    (match expr
      [`(const ,expr) (apply-k k expr)]
      [`(mult ,x1 ,x2) (value-of-cps x1 env (outer-mult-k x2 env k))]
      [`(sub1 ,x) (value-of-cps x env (inner-sub1-k k))]
      [`(zero ,x) (value-of-cps x env (zero-continuation-k k))]
      [`(if ,test ,conseq ,alt) (value-of-cps test env (if-continuation-k conseq alt env k))]
      [`(letcc ,body) (value-of-cps body (extend-env k env k) k)]
      [`(throw ,k-exp ,v-exp) (value-of-cps v-exp env (throw-outer-k k-exp env))]
      [`(let ,e ,body) (value-of-cps e env (let-continuation-k body env k))]
      [`(var ,y) (apply-env env y k)]
      [`(lambda ,body) (apply-k k (make-closure body env))]
      [`(app ,rator ,rand) (value-of-cps rator env (application-outer-k rand env k))]
      )))

(define zero-continuation-k
  (lambda (k)
    `(zero-continuation ,k)
      ))

(define inner-mult-k
  (lambda (v2 k^)
    `(inner-mult-k ,v2 ,k^)
    ))

(define outer-mult-k
  (lambda (x2 env k)
    `(outer-mult-k ,x2 ,env ,k)
      ))

(define inner-sub1-k
  (lambda (k^)
    `(inner-sub1-k ,k^)
      ))

(define if-continuation-k
  (lambda (conseq alt env k)
      `(if-continuation-k ,conseq ,alt ,env ,k)
    ))

(define throw-inner-k
  (lambda (v2)
    `(throw-inner-k ,v2)))

(define throw-outer-k
  (lambda (k-exp env)
    `(throw-outer-k ,k-exp ,env)))

(define let-continuation-k
  (lambda (body env k^)
    `(let-continuation-k ,body ,env ,k^)
      ))

(define application-inner-k
  (lambda (v1 k^)
    `(application-inner-k ,v1 ,k^)
    ))

(define application-outer-k
  (lambda (rand env k^)
    `(application-outer-k ,rand ,env ,k^)
    ))

(define empty-env
  (lambda ()
    `(empty-env)))
 
(define empty-k
  (lambda ()
    `(empty-k)))

(define apply-k
  (lambda (k v)
    (match k
      [`(if-continuation-k ,conseq ,alt ,env ,k^) (if v
                                                      (value-of-cps conseq env k^)
                                                      (value-of-cps alt env k^))]
      [`(outer-mult-k ,x2 ,env ,k^) (value-of-cps x2 env
                                                 (inner-mult-k v k^))]
      [`(inner-mult-k ,v2 ,k^) (apply-k k^ (* v v2))]
      [`(zero-continuation ,k^) (apply-k k^ (zero? v))]
      [`(inner-sub1-k ,k^) (apply-k k^ (sub1 v))]
      [`(throw-outer-k ,k-exp ,env) (value-of-cps k-exp env (throw-inner-k v))]
      [`(throw-inner-k ,v2) (apply-k v v2)]
      [`(let-continuation-k ,body ,env ,k^) (let ([a v])
                                              (value-of-cps body (extend-env a env k^) k^))]
      [`(application-inner-k ,v1 ,k^) (apply-closure v1 v k^)]
      [`(application-outer-k ,rand ,env ,k^) (value-of-cps rand env (application-inner-k v k^))]
      [`(empty-k) v]
      )))

(define apply-env
  (lambda (env y k)
    (match env
      [`(extend-env ,arg^ ,env^ ,k^) (if (zero? y)
                                         (apply-k k arg^)
                                         (apply-env env^ (sub1 y) k))]
      [`(empty-env) (error 'value-of "unbound identifier")]
      [else (env y k)]
      )))

(define apply-closure
  (lambda (clos arg k)
    (match clos
      [`(make-closure ,body ,env) (value-of-cps body
                                                (extend-env arg env k) k)]
      )))

(define make-closure
  (lambda (body env)
    `(make-closure ,body ,env)
    ))

(define extend-env
  (lambda (arg^ env^ k^)
    `(extend-env ,arg^ ,env^ ,k^)
    ))


#|    
    (λ (y)
      (cond
        [(eqv? y x) (apply-k k arg)]
        [else (apply-env env y k)]))))
 |#


;(value-of-cps (lex '(lambda (x) (zero? x)) (empty-env)) (empty-env) (empty-k))
;test cases

(check-equal? (value-of-cps '(const 5) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(mult (const 5) (const 5)) (empty-env) (empty-k)) 25)
(check-equal? (value-of-cps '(zero (const 5)) (empty-env) (empty-k)) #f)
(check-equal? (value-of-cps '(sub1 (const 5)) (empty-env) (empty-k)) 4)
(check-equal? (value-of-cps '(sub1 (sub1 (const 5))) (empty-env) (empty-k)) 3)
(check-equal? (value-of-cps '(zero (sub1 (const 6))) (empty-env) (empty-k)) #f)
(check-equal? (value-of-cps '(if (zero (const 5)) (const 3) (mult (const 2) (const 2))) (empty-env) (empty-k)) 4)
(check-equal? (value-of-cps '(if (zero (const 0)) (mult (const 2) (const 2)) (const 3)) (empty-env) (empty-k)) 4)
(check-equal? (value-of-cps '(app (app (lambda (lambda (var 1))) (const 6)) (const 5)) (empty-env) (empty-k)) 6)
(check-equal? (value-of-cps '(app (lambda (app (lambda (var 1)) (const 6))) (const 5)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(app (lambda (const 5)) (const 6)) (empty-env) (empty-k)) 5) 
(check-equal? (value-of-cps '(app (lambda (var 0)) (const 5)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(app (lambda (if (zero (var 0)) (const 4) (const 5))) (const 3)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(let (const 6) (const 4)) (empty-env) (empty-k)) 4)
(check-equal? (value-of-cps '(let (const 5) (var 0)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(mult (const 5) (let (const 5) (var 0))) (empty-env) (empty-k)) 25)
(check-equal? (value-of-cps '(app (if (zero (const 4)) (lambda (var 0)) (lambda (const 5))) (const 3)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(app (if (zero (const 0)) (lambda (var 0)) (lambda (const 5))) (const 3)) (empty-env) (empty-k)) 3)
(check-equal? (value-of-cps '(letcc (const 5)) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(letcc (throw (var 0) (const 5))) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(letcc (throw (var 0) (mult (const 5) (const 5)))) (empty-env) (empty-k)) 25)
(check-equal? (value-of-cps '(letcc (throw (app (lambda (var 0)) (var 0)) (mult (const 5) (const 5)))) (empty-env) (empty-k)) 25)
(check-equal? (value-of-cps '(letcc (sub1 (throw (var 0) (const 5)))) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(letcc (throw (throw (var 0) (const 5)) (const 6))) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(letcc (throw (const 5) (throw (var 0) (const 5)))) (empty-env) (empty-k)) 5)
(check-equal? (value-of-cps '(mult (const 3) (letcc (throw (const 5) (throw (var 0) (const 5))))) (empty-env) (empty-k)) 15)
(check-equal? (value-of-cps '(if (zero (const 5)) (app (lambda (app (var 0) (var 0))) (lambda (app (var 0) (var 0)))) (const 4))
                            (empty-env)
                            (empty-k))
              4)
(check-equal? (value-of-cps '(if (zero (const 0)) (const 4) (app (lambda (app (var 0) (var 0))) (lambda (app (var 0) (var 0)))))
                            (empty-env)
                            (empty-k))
              4)
(check-equal? (value-of-cps '(app (lambda (app (app (var 0) (var 0)) (const 2)))
                                  (lambda
                                      (lambda 
                                          (if (zero (var 0))  
                                              (const 1)
                                              (app (app (var 1) (var 1)) (sub1 (var 0)))))))
                            (empty-env)
                            (empty-k))
              1)


#|
(list 5 (let/cc k (k 5)) 20)
(list 5 (call/cc (λ (k) (k 5))) 20)


(let fac ([n 10])
    (if (zero? n)
        1
        (* n (fac (sub1 n)))))


(call/cc (λ (return)
           (let loop ([n 0])
             (if (= n 7) (return n) (loop (+ n 1))))))
(* 5 (call/cc (λ (k) (* 6 (k 2)))))
|#
#|(let ((a 5)) (* a 5))
((λ (a) (* a 5)) 5) |#