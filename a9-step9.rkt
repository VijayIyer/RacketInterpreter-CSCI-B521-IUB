;; (let ((f (lambda (f)
;;   	      (lambda (n)
;; 	        (if (zero? n) 
;; 		    1
;; 	            (* n ((f f) (sub1 n))))))))
;;   (* (letcc k ((f f) (throw k ((f f) 4)))) 5))

; This file becomes interp.pc

(define-registers *exp* *env* *k* *clos^* *arg* *y* *v*)
(define-program-counter pc)

(define-union expr
  (const cexp)
  (var n)
  (if test conseq alt)
  (mult nexp1 nexp2)
  (sub1 nexp)
  (zero nexp)
  (letcc body)
  (throw kexp vexp)
  (let exp body)              
  (lambda body)
  (app rator rand))

(define-union kt
  (zero-continuation-k k)
  (inner-mult-k v2 k^)
  (outer-mult-k x2 env k)
  (inner-sub1-k k^)
  (if-continuation-k conseq alt env k)
  (throw-inner-k v2)
  (throw-outer-k k-exp env)
  (let-continuation-k body env k^)
  (application-inner-k v1 k^)
  (application-outer-k rand env k^)
  (empty-k dismount)
  )
(define-union clos
  (make-closure body env)
  )
(define-union envr
  (empty-env)
  (extend-env arg^ env^ k^))


(define-label apply-k
    (union-case *k* kt
      [(if-continuation-k conseq alt env k^) (if *v*
                                                 (begin (set! *k* k^)
                                                        (set! *exp* conseq)
                                                        (set! *env* env)
                                                        (set! pc value-of-cps))
                                                 (begin (set! *k* k^)
                                                        (set! *exp* alt)
                                                        (set! *env* env)
                                                        (set! pc value-of-cps)))]
      [(outer-mult-k x2 env k^) (begin (set! *k* (kt_inner-mult-k *v* k^))
                                       (set! *exp* x2)
                                       (set! *env* env)
                                       (set! pc value-of-cps))]
      [(inner-mult-k v2 k^) (begin (set! *k* k^)
                                   (set! *v* (* *v* v2))
                                   (set! pc apply-k))]
      [(zero-continuation-k k^) (begin (set! *k* k^)
                                       (set! *v* (zero? *v*))
                                       (set! pc apply-k))]
      [(inner-sub1-k k^) (begin (set! *k* k^)
                                (set! *v* (sub1 *v*))
                                (set! pc apply-k))]
      [(throw-outer-k k-exp env) (begin (set! *k* (kt_throw-inner-k *v*))
                                        (set! *exp* k-exp)
                                        (set! *env* env)
                                        (set! pc value-of-cps))]
      [(throw-inner-k v2) (begin (set! *k* *v*)
                                 (set! *v* v2)
                                 (set! pc apply-k))]
      [(let-continuation-k body env k^) (begin (set! *k* k^)
                                               (set! *exp* body)
                                               (set! *env* (envr_extend-env *v* env *k*))
                                               (set! pc value-of-cps))]
      [(application-inner-k v1 k^) (begin (set! *k* k^)
                                          (set! *clos^* v1)
                                          (set! *arg* *v*)
                                          (set! pc apply-closure))]
      [(application-outer-k rand env k^) (begin (set! *k* (kt_application-inner-k *v* k^))
                                                (set! *exp* rand)
                                                (set! *env* env)
                                                (set! pc value-of-cps))]
      [(empty-k dismount) (dismount-trampoline dismount)]
      ))

(define-label apply-closure
    (union-case *clos^* clos
      [(make-closure body env) (begin (set! *env* (envr_extend-env *arg* env *k*))
                                      (set! *k* *k*)
                                      (set! *exp* body)
                                      (set! pc value-of-cps))]
      ))

(define-label apply-env
    (union-case *env* envr
      [(extend-env arg^ env^ k^) (if (zero? *y*)
                                     (begin (set! *k* *k*)
                                            (set! *v* arg^)
                                       (set! pc apply-k))
                                     (begin (set! *env* env^)
                                            (set! *y* (sub1 *y*))
                                            (set! *k* *k*)
                                            (set! pc apply-env)))]
      [(empty-env) (error 'value-of "unbound identifier")]
      ))

(define-label value-of-cps
    (union-case *exp* expr
      [(const e) (begin
                     (set! *k* *k*)
                     (set! *v* e)
                     (set! pc apply-k))]
      [(mult x1 x2) (begin (set! *exp* x1)
                           (set! *env* *env*)
                           (set! *k* (kt_outer-mult-k x2 *env* *k*))
                           (set! pc value-of-cps))]
      [(sub1 x) (begin (set! *k* (kt_inner-sub1-k *k*))
                       (set! *exp* x)
                       (set! *env* *env*)
                       (set! pc value-of-cps))]
      [(zero x) (begin (set! *exp* x)
                       (set! *env* *env*)
                       (set! *k* (kt_zero-continuation-k *k*))
                       (set! pc value-of-cps))]
      [(if test conseq alt) (begin (set! *exp* test)
                                   (set! *env* *env*)
                                   (set! *k* (kt_if-continuation-k conseq alt *env* *k*))
                              (set! pc value-of-cps))]
      [(letcc body) (begin (set! *exp* body)
                           (set! *env* (envr_extend-env *k* *env* *k*))
                           (set! *k* *k*)
                           (set! pc value-of-cps))]
      [(throw k-exp v-exp) (begin (set! *exp* v-exp)
                                  (set! *env* *env*)
                                  (set! *k* (kt_throw-outer-k k-exp *env*))
                                  (set! pc value-of-cps))]
      [(let e body) (begin (set! *exp* e)
                           (set! *env* *env*)
                           (set! *k* (kt_let-continuation-k body *env* *k*))
                           (set! pc value-of-cps))]
      [(var y) (begin (set! *env* *env*)
                      (set! *y* y)
                      (set! *k* *k*)
                      (set! pc apply-env))]
      [(lambda body) (begin (set! *k* *k*)
                            (set! *v* (clos_make-closure body *env*))
                            (set! pc apply-k))]
      [(app rator rand) (begin (set! *exp* rator)
                               (set! *env* *env*)
                               (set! *k* (kt_application-outer-k rand *env* *k*))
                               (set! pc value-of-cps))]
      ))


(define-label main 
    (begin (set! *exp* (expr_let 
                         (expr_lambda
                          (expr_lambda 
                           (expr_if
                            (expr_zero (expr_var 0))
                            (expr_const 1)
                            (expr_mult (expr_var 0) (expr_app (expr_app (expr_var 1) (expr_var 1)) (expr_sub1 (expr_var 0)))))))
                         (expr_mult
                          (expr_letcc
                           (expr_app
                            (expr_app (expr_var 1) (expr_var 1))
                            (expr_throw (expr_var 0) (expr_app (expr_app (expr_var 1) (expr_var 1)) (expr_const 4)))))
                          (expr_const 5))))
            (set! *env* (envr_empty-env))
           (set! pc value-of-cps)
           (mount-trampoline kt_empty-k *k* pc)
           (printf "Factorial of 5: ~s\n" *v*)))

