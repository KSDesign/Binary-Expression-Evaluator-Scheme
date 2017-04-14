(module evaluator scheme

  ; some helper functions that should make your code much easier to read
  (define unary-op first)
  (define operand second)
  (define binary-op second)
  (define left first)
  (define right third)
  (define (atomic? v) (not (list? v)))
  (define (unary? expr) (= 2 (length expr)))
  (define (binary? expr) (= 3 (length expr)))

  ; (keyref expr context) -> value, expr
  ; expr: a valid representation of an expression
  ; context: list of pairs: symbol to #t/#f
  ; Return the value of expr with value specified in context.
  ; Else return the expression
  (define keyref
    (λ (expr context)
      (if (dict-has-key? context expr)
          (dict-ref context expr)
          (first (list expr)))))



  ;Check if left and right side of binary equation are atomic
  (define (atomicatomic? expr) (and (atomic? (left expr)) (atomic? (right expr))))
  ;Check if left side is atomic and right side of is a list of binary equation
  (define (atomiclist? expr) (and (atomic? (left expr)) (list? (right expr))))
  ;Check if left side is list and right side of is atomic of binary equation
  (define (listatomic? expr) (and (list? (left expr)) (atomic? (right expr))))
   ;Check if left and right side of binary equation are lists
  (define (listlist? expr) (and (list? (left expr)) (list (right expr))))

  ; (evaluate expr context) -> boolean
  ; expr: a valid representation of an expression
  ; context: list of pairs: symbol to #t/#f
  ; Return the value of expr with values of all variables
  ; that occur in expr specified in context.
  (define evaluate
    (lambda (expr context)
      (cond [(atomic? expr) (keyref expr context)]
            [(binary? expr)
             (cond [(equal? (binary-op expr) 'and)
                 (cond [(atomicatomic? expr) (and (keyref (left expr) context) (keyref (right expr) context))]
                       [(atomiclist? expr) (and (keyref (left expr) context) (evaluate (right expr) context))]
                       [(listatomic? expr) (and (evaluate (left expr) context) (keyref (right expr) context))]
                       [(listlist? expr) (and (evaluate (left expr) context) (evaluate (right expr) context))])]
                   [(equal? (binary-op expr) 'or)
                 (cond [(atomicatomic? expr) (or (keyref (left expr) context) (keyref (right expr) context))]
                       [(atomiclist? expr) (or (keyref (left expr) context) (evaluate (right expr) context))]
                       [(listatomic? expr) (or (evaluate (left expr) context) (keyref (right expr) context))]
                       [(listlist? expr) (or (evaluate (left expr) context) (evaluate (right expr) context))])])]
            [(unary? expr)
             (cond [(equal? (unary-op expr) 'not)
                 (cond [(atomic? (operand expr)) (not (keyref (operand expr) context))]
                       [(list? (operand expr)) (not (evaluate (operand expr) context))])])])))


  ; (simplify expr context) -> valid expression
  ; expr: a valid representation of an expression
  ; context: list of pairs: symbol to #t/#f
  ; Return an expression that is equivalent to expr,
  ; but is simplified as much as possible, according to
  ; the given rules.
  (define simplify
    (lambda (expr context)
      (cond [(atomic? expr) (keyref expr context)]
            [(binary? expr)
             (cond [(equal? (binary-op expr) 'or)
                 (cond [(atomicatomic? expr)
                        (cond [(equal? #t (keyref (left expr) context)) (keyref (left expr) context)]
                              [(equal? #t (keyref (right expr) context)) (keyref (right expr) context)]
                              [(equal? #f (keyref (left expr) context)) (keyref (right expr) context)]
                              [(equal? #f (keyref (right expr) context)) (keyref (left expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(atomiclist? expr)
                        (cond [(equal? #t (keyref (left expr) context)) (keyref (left expr) context)]
                              [(equal? #f (keyref (left expr) context)) (simplify (right expr) context)]
                              [(equal? #t (simplify (right expr) context)) (simplify (right expr) context)]
                              [(equal? #f (simplify (right expr) context)) (keyref (left expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(listatomic? expr)
                        (cond [(equal? #t (keyref (right expr) context)) (keyref (right expr) context)]
                              [(equal? #f (keyref (right expr) context)) (simplify (left expr) 1)]
                              [(equal? #t (simplify (left expr) context)) (simplify (left expr) context)]
                              [(equal? #f (simplify (left expr) context)) (keyref (right expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(listlist? expr)
                        (cond [(equal? #t (simplify (left expr) context)) (simplify (left expr) context)]
                              [(equal? #t (simplify (right expr) context)) (simplify (right expr) context)]
                              [(equal? #f (simplify (left expr) context)) (simplify (right expr) context)]
                              [(equal? #f (simplify (right expr) context)) (simplify (left expr) context)]
                              [(equal? (right expr) (left expr)) (left expr)]
                              [else (list (simplify (left expr) context) (binary-op expr) (simplify (right expr) context))])])]
                   [(equal? (binary-op expr) 'and)
                 (cond [(atomicatomic? expr)
                        (cond [(equal? #t (keyref (left expr) context)) (keyref (right expr) context)]
                              [(equal? #t (keyref (right expr) context)) (keyref (left expr) context)]
                              [(equal? #f (keyref (left expr) context)) (keyref (left expr) context)]
                              [(equal? #f (keyref (right expr) context)) (keyref (right expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(atomiclist? expr)
                        (cond [(equal? #t (keyref (left expr) context)) (simplify (right expr) context)]
                              [(equal? #f (keyref (left expr) context)) (keyref (left expr) context)]
                              [(equal? #t (simplify (right expr) context)) (keyref (left expr) context)]
                              [(equal? #f (simplify (right expr) context)) (simplify (right expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(listatomic? expr)
                        (cond [(equal? #t (keyref (right expr) context)) (simplify (left expr) context)]
                              [(equal? #f (keyref (right expr) context)) (keyref (right expr) context)]
                              [(equal? #t (simplify (left expr) context)) (keyref (right expr) context)]
                              [(equal? #f (simplify (left expr) context)) (simplify (left expr) context)]
                              [else (list (left expr) (binary-op expr) (right expr))])]
                       [(listlist? expr)
                        (cond [(equal? #t (simplify (left expr) context)) (simplify (right expr) context)]
                              [(equal? #t (simplify (right expr) context)) (simplify (left expr) context)]
                              [(equal? #f (simplify (left expr) context)) (simplify (left expr) context)]
                              [(equal? #f (simplify (right expr) context)) (simplify (right expr) context)]
                              [(equal? (right expr) (left expr)) (left expr)]
                              [else (list (simplify (left expr) context) (binary-op expr) (simplify (right expr) context))])])])]
            [(unary? expr)
             (cond [(equal? (unary-op expr) 'not)
                    (cond [(atomic? (operand expr))
                        (cond [(equal? #t (keyref (operand expr) context)) (not (keyref (operand expr) context))]
                              [(equal? #f (keyref (operand expr) context)) (not (keyref (operand expr) context))]
                              [else (list (unary-op expr) (operand expr))])]
                       [(list? (operand expr))
                        (cond [(equal? #t (simplify (operand expr) context)) (not (simplify (operand expr) context))]
                              [(equal? #f (simplify (operand expr) context)) (not (simplify (operand expr) context))]
                              [else (list (unary-op expr) (simplify (operand expr) context))])])])])))


  (provide evaluate simplify)
  )
