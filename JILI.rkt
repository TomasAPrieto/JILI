#lang typed/racket

(require typed/rackunit)
(require racket/format)

#|implemented all new functionality|#

;defining type ExprC
(define-type ExprC (U NumC StrC AppC IdC IfC LamC RecC))
(struct NumC ([n : Real]) #:transparent)
(struct StrC ([s : String]) #:transparent)
(struct IdC ([name : Symbol]) #:transparent)
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)
(struct IfC ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct LamC
  ([params : (Listof Symbol)]
   [param-types : (Listof Type)]
   [body : ExprC]) #:transparent)
(struct RecC ([name : Symbol]
              [args : (Listof Symbol)]
              [types : (Listof Type)]
              [body : ExprC]
              [ret : Type]
              [use : ExprC]) #:transparent)


;defining type Value
(define-type Value (U NumV BoolV StrV CloV PrimOpV))
(struct NumV ([n : Real]) #:transparent)
(struct BoolV ([b : Boolean]) #:transparent)
(struct StrV ([s : String]) #:transparent)
(struct CloV ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimOpV ([o : Symbol]) #:transparent)

; defining type Type
(define-type Type (U NumT StrT BoolT FunT))
(struct NumT () #:transparent)
(struct StrT () #:transparent)
(struct BoolT () #:transparent)
(struct FunT ([args : (Listof Type)] [ret : Type]) #:transparent)


;define binding
(struct Bind ([s : Symbol] [v : (Boxof Value)]) #:transparent)

;define env
(struct Env ([b : (Listof Bind)]) #:transparent)

; define top-env
(define top-env (Env (list (Bind '+ (box (PrimOpV '+)))
                           (Bind '* (box (PrimOpV '*)))
                           (Bind '- (box (PrimOpV '-)))
                           (Bind '/ (box (PrimOpV '/)))
                           (Bind 'true (box (BoolV true)))
                           (Bind 'false (box (BoolV false)))
                           (Bind 'str-eq? (box (PrimOpV 'str-eq?)))
                           (Bind 'num-eq? (box (PrimOpV 'num-eq?)))
                           (Bind '<= (box (PrimOpV '<=)))
                           (Bind 'substring (box (PrimOpV 'substring))))))

;define TBind
(struct TBind ([s : Symbol] [T : Type]) #:transparent)

;define type env
(struct TEnv ([b : (Listof TBind)]) #:transparent)

;define base-tenv
(define base-tenv (TEnv (list (TBind '+ (FunT (list (NumT) (NumT)) (NumT)))
                           (TBind '* (FunT (list (NumT) (NumT)) (NumT)))
                           (TBind '- (FunT (list (NumT) (NumT)) (NumT)))
                           (TBind '/ (FunT (list (NumT) (NumT)) (NumT)))
                           (TBind 'true (BoolT))
                           (TBind 'false (BoolT))
                           (TBind 'str-eq? (FunT (list (StrT) (StrT)) (BoolT)))
                           (TBind 'num-eq? (FunT (list (NumT) (NumT)) (BoolT)))
                           (TBind '<= (FunT (list (NumT) (NumT)) (BoolT)))
                           (TBind 'substring (FunT (list (StrT) (NumT) (NumT)) (StrT))))))


;takes an Sexp and returns a Real
(: top-interp (Sexp -> String))
(define (top-interp [s : Sexp]) : String
  (define parsed-sexp (parse s))
  (type-check parsed-sexp base-tenv)
  (serialize (interp parsed-sexp top-env)))

;interpret ExprC AST returns a number ***from the book- still needs to be altered for JILI
(define (interp [expr : ExprC] [env : Env]) : Value
  (match expr
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    [(IdC n) (lookup n env)]
    [(AppC f a) (define f-value (interp f env))
                (define args-to-values
                  (for/list: : (Listof Value) ([x a]) (interp x env)))
                (match f-value
                  [(PrimOpV s)
                   (cond
                     [(= (length args-to-values) 2)
                      (match* ((first args-to-values) (second args-to-values))
                        [((NumV num1) (NumV num2))
                         #:when
                         (and (member s '(+ - / *))
                              (false? (and (equal? s '/) (= num2 0))))
                         (NumV ((apply-primitive f-value) num1 num2))]
                        [((NumV num1) (NumV num2))
                         #:when (equal? s '<=)
                         (BoolV (<= num1 num2))]
                        [((NumV n1) (NumV n2))
                         #:when (equal? s 'num-eq?)
                         (BoolV (= n1 n2))]
                        [((StrV s1) (StrV s2))
                         #:when (equal? s 'str-eq?)
                         (BoolV (equal? s1 s2))]
                        [(_ _) (error 'interp "JILI Invalid Syntax")])]
                     [(= (length args-to-values) 3)
                      (match* ((first args-to-values) (second args-to-values) (third args-to-values))
                        [((StrV s) (NumV start) (NumV end))
                         (StrV (substring s (cast start Integer) (cast end Integer)))]
                        [(_ _ _) (error 'interp "JILI Invalid Syntax")])]
                     [else (error 'interp "JILI Invalid Syntax")])]
                  [(CloV a b e)
                   (interp b (extend-env (CloV-args f-value) args-to-values e))])]
    [(IfC test then else) (define val (interp test env))
                          (match val
                            [(BoolV f) #:when (false? f) (interp else env)]
                            [(BoolV t) (interp then env)])]
    [(LamC a t b) (CloV a b env)]
    [(RecC n a t b r u) (define new-env (extend-env (list n) (list (StrV "temp")) env))
                        (define c (CloV a b new-env))
                        (set-box! (Bind-v (first (Env-b new-env))) c)
                        (interp u new-env)]))


;accepts an Sexp and parses to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)] ;NumC case

    [(? symbol? s) #:when (false? (member s '(if : = var in rec => ->))) (IdC s)] ;IdC case

    [(? string? s) (StrC s)] ;StrC case

    [(list 'if test then else) (IfC (parse test) (parse then) (parse else))] ;{if Expr Expr Expr}

    [(list 'var (list (list (? symbol? params) ': types '= exprs) ...) 'in body)
     #:when (false? (member params '(if : = var in rec => ->)))
                     (parse (desugar s))]
    [(list 'rec
           (list (? symbol? name) '=
                 (list (list (? symbol? args) ': types) ... ': ret '=> body)) 'in use)
     #:when (and (= (length args) (length types))
                 (false? (member args '(if : = var in rec => ->))))
     (RecC
      name
      (cast args (Listof Symbol))
      (for/list: : (Listof Type) ([type : Sexp (cast types (Listof Sexp))])
        (parse-type type))
      (parse body) (parse-type ret) (parse use))]
    
    [(list (list (? symbol? a) ': t) ... '=> b)
     #:when (and (false? (member a '(if : = var in rec => ->)))
                 (unique? (cast a (Listof Symbol)))
                 (= (length a) (length t)))
                                    (LamC (cast a (Listof Symbol))
                                          (for/list ([ty : Sexp (cast t (Listof Sexp))])
                                            (parse-type ty)) (parse b))] 
    [(list f a ...) #:when (false? (member f '(if : = var in rec => ->)))
                    (AppC (parse f) (for/list ([x (cast a (Listof Sexp))]) (parse x)))]
    [other (error 'parse "JILI Invalid Syntax ~e" other)]))

; accepts a Sexp and parses to a Ty
(define (parse-type [s : Sexp]) : Type
  (match s
    ['num (NumT)]
    ['str (StrT)]
    ['bool (BoolT)]
    [(list a ... '-> b)
     (FunT (for/list ([x : Sexp (cast a (Listof Sexp))]) (parse-type x)) (parse-type b))]
    [_ (error 'parse-type "JILI Invalid type ~e" s)]))

; define type-check, accepts an ExprC and returns its Type
(define (type-check [e : ExprC] [tenv : TEnv]) : Type
  (match e
    [(NumC n) (NumT)]
    [(StrC s) (StrT)]
    [(IdC s) (tenv-lookup s tenv)]
    [(AppC f a) (define-values (ft at)
                  (values (type-check f tenv)
                          (for/list: : (Listof Type) ([x : ExprC a])
                            (type-check x tenv))))
                (match ft
                  [(FunT a ret) #:when (equal? at a) ret]
                  [(NumT) (NumT)]
                  [(BoolT) (BoolT)]
                  [(StrT) #:when (equal? ft (first at)) (StrT)]
                  [_ (error 'type-check "JILI type-check error ~e" ft)])]
    [(IfC test then else)
     (define-values
       (test-type then-type else-type)
       (values (type-check test tenv)
               (type-check then tenv)
               (type-check else tenv)))
     (if (and (equal? test-type (BoolT)) (equal? then-type else-type))
         then-type
         (error 'type-check "JILI IfC Invalid Type ~e" e))]
    [(LamC a t b) (define ret
                    (type-check b (extend-tenv a t tenv)))
                  (FunT t ret)]
    [(RecC n a t b r u) (define new-env (extend-tenv (list n) (list r) tenv))
                        (define check-u (type-check u new-env))
                        (if (equal? r (type-check b (extend-tenv a t new-env)))
                            r
                            (error 'type-check "JILI RecC Invalid Type"))]))

;takes in a value input and returns a string
(define (serialize [output : Value]) : String
  (match output
    [(NumV n) (~v n)]
    [(BoolV b) (if b "true" "false")]
    [(StrV s) (~v s)]
    [(CloV a b e) "#<procedure>"]
    [(PrimOpV o) "#<primop>"]))

; define lookup, takes a symbol and environment and looks for the binding in the environment
(define (lookup [s : Symbol] [env : Env]) : Value
  (match (Env-b env)
    ['() (error 'lookup "JILI Name not found")]
    [(cons f r) (if (symbol=? s (Bind-s f)) (unbox (Bind-v f)) (lookup s (Env r)))]))

;define tenv-lookup : a lookup for types 
(define (tenv-lookup [s : Symbol] [env : TEnv]) : Type
  (match (TEnv-b env)
    ['() (error 'tenv-lookup "JILI Name not found ~e" s)]
    [(cons f r) (if (symbol=? s (TBind-s f)) (TBind-T f) (tenv-lookup s (TEnv r)))]))

; define extend-env, binds list of symbols to list of values in new environment
(define (extend-env [sym : (Listof Symbol)] [to : (Listof Value)] [env : Env]) : Env
  (cond
    [(equal? (length sym) (length to)) (Env (append (for/list: : (Listof Bind) ([s sym]
                                                                        [val to])
                                              (Bind s (box val))) (Env-b env)))]
    [else (error 'extend-env "JILI Mismatching number of arguments")]))

; define extend-tenv
(define (extend-tenv [sym : (Listof Symbol)] [to : (Listof Type)] [tenv : TEnv]) : TEnv
  (cond
    [(equal? (length sym) (length to)) (TEnv (append (for/list: : (Listof TBind) ([s sym]
                                                                        [val to])
                                              (TBind s val)) (TEnv-b tenv)))]
    [else (error 'extend-tenv "JILI Mismatching number of arguments")]))

;takes a Symbol and returns a function which takes two Reals and returns a Real
(define (apply-primitive [primop : PrimOpV]) : (-> Real Real Real)
  (match primop
    [(PrimOpV '+) +]
    [(PrimOpV '*) *]
    [(PrimOpV '-) -]
    [(PrimOpV '/) /]))

;define desugars the var form into the => form
(define (desugar [s : Sexp]) : Sexp
  (match s
    [(list 'var
           (list (list (? symbol? params) ': types '= exprs) ...)
           'in body)
     (define stypes (cast types (Listof Sexp)))
     (define sexps (cast params (Listof Sexp)))
     (if (false? (or (member '=> sexps)
                     (member 'if sexps)
                     (member 'var sexps)
                     (member 'in sexps)
                     (member ': sexps)
                     (member '-> sexps)
                     (member 'rec sexps)
                     (member '= sexps)))
         (cons (append (for/list: : (Listof Sexp) ([sexp : Sexp sexps] [type : Sexp stypes])
                         (cons sexp (list ': type))) (list '=> body))
               (cast exprs (Listof Sexp)))
         (error 'desugar "JILI Invalid Syntax"))]
    [_ (error 'desugar "JILI Invalid Syntax ~e" s)]))

;define unique?, takes a list of symbol and checks if unique
(define (unique? [a : (Listof Symbol)]) : Boolean
  (match a
    ['() #t]
    [(cons a b) (if (false? (member a b)) (unique? b) #f)]))



;----------------------------------------------------------------------------------------
;########################################################################################
;##################################### [TEST CASES] #####################################
;########################################################################################
;----------------------------------------------------------------------------------------



; unique?
(check-equal? (unique? (list 'a 'a 'b)) #f)

; type-check
(check-equal? (type-check (NumC 1) base-tenv) (NumT))
(check-equal? (type-check (StrC "a") base-tenv) (StrT))
(check-equal? (type-check (IdC 'true) base-tenv) (BoolT))
(check-equal? (type-check (AppC (IdC 'true) '()) base-tenv) (BoolT))
(check-equal? (type-check (AppC (StrC "a") (list (StrC "b"))) base-tenv) (StrT))
(check-equal? (type-check (AppC (IdC '+) (list (NumC 1) (NumC 2))) base-tenv) (NumT))
(check-equal? (type-check (IfC (IdC 'true) (NumC 1) (NumC 2)) base-tenv) (NumT))
(check-exn (regexp
            (regexp-quote "type-check: JILI IfC Invalid Type"
                          '(IfC (IdC 'true) (NumC 1) (StrC "a"))))
            (lambda () (type-check (IfC (IdC 'true) (NumC 1) (StrC "a")) base-tenv)))
(check-equal? (type-check
               (LamC (list 'x 'y)
                     (list (NumT) (NumT)) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                          base-tenv)
              (FunT (list (NumT) (NumT)) (NumT)))

(check-exn (regexp (regexp-quote "type-check: JILI RecC Invalid Type"))
           (lambda () (type-check (parse '(rec (a = ((c : num) : num => "abc")) in 13)) base-tenv)))

(check-exn (regexp (regexp-quote "tenv-lookup: JILI Name not found" 'random))
           (lambda () (type-check (IdC 'random) base-tenv)))

(check-exn (regexp
            (regexp-quote "type-check: JILI type-check error"))
            (lambda () (type-check (parse '{"abc" 9}) base-tenv)))

; extend-tenv
(check-exn (regexp (regexp-quote "extend-tenv: JILI Mismatching number of arguments")) 
           (lambda () (type-check (LamC (list 'x) '() (NumC 1)) base-tenv)))

; parse-type
(check-exn (regexp (regexp-quote "parse-type: JILI Invalid type" 'nottype))
           (lambda () (parse-type '{[x : nottype] => {+ x 1}})))
(check-equal? (parse-type 'num) (NumT))
(check-equal? (parse-type 'str) (StrT))
(check-equal? (parse-type 'bool) (BoolT))
(check-equal? (parse-type '{num str -> bool})
              (FunT (list (NumT) (StrT)) (BoolT)))

; top-interp
(check-equal? (top-interp "hi") "\"hi\"")

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax")) 
           (lambda () (top-interp '{a a => 3})))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax")) 
           (lambda () (top-interp '{/ 1 {- 3 3}})))


(check-exn (regexp (regexp-quote "match: no matching clause for (NumV 3)")) 
           (lambda () (top-interp '(((=> 3)) 4 5))))

(check-equal? (top-interp '{substring "hello" 0 4}) "\"hell\"")

(check-equal?
 (top-interp
  '{rec {square-helper = {[n : num] : num =>
                                    {if {<= n 0} 0 {+ n {square-helper {- n 2}}}}}}
     in
     {var {[square : {num -> num}  =
                   {[n : num] => {square-helper {- {* 2 n} 1}}}]}
          in
          {square 13}}}) "169")

; interp
(define test-env (Env (list (Bind 'a (box (StrV "hello"))))))
(check-equal? (interp (IdC 'a) test-env) (StrV "hello"))
(check-equal? (interp (StrC "hello") top-env) (StrV "hello"))
(check-equal? (interp (NumC 1) top-env) (NumV 1))
(check-equal? (interp (IdC 'true) top-env) (BoolV true))
(check-equal? (interp (AppC (IdC '+) (list (NumC 1) (NumC 2))) top-env) (NumV 3))
(check-equal?
 (interp
  (AppC
   (LamC (list 'x) (list (NumT)) (AppC (IdC '*) (list (IdC 'x) (NumC 2))))
   (list (NumC 1)))
  top-env)
 (NumV 2))
(check-equal?
 (interp
  (AppC (IdC '<=) (list (NumC 1) (NumC 2)))
  top-env)
 (BoolV true))
(check-equal?
 (interp
  (AppC (IdC 'str-eq?) (list (StrC "hello") (StrC "hello")))
  top-env)
 (BoolV true))
(check-equal? (interp (IfC (AppC (IdC 'str-eq?) (list (StrC "ur") (StrC "mom")))
                           (AppC (IdC '-) (list (NumC 5) (NumC 2)))
                           (AppC (IdC '/) (list (NumC 4) (NumC 2)))) top-env) (NumV 2))
(check-equal? (interp (IfC (AppC (IdC 'str-eq?) (list (StrC "mom") (StrC "mom")))
                           (AppC (IdC '-) (list (NumC 5) (NumC 2)))
                           (AppC (IdC '/) (list (NumC 3) (NumC 2)))) top-env) (NumV 3))
(check-equal? (interp (AppC (IdC 'num-eq?) (list (NumC 1) (NumC 1))) top-env)
              (BoolV true))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax")) 
           (lambda () (interp (AppC (IdC '+) (list (StrC "a") (StrC "a") (StrC "a"))) top-env)))

(check-exn (regexp (regexp-quote "interp: JILI Invalid Syntax")) 
           (lambda () (interp (AppC (IdC '+) (list (StrC "a"))) top-env)))

(check-exn (regexp (regexp-quote "type-check: JILI type-check error")) 
           (lambda () (top-interp '{+ + +})))

(check-exn (regexp (regexp-quote "type-check: JILI type-check error")) 
           (lambda () (top-interp '{<= <= <=})))

(check-exn (regexp (regexp-quote "type-check: JILI type-check error")) 
           (lambda () (top-interp '{+ + + +})))

(check-exn (regexp (regexp-quote "type-check: JILI type-check error")) 
           (lambda () (top-interp '{+ + + + +})))
 

; parse
(check-equal? (parse '{+ 1 2}) (AppC (IdC '+) (list (NumC 1) (NumC 2))))

(check-equal?
 (parse '{* {+ 1 2} 3})
 (AppC (IdC '*) (list (AppC (IdC '+) (list (NumC 1) (NumC 2))) (NumC 3))))

(check-equal? (parse '{- 4 1}) (AppC (IdC '-) (list (NumC 4) (NumC 1))))

(check-equal? (parse '{/ 4 2}) (AppC (IdC '/) (list (NumC 4) (NumC 2))))

(check-equal?
 (parse '{+ {f {h x}} {i 9}})
 (AppC (IdC '+)
       (list (AppC (IdC 'f) (list (AppC (IdC 'h) (list (IdC 'x)))))
             (AppC (IdC 'i) (list (NumC 9))))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax")) 
           (lambda () (parse '{})))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax"))
           (lambda () (parse '{})))

(check-equal? (parse '{f 1 2 3}) (AppC (IdC 'f) (list (NumC 1) (NumC 2) (NumC 3))))

(check-equal? (parse '{test-func x y}) (AppC (IdC 'test-func) (list (IdC 'x) (IdC 'y))))

;(check-equal? (parse '{test-no-args}) (AppC (IdC 'test-no-args) '()))

(check-equal? (parse '{{f 4} {[x : num] => 44}}) (AppC (AppC (IdC 'f) (list (NumC 4)))
                                   (list (LamC '(x) (list (NumT)) (NumC 44)))))

(check-equal? (parse '{[a : str] => {+ a 1}})
              (LamC (list 'a) (list (StrT)) (AppC (IdC '+) (list (IdC 'a) (NumC 1)))))

(check-equal? (parse '{if a b c}) (IfC (IdC 'a) (IdC 'b) (IdC 'c)))
(check-equal? (parse 1) (NumC 1))
(check-equal? (parse "s") (StrC "s"))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{var {[z : num = {+ 9 14}] [y : num = 98]} in {+ z y}})
              (AppC (LamC '(z y) (list (NumT) (NumT))
                          (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse '{rec {f = {[a : num] [b : num] : num => {+ a b}}} in {f 1 2}})
              (RecC
               'f
               '(a b)
               (list (NumT) (NumT))
               (AppC (IdC '+) (list (IdC 'a) (IdC 'b)))
               (NumT)
               (AppC (IdC 'f) (list (NumC 1) (NumC 2)))))

(check-exn (regexp (regexp-quote "desugar: JILI Invalid Syntax")) 
           (lambda () (parse '(var ((=> : num = "")) in "World"))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax '(var ((=> = "")) in \"World\")"))
           (lambda () (parse '(var ((=> = "")) in "World"))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax '(var ((in = "")) in \"World\")")) 
           (lambda () (parse '(var ((in = "")) in "World"))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax '(var ((if = "")) in \"World\")")) 
           (lambda () (parse '(var ((if = "")) in "World"))))

(check-exn (regexp (regexp-quote "parse: JILI Invalid Syntax '(var ((var = "")) in \"World\")")) 
           (lambda () (parse '(var ((var = "")) in "World"))))

; serialize
(check-equal? (serialize (NumV 3)) "3")  ;NumV
(check-equal? (serialize (BoolV false)) "false")   ;BoolV
(check-equal? (serialize (BoolV true)) "true")   ;BoolV
(check-equal? (serialize (StrV "test")) "\"test\"") ;StrV
(check-equal? (serialize (CloV (list 'b 'c) (IdC 'a) test-env)) "#<procedure>") ;CloV
(check-equal? (serialize (PrimOpV '+)) "#<primop>")  ;PrimOpV

;extend-env
(check-equal? (extend-env (list 'a 'b 'c) (list (NumV 1) (NumV 2) (NumV 3)) top-env)
              (Env (append (list (Bind 'a (box (NumV 1)))
                         (Bind 'b (box (NumV 2)))
                         (Bind 'c (box (NumV 3)))) (Env-b top-env))))

(check-exn (regexp (regexp-quote "type-check: JILI type-check error")) 
           (lambda () (top-interp '((=> 9) 17))))

(check-exn (regexp (regexp-quote "extend-env: JILI Mismatching number of arguments")) 
           (lambda () (extend-env '(a) '() top-env)))

; desugar
(check-equal? (desugar '{var {[z : num = {+ 9 14}] [y : num = 98]} in {+ z y}}) 
              '(([z : num] [y : num] => {+ z y})(+ 9 14) 98))

(check-exn (regexp (regexp-quote "desugar: JILI Invalid Syntax"))
           (lambda () (desugar 's)))

; lookup
(check-exn (regexp (regexp-quote "lookup: JILI Name not found")) 
           (lambda () (interp (IdC 'x) top-env)))