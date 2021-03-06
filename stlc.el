;;; stlc.el --- Simply-typed lambda calculus  -*- lexical-binding: t; -*-

;;; Commentary:

;; Syntactic forms:
;;
;;
;;   term :=
;;     (λ (NAME : TYPE) TERM)      a lambda term
;;     (TERM TERM)                 a function application
;;     (if T1 T2 T3)               an if expression
;;     SYMBOL                      a variable reference
;;     OTHERWISE                   an uninterpreted value literal.

;;   types :=
;;     Bool
;;     Nat
;;     (T₁ -> T₂)

;;   value :=
;;     true                    boolean literals
;;     false
;;     0,1,...,n               natural numbers
;;     (λ (NAME : TYPE) TERM)  a lambda value
;;     OTHERWISE               some other uninterpreted value

;;   contexts
;;     ∅                      empty context
;;     Γ, x:T                 term variable binding

;;; Code:

(require 'seq)
(require 'subr-x)

;;; Contexts

;; A context is represented as an alist of binding name to type.

(defun stlc-add-binding (ctx name type)
  (cons (cons name type) ctx))

(defun stlc-lookup-type (ctx name)
  (alist-get name ctx))

;; Type-checking

(defun stlc-unifies-p (t1 t2)
  (or (equal t1 t2)
      (equal t1 'diverge)
      (equal t2 'diverge)))

(defun stlc-typecheck (ctx term)
  (let (errors)
    (cl-labels
        ((unify
          (expected actual &optional message)
          (if (stlc-unifies-p expected actual)
              expected
            (let ((err (list :error :type-error
                             :message (or message (format "Type error: Expected \
a value of type %s, but got %s" expected actual))
                             :expected expected
                             :actual actual)))
              (setq errors (cons err errors))
              'diverge)))

         (unbound-var-error
          (name)
          (let ((err (list :error :unbound-var
                           :message (format "Unbound identifier: %s" name)
                           :name name)))
            (setq errors (cons err errors))
            'diverge))

         (invalid-term-error
          (term)
          (let ((err (list :error :invalid-term
                           :message (format "Invald term: %s" term)
                           :term term)))
            (setq errors (cons err errors))
            'diverge))

         (application-type-error
          (actual arg-type)
          (unless (or (equal actual 'diverge)
                      (equal arg-type 'diverge))
            (let ((err (list :error :application-type-error
                             :message (format "Expected a function of taking a \
value of type %s, but got a value of type %s" arg-type actual)
                             :arg-type arg-type
                             :actual actual)))
              (setq errors (cons err errors))))
          'diverge)

         (typecheck
          (ctx term)
          (pcase term

            ;; Typing Rule: Literals
            ;;
            ;;   false : Bool
            ;;   true : Bool
            ;;   0,1,...,n : Nat

            ('true 'Bool)
            ('false 'Bool)
            ((and n (pred numberp) (guard (>= n 0)))
             n ; silence unused variable warning
             'Nat)


            ;; Typing Rule: T-IF
            ;;
            ;;    Γ ⊢ e₁ : Bool    Γ ⊢ e₂ : T    Γ ⊢ e₃ : T
            ;;    ——————————————————————————————————————————
            ;;         Γ ⊢ (if e₁ e₂ e₃) : T

            (`(if ,p ,e1 ,e2)
             (unify 'Bool (typecheck ctx p)
                    "The first expression in an if expression \
must be of type Bool.")
             (let ((t1 (typecheck ctx e1))
                   (t2 (typecheck ctx e2)))
               (unify t1 t2
                      "Both branches of an if expression must \
evaluate to the same type.")))


            ;; Typing Rule: T-VAR
            ;;
            ;;    x:T ∈ Γ
            ;;    ———————
            ;;    Γ ⊢ x:T

            ((and name (pred symbolp))
             (or (stlc-lookup-type ctx name)
                 (unbound-var-error name)))


            ;; Typing Rule: T-ABS
            ;;
            ;;       Γ, x:T₁ ⊢ e:T₂
            ;;    —————————————————————————
            ;;    Γ ⊢ (λ (x : T₁) e) : T₁ → T₂

            (`(λ (,name : ,ty) ,body)
             (let* ((ctx (stlc-add-binding ctx name ty))
                    (result-ty (typecheck ctx body)))
               `(,ty -> ,result-ty)))

            ;; Typing Rule: T-APP
            ;;
            ;;    Γ ⊢ t₁ : A → B     Γ ⊢ t₂ : A
            ;;    ——————————————————————————————
            ;;            Γ ⊢ (t₁ t₂) : B

            (`(,e1 ,e2)
             (let ((t1 (typecheck ctx e1))
                   (t2 (typecheck ctx e2)))
               (pcase t1
                 (`(,ty-argument -> ,ty-result)
                  (unify ty-argument t2)
                  ty-result)
                 (_
                  (application-type-error t1 t2)))))

            (expr
             (invalid-term-error expr)))))

      (let ((result (typecheck ctx term)))
        (if (and result (null errors))
            result
          `(:errors ,(nreverse errors)))))))



;;; Context Tests

(ert-deftest stlc-test--add-binding ()
  (let ((ctx nil))
    (should-not (stlc-lookup-type ctx 'foo))
    (setq ctx (stlc-add-binding ctx 'foo 'Bool))
    (should (equal 'Bool (stlc-lookup-type ctx 'foo)))))


;;; Type-checking tests

(ert-deftest stlc-test--boolean-literals ()
  (should (equal 'Bool (stlc-typecheck nil 'true)))
  (should (equal 'Bool (stlc-typecheck nil 'false))))

(ert-deftest stlc-test--nat-literals ()
  (should-not (equal 'Nat (stlc-typecheck nil -1)))
  (should (equal 'Nat (stlc-typecheck nil 0)))
  (should (equal 'Nat (stlc-typecheck nil 1))))


(ert-deftest stlc-test--if-expression ()
  (should (equal 'Nat (stlc-typecheck nil '(if true 0 1))))
  (should (equal 'Bool (stlc-typecheck nil '(if true true false)))))

(ert-deftest stlc-test--if-expression--not-bool ()
  (let* ((result (stlc-typecheck nil '(if 0 0 0)))
         (errs (plist-get result :errors)))
    (should (equal 1 (length errs)))
    (should (equal :type-error (plist-get (car errs) :error)))))

(ert-deftest stlc-test--if-expression--different-types ()
  (let* ((result (stlc-typecheck nil '(if true true 0)))
         (errs (plist-get result :errors)))
    (should (equal 1 (length errs)))
    (should (equal :type-error (plist-get (car errs) :error)))))


(ert-deftest stlc-test--var-reference ()
  (should-not (equal 'Nat (stlc-typecheck nil 'foo)))
  (should (equal 'Nat (stlc-typecheck '((foo . Nat)) 'foo))))


(ert-deftest stlc-test--lambda ()
  (should-not (equal '(Nat -> Nat) (stlc-typecheck nil '(λ (foo : Nat) true))))
  (should (equal '(Nat -> Nat) (stlc-typecheck nil '(λ (foo : Nat) foo)))))


(ert-deftest stlc-test--apply ()
  (should (equal 'Nat (stlc-typecheck nil `((λ (foo : Nat) foo) 0)))))

(ert-deftest stlc-test--apply-from-ctx ()
  (should (equal 'Nat (stlc-typecheck '((identity . (Nat -> Nat)))
                                      '(identity 0)))))

(ert-deftest stlc-test--apply-type-error ()
  (let* ((result (stlc-typecheck '((f . (Bool -> Nat)))
                                 '(f 0)))
         (errs (plist-get result :errors)))
    (should (equal 1 (length errs)))
    (should (equal :type-error (plist-get (car errs) :error)))))

(ert-deftest stlc-test--apply-nonfunction-error ()
  (let* ((result (stlc-typecheck nil '(0 0)))
         (errs (plist-get result :errors)))
    (should (equal 1 (length errs)))
    (should (equal :application-type-error (plist-get (car errs) :error)))))

(ert-deftest stlc-test--apply-unbound-function-error ()
  (let* ((result (stlc-typecheck nil '(identity 0)))
         (errs (plist-get result :errors)))
    (should (equal 1 (length errs)))
    (should (equal :unbound-var (plist-get (car errs) :error)))))


(ert-deftest stlc-test--shadowing ()
  (let ((ctx '((x . Nat)))
        (program '((λ (x : Bool) x) true)))
    (should (equal 'Bool (stlc-typecheck ctx program)))))


(ert-deftest stlc-test--program ()
  (let ((ctx '((not . (Bool -> Bool))
               (+ . (Nat -> (Nat -> Nat)))
               (identity . (Nat -> Nat))
               (x . Bool)
               (const . (Nat -> (Nat -> Nat)))))

        (program '((λ (x : Nat) ((+ x) 1))
                   ((if (not x) identity (const 0))
                    1))))
    (should (equal 'Nat (stlc-typecheck ctx program)))))

(provide 'stlc)

;;; stlc.el ends here
