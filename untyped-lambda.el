;;; untyped-lambda.el --- Untyped lambda calculus  -*- lexical-binding: t; -*-

;;; Commentary:

;; The language is defined as follows:
;;
;;
;;
;;   term :=
;;
;;     (lam BINDING-SYMBOL TERM)   a lambda term
;;
;;     (var N)                     a variable reference (as a De Bruijn index).
;;                                 See: https://en.wikipedia.org/wiki/De_Bruijn_index
;;
;;     (app TERM TERM)             a function application
;;
;;     OTHERWISE                   an uninterpreted value literal.
;;
;;
;;    value :=
;;
;;      (lam BINDING-SYMBOL TERM)  a lambda value
;;
;;      OTHERWISE                  some other uninterpreted value
;;
;; Sketch:
;;
;;   let const := (lam "" (lam "" (var 1)))
;;   let result := (untyped-lambda-eval nil (app (app const "foo") "bar"))
;;   result = "foo"

;;; Code:

;; Terms

(require 'cl-lib)

(defun untyped-lambda-eval (ctx expr)
  (pcase expr
    (`(app ,e1 ,e2)
     (let ((f (untyped-lambda-eval ctx e1))
           (x (untyped-lambda-eval ctx e2)))
       (pcase f
         (`(lam ,s ,body)
          (untyped-lambda-eval (cons s ctx) (untyped-lambda-subst x body)))
         (_
          (error "Attempt to apply non-function")))))
    (`(var ,n)
     (elt ctx n))
    (x x)))


(defun untyped-lambda-mapvar (f expr)
  "Map over EXPR, applying F to each var in the expression.

F is a binary function taking a var and the current lambda binder
depth."
  (cl-labels
      ((walk (depth expr)
             (pcase expr
               ((and v `(var ,_))
                (funcall f v depth))

               (`(lam ,s ,body)
                `(lam ,s ,(walk (1+ depth) body)))

               (`(app ,e1 ,e2)
                `(app ,(walk depth e1) ,(walk depth e2)))

               (x x))))

    (walk 0 expr)))

(defun untyped-lambda-subst (new-expr old-expr)
  (cl-labels
      ((shift (delta expr)
              (untyped-lambda-mapvar (lambda (var depth)
                         (pcase-let ((`(var ,idx) var))
                           (if (>= idx depth)
                               `(var ,(+ delta idx))
                             `(var ,idx))))
                       expr))

       (subst (var-num new-expr)
              (untyped-lambda-mapvar (lambda (var depth)
                         (pcase-let ((`(var ,idx) var))
                           (if (= idx (+ var-num depth))
                               (shift depth new-expr)
                             `(var ,idx))))
                       old-expr)))

    (shift -1 (subst 0 (shift 1 new-expr)))))


;; Tests

(ert-deftest untyped-lambda--test-lambda-is-normal-form ()
  (let ((lam '(lam "x" (var 0))))
    (should (equal lam (untyped-lambda-eval nil lam)))))

(ert-deftest untyped-lambda--test-identity ()
  (let ((id '(lam "x" (var 0))))
    (should (equal id (untyped-lambda-eval nil `(app ,id ,id))))))

(ert-deftest untyped-lambda--test-const ()
  (let ((const `(lam "x" (lam "y" (var 1)))))
    (should (equal "foo"
                   (untyped-lambda-eval nil `(app (app ,const "foo") "bar"))))))


(provide 'untyped-lambda)

;;; untyped-lambda.el ends here
