;;; lc.el --- Untyped lambda calculus  -*- lexical-binding: t; -*-

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
;;   let result := (lc-eval nil (app (app const "foo") "bar"))
;;   result = "foo"

;;; Code:

;; Terms

(require 'cl-lib)

(defun lc-eval (ctx expr)
  (pcase expr
    (`(app ,e1 ,e2)
     (let ((f (lc-eval ctx e1))
           (x (lc-eval ctx e2)))
       (pcase f
         (`(lam ,s ,body)
          (lc-eval (cons s ctx) (lc-subst x body)))
         (_
          (error "Attempt to apply non-function")))))
    (`(var ,n)
     (elt ctx n))
    (x x)))


(defun lc-mapvar (f expr)
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

(defun lc-subst (new-expr old-expr)
  (cl-labels
      ((shift (delta expr)
              (lc-mapvar (lambda (var depth)
                         (pcase-let ((`(var ,idx) var))
                           (if (>= idx depth)
                               `(var ,(+ delta idx))
                             `(var ,idx))))
                       expr))

       (subst (var-num new-expr)
              (lc-mapvar (lambda (var depth)
                         (pcase-let ((`(var ,idx) var))
                           (if (= idx (+ var-num depth))
                               (shift depth new-expr)
                             `(var ,idx))))
                       old-expr)))

    (shift -1 (subst 0 (shift 1 new-expr)))))


;; Tests

(ert-deftest lc--test-lambda-is-normal-form ()
  (let ((lam '(lam "x" (var 0))))
    (should (equal lam (lc-eval nil lam)))))

(ert-deftest lc--test-identity ()
  (let ((id '(lam "x" (var 0))))
    (should (equal id (lc-eval nil `(app ,id ,id))))))

(ert-deftest lc--test-const ()
  (let ((const `(lam "x" (lam "y" (var 1)))))
    (should (equal "foo"
                   (lc-eval nil `(app (app ,const "foo") "bar"))))))


(provide 'lc)

;;; lc.el ends here
