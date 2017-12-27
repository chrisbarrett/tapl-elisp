;;; untyped-arith.el --- Implementation of untyped arithmetic expression evaluation.  -*- lexical-binding: t; -*-
;;; Commentary:
;;; Code:

;; Terms

(defun untyped-arith-true ()
  'true)

(defun untyped-arith-false ()
  'false)

(defun untyped-arith-if (e1 e2 e3)
  `(if ,e1 ,e2 ,e3))

(defun untyped-arith-zero ()
  'zero)

(defun untyped-arith-succ (e)
  `(succ ,e))

(defun untyped-arith-pred (e)
  `(pred ,e))

(defun untyped-arith-is-zero (e)
  `(is-zero ,e))

;; Evaluator

(defun untyped-arith-eval (expr)
  (pcase expr
    ('true expr)
    ('false expr)
    ('zero expr)

    (`(if ,p ,e1 ,e2)
     (pcase (untyped-arith-eval p)
       ('false (untyped-arith-eval e2))
       (_ (untyped-arith-eval e1))))

    (`(is-zero ,e)
     (pcase (untyped-arith-eval e)
       ('zero
        (untyped-arith-true))
       (_
        (untyped-arith-false))))

    (`(succ ,e)
     (untyped-arith-succ (untyped-arith-eval e)))

    (`(pred ,e)
     (pcase (untyped-arith-eval e)
       ('zero (untyped-arith-zero))
       (`(succ ,e) e)
       (e
        (untyped-arith-pred e))))
    (_
     (error "Evaluation error"))))

;; Tests

(ert-deftest untyped-arith--eval--if-true ()
  (let ((expr (untyped-arith-if (untyped-arith-true)
                   (untyped-arith-zero)
                   (untyped-arith-false))))
    (should (equal (untyped-arith-zero) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--if-false ()
  (let ((expr (untyped-arith-if (untyped-arith-false)
                   (untyped-arith-true)
                   (untyped-arith-zero))))
    (should (equal (untyped-arith-zero) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--if-step ()
  (let ((expr (untyped-arith-if (untyped-arith-is-zero (untyped-arith-zero))
                   (untyped-arith-true)
                   (untyped-arith-false))))
    (should (equal (untyped-arith-true) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--is-zero--zero ()
  (let ((expr (untyped-arith-is-zero (untyped-arith-zero))))
    (should (equal (untyped-arith-true) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--is-zero--succ ()
  (let ((expr (untyped-arith-is-zero (untyped-arith-succ (untyped-arith-zero)))))
    (should (equal (untyped-arith-false) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--is-zero--if ()
  (let ((expr (untyped-arith-is-zero (untyped-arith-if (untyped-arith-true)
                             (untyped-arith-zero)
                             (untyped-arith-false)))))
    (should (equal (untyped-arith-true) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--succ ()
  (let ((expr (untyped-arith-succ (untyped-arith-if (untyped-arith-true)
                          (untyped-arith-zero)
                          (untyped-arith-succ (untyped-arith-zero))))))
    (should (equal (untyped-arith-succ (untyped-arith-zero)) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--pred-zero ()
  (let ((expr (untyped-arith-pred (untyped-arith-zero))))
    (should (equal (untyped-arith-zero) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--pred-numeric ()
  (let ((expr (untyped-arith-pred (untyped-arith-succ (untyped-arith-succ (untyped-arith-zero))))))
    (should (equal (untyped-arith-succ (untyped-arith-zero))
                   (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval--pred-inner ()
  (let ((expr (untyped-arith-pred (untyped-arith-if (untyped-arith-true)
                          (untyped-arith-true)
                          (untyped-arith-false)))))
    (should (equal (untyped-arith-pred (untyped-arith-true)) (untyped-arith-eval expr)))))

(ert-deftest untyped-arith--eval-reduces-to-normal-form ()
  (let ((expr (untyped-arith-pred
               (untyped-arith-pred
                (untyped-arith-succ (untyped-arith-if (untyped-arith-is-zero (untyped-arith-false))
                            (untyped-arith-pred (untyped-arith-true))
                            (untyped-arith-zero)))))))

    (should (equal (untyped-arith-zero) (untyped-arith-eval expr)))))

(provide 'untyped-arith)

;;; untyped-arith.el ends here
