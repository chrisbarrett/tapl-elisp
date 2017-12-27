;;; type.el --- POC type-checker for Elisp.  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Chris Barrett

;; Author: Chris Barrett <chris@walrus.cool>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'subr-x)

(defconst type--global-table (make-hash-table)
  "Lookup table for globally bound identifiers.")

(defun type (ident ty)
  (puthash ident ty type--global-table))

(defun type--error-unbound-ident (ident)
  (list :error 'unbound-ident :ident ident))

(defun type-lookup (ident env)
  (or (alist-get ident env)
      (gethash ident type--global-table)))

(defun type--error-param-count (expected actual)
  (list :error 'param-count :expected expected :actual actual))

(defun type--error-type-mismatch (expected actual)
  (list :error 'type-mismatch :expected expected :actual actual))

(defun type--symbol-type (sym env)
  (pcase sym
    ('t 'true)
    ('() 'false)
    (x
     (type-lookup x env))))

(defun type-check (expr &optional env)
  "Infer the type of expression EXPR.

ENV is a bindings environment, represented by a list of cons
cells of the form `(SYMBOL . BINDING-ATTRS)'.

Functions are represented as a cons of `(PARAM-TYPES . RESULT)'.

All other types are those given by `type-of'."
  (let ((errors))
    (cl-labels ((go (expr env)
                    (let ((ty (type-of expr)))
                      (pcase ty
                        ('symbol
                         (if-let* ((ty (type--symbol-type expr env)))
                             ty
                           (push (type--error-unbound-ident expr) errors)
                           'void))

                        ('vector
                         (let ((ty (type--unify-types (seq-map (lambda (e) (go e env)) expr))))
                           (type--type-app 'vector ty)))

                        ('integer
                         (if (<= 0 expr)
                             'nat
                           'integer))

                        ('cons
                         (pcase expr

                           ;; Differentiate various quoted symbols from quoted lists.

                           (`(quote ,'nil)
                            'false)
                           (`(quote ,'t)
                            'true)
                           ((and `(quote ,s) (guard (symbolp s)))
                            s ; suppress unused binding warning
                            'symbol)
                           ((and `(quote ,es) (guard (consp es)))
                            (let ((ty (type--unify-types (seq-map (lambda (e) (go e env)) es))))
                              (type--type-app 'list ty)))
                           (`(quote ,e)
                            (list :quote (type-of e)))


                           ;; The PROGN family of special forms.

                           (`(progn . ,body)
                            (go (car (reverse body)) env))

                           (`(prog1 ,x . ,_)
                            (go x env))
                           (`(prog1)
                            (push (type--error-param-count 1 0) errors)
                            'void)

                           (`(prog2 ,_ ,x . ,_)
                            (go x env))
                           (`(prog2 . ,forms)
                            (push (type--error-param-count 2 (length forms)) errors)
                            'void)

                           ;; Control flow

                           (`(if ,_ ,then . ,else)
                            (type--unify (go then env) (go (car (reverse else)) env)))
                           (`(if . ,forms)

                            (push (type--error-param-count 3 (length forms)) errors)
                            'void)

                           (`(when ,_ . ,forms)
                            (go (car (reverse forms)) env))
                           (`(when . ,forms)
                            (push (type--error-param-count 2 (length forms)) errors)
                            'void)

                           (`(unless ,_ . ,forms)
                            (go (car (reverse forms)) env))
                           (`(unless . ,forms)

                            (push (type--error-param-count 2 (length forms)) errors)
                            'void)

                           (`(cond . ,forms)
                            (let ((results
                                   (seq-map (lambda (it)
                                              (go (car (reverse (cdr it))) env))
                                            forms)))
                              (type--unify-types results)))

                           ;; TODO: Lambda

                           (`(lambda ,params . ,body)
                            (let ((env (append (type--parse-parameter-list params) env)))
                              (go body env)))

                           ;; TODO: defun

                           ;; Function application

                           ((and `(,f . ,args)
                                 (guard (symbolp f)))
                            (if-let* ((ty (type--apply env f args)))
                                ty
                              (let ((arg-types (type--arg-types args)))
                                ;; TODO: Infer return type
                                (push (type--error-type-mismatch (cons arg-types 'uninferred) ty) errors)
                                'void)))

                           (_
                            (error "Catastrophic type-checking failure"))))

                        (_
                         ty)))))

      (list :type (go expr env)
            :errors errors))))

(defun type--parse-parameter-list (parameters)
  (seq-map (lambda (p) (cons p (type--binding-attrs)))
           parameters))

(cl-defun type--binding-attrs (&key type optional)
  (list :type type :optional optional))

(type-check '(lambda (x) x))

;; TODO: Check arguments

(defun type--apply (env f _args)
  (cdr (type-lookup f env)))

(defun type--arg-types (args)
  (seq-map (lambda (_) 'void) args))

(defun type--type-app (e1 e2)
  (list e1 e2))


;; Subsumption rules are currently basic:
;;
;; 1. Any type is subsumed for itself.
;; 2. Any type can be subsumed by 'any.
;; 3. Any integer can be widened to a float.
;; 4. False and true can be subsumed for bool.

(defconst type--subsumption-rules
  '((nat . integer)
    (integer . float)
    (true . bool)
    (false . bool))
  "A mapping from subtypes to the next supertype, used to construct the subtyping lattice.")

(defun type--supertype-heirarchy (ty)
  (cl-labels ((go (ty)
                  (if-let* ((parent (alist-get ty type--subsumption-rules)))
                      (cons ty (go parent))
                    (list ty 'any))))
    (go ty)))

(defun type--unify (t1 t2)
  (let ((xs (type--supertype-heirarchy t1))
        (ys (type--supertype-heirarchy t2)))
    (car (seq-intersection xs ys))))

(defun type--unify-types (xs)
  (if (null xs)
      'any
    (cl-reduce #'type--unify xs)))

(defun type--subtype-p (t1 t-upper-bound)
  (seq-contains (type--supertype-heirarchy t1) t-upper-bound))


;; Tests

(defun should-infer-type (result expected-type)
  (let ((actual-type (plist-get result :type))
        (errors (plist-get result :errors)))
    (should (equal expected-type actual-type))
    (should (null errors))))

(defun should-have-error (result expected-error)
  (let ((actual-type (plist-get result :type))
        (errors (plist-get result :errors)))
    (should (equal 'void actual-type))
    (should (seq-contains errors expected-error))))

(ert-deftest type-type-of-unbound-ident-is-error ()
  (should-have-error (type-check 'hello) (type--error-unbound-ident 'hello)))

(ert-deftest type-function-application ()
  (let ((env '((foo . (() . integer))
               (bar . ((nat nat) . bool)))))
    (should-infer-type (type-check '(foo) env) 'integer)
    (should-infer-type (type-check '(bar 1 2) env) 'bool)))

(ert-deftest type-nil-is-false ()
  (should-infer-type (type-check nil) 'false)
  (should-infer-type (type-check ()) 'false)
  (should-infer-type (type-check '()) 'false))

(ert-deftest type-t-is-true ()
  (should-infer-type (type-check t) 'true))

(ert-deftest type-true-and-false-subsume-to-bool ()
  (should (equal 'bool (type--unify 'false 'true)))
  (should (equal 'bool (type--unify 'true 'false))))

(ert-deftest type-nat-literal ()
  (should-infer-type (type-check 0) 'nat)
  (should-infer-type (type-check 1) 'nat))

(ert-deftest type-int-literal ()
  (should-infer-type (type-check -1) 'integer))

(ert-deftest type-float-literal ()
  (should-infer-type (type-check 1.2) 'float))

(ert-deftest type-int-and-float-subsume-to-float ()
  (should (equal 'float (type--unify 'float 'integer)))
  (should (equal 'float (type--unify 'integer 'float))))

(ert-deftest type-string-literal ()
  (should-infer-type (type-check "") 'string))

(ert-deftest type-empty-vector-is-vec-of-any ()
  (should-infer-type (type-check []) '(vector any)))

(ert-deftest type-singleton-vector ()
  (should-infer-type (type-check [1]) '(vector nat)))

(ert-deftest type-vector-inner-expressions ()
  (should-infer-type (type-check [1 2]) '(vector nat)))

(ert-deftest type-vector-type-subsumption ()
  (should-infer-type (type-check [1.0]) '(vector float))
  (should-infer-type (type-check [1 2.2]) '(vector float))
  (should-infer-type (type-check [1 "hello"]) '(vector any)))

(ert-deftest type-if-same-type ()
  (should-infer-type (type-check '(if t 1 2)) 'nat)
  (should-infer-type (type-check '(if t 1 "hello" 1)) 'nat))

(ert-deftest type-if-subsumption ()
  (should-infer-type (type-check '(if t 1.0 2)) 'float)
  (should-infer-type (type-check '(if t 1 1 "hello")) 'any)
  (should-infer-type (type-check '(if t nil t)) 'bool))

(ert-deftest type-when-single-body-form ()
  (should-infer-type (type-check '(when t 12)) 'nat))

(ert-deftest type-when-multiple-body-forms ()
  (should-infer-type (type-check '(when t 2 1.0 )) 'float)
  (should-infer-type (type-check '(when t 1 "hello")) 'string)
  (should-infer-type (type-check '(when t nil t)) 'true))

(ert-deftest type-cond-single-case ()
  (should-infer-type (type-check '(cond (t 1)))
                     'nat))

(ert-deftest type-cond-subsumption ()
  (should-infer-type (type-check '(cond (t nil)
                                    (t t)))
                     'bool))

(ert-deftest type-resolve-binding-type-from-environment ()
  (let ((env '((hello . number))))
    (should-infer-type (type-check 'hello env)
                       'number)))

(ert-deftest type-symbols ()
  ;; Note that this symbol must be double-quoted, or it is considered a binding
  ;; reference in the target language.
  (should-infer-type (type-check (quote 'hello)) 'symbol))

(ert-deftest type-singleton-list ()
  (should-infer-type (type-check (quote '(1))) '(list nat)))

(ert-deftest type-list-with-multiple-subexpressions ()
  (should-infer-type (type-check (quote '(1 2))) '(list nat)))

(ert-deftest type-list-subsumption ()
  (should-infer-type (type-check (quote '(1 2.2))) '(list float))
  (should-infer-type (type-check (quote '(1 "hello"))) '(list any))
  (should-infer-type (type-check (quote '(nil t))) '(list bool)))

(ert-deftest type-test-type-heirarchy ()
  (should (equal (type--supertype-heirarchy 'true)
                 '(true bool any))))

(ert-deftest type-test-subtyping ()
  (should (type--subtype-p 'integer 'float))
  (should-not (type--subtype-p 'float 'integer))
  (should (type--subtype-p 'true 'bool)))

(ert-deftest type-test-subtyping-transitive ()
  (should (type--subtype-p 'nat 'float))
  (should (type--subtype-p 'nat 'any))
  (should (type--subtype-p 'true 'any)))

(provide 'type)

;;; type.el ends here
