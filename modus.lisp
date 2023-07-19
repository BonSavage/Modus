;;;; Modus: Prolog-like language interpreter
;;;; 09.07.2023
;;;; Maxim "BonSavage" Kirillov
;;;; Todo: efficient compiler

(in-package :modus)

(defparameter *known* nil)
(defparameter *rules* nil)

(defstruct (rule (:constructor make-rule(prerequisite consequence)))
  (prerequisite nil :type predicate)
  (consequence nil :type predicate))

(defmacro rule(prerequisite consequence)
  `(make-rule (expr-predicate ',prerequisite)
	      (expr-predicate ',consequence)))

(defmacro all((&rest args) prerequisite consequence)
  (awith (mapcar (lambda (arg) (cons arg (gensym "?"))) args)
    `(rule ,(sublis it prerequisite)
	   ,(sublis it consequence))))


;;Experimental cashing
(defvar *cash* nil)

(defmacro cash-block((key) &body forms)
  (alexandria:with-gensyms ()
    `(aif (assoc ,key *cash*)
	  it
	  (awith (multiple-value-list (progn ,@forms))
	    (push (first it) *cash*)
	    (values-list it)))))

(defmacro cash-context((&rest args) &body forms)
  `(let ((*cash* nil))
     ,@forms))

;;Debug

(defun tracer(sym f)
  (lambda (&rest args)
    (if (find :untrace args)
	(setf (symbol-function sym) f)
	(progn
	  (mvb (subs succ) (apply f args)
	       (when succ
		 (format t "Trace ~a ~a => ~a ~%" sym args subs))
	       (values subs succ))))))

(defmacro trace-inference(f)
  (psetf (symbol-function f) (tracer f (symbol-function f))))

(defmacro with-subs(name form &body forms)
  (awith (gensym)
    `(mvb (,name ,it) ,form
	  (when ,it
	    (values (progn ,@forms) t)))))

;;Evaluator

(defvar *sweeped* nil)
(defvar *deepness* 0)
(defvar *sweeped-rules* nil)

(defun extend-bindings(bnds1 bnds2)
  (append bnds1 bnds2))

(defun bindings-list(&rest args)
  (apply #'list args))

(defun update-bindings(update-data bindings)
  (mapcar (lambda (bnd) (cons (car bnd) (sublis update-data (cdr bnd)))) bindings))

(defun autoupdate(bindings)
  (mapcar (lambda (bnd) (cons (car bnd) (sublis bindings (cdr bnd)))) bindings))

(defun eval-and-iter(operands subs)
  (if (null operands)
      (values (bindings-list subs) t)
      (mvb (new-subs succ) (eval-pattern (predicate-sublis subs (car operands)))
	   (when succ
	     (aif (mappend (lambda (sub) (eval-and-iter (cdr operands) (extend-bindings sub (update-bindings sub subs))))
			   new-subs)
		  (values it t))))))

(defun eval-or-iter(operands subs &optional any-success)
  (aif (mappend #'eval-pattern operands)
       (values it t)))

(defun eval-and(body)
  (eval-and-iter (mapcar #'expr-predicate body) nil))

(defun eval-or(body)
  (eval-or-iter (mapcar #'expr-predicate body) nil))

(defun eval-none(pattern)
  (mvb (bnds succ) (eval-pattern (expr-predicate pattern))
       (unless (or bnds succ)
	 (values (bindings-list nil) t))))
  
(defun eval-pattern(pattern)
  (cond ((sweepedp pattern) 
	 nil)
	((= *deepness* 30) (error "Modus: it looks like program entered infinite recursion. Evaluation aborted due to recursion became too big.~&Last pattern is:~& ~a" pattern))
	(t
	 (let-be [*sweeped* (cons pattern *sweeped*)
		  *deepness* (1+ *deepness*)]
	   (if (atom (predicate-body pattern))
	       (rule-inference pattern)
	       (destructuring-bind (op &rest args) (predicate-body pattern)
		 (case op
		   (and (with-subs subs (eval-and args)
			  subs))
		   (or (with-subs subs (eval-or args)
			 subs))
		   (none (apply #'eval-none args))
		   (lisp-value (apply (car args) (cdr args)))
		   (t (with-subs subs (rule-inference pattern)
			subs)))))))))

(defun find-known(pattern)
  (awith (filtering-map (lambda (known)
			  (with-subs sub (unify-predicates* pattern (expr-predicate known))
			    (or sub (list nil))))
			*known*)
    (when it
      (values it t))))

(defun unify-predicates*(pred1 pred2 &optional subs)
  (with-subs subs (unify-predicates pred1 pred2 subs)
    (intersection subs (predicate-args pred1) :test (lambda (bnd arg) (eq arg (car bnd))))))

(defun sweepedp(pattern)
  (find pattern *sweeped*
	:test
	(lambda (pred swpd)
	  (and (eql (first (predicate-body pred)) (first (predicate-body swpd)))
	       (partialp (predicate-body pred) (predicate-body swpd))))))


;; Inference itself
(defun filter-rules(pattern)
  (filtering-map (lambda (rule) (with-subs subs (unify-predicates* (rule-consequence rule) pattern)
				  (cons subs (make-rule (predicate-sublis subs (rule-prerequisite rule))
							(predicate-sublis subs (rule-consequence rule))))))
		 (remove-if (lambda (rule) (not (eql (first (predicate-body (rule-consequence rule)))
						     (first (predicate-body pattern)))))
			    *rules*)))

(defun rules-bindings(pattern filtered-rules)
  (mappend (lambda (pair &aux (subed (predicate-sublis (car pair) (rule-prerequisite (cdr pair)))))
	     (let-be [*sweeped-rules* (cons pair *sweeped-rules*)]
	       (with-subs it (eval-pattern subed)
		 (or (mapcar (lambda (subs) (unify-predicates*
					     pattern
					     (predicate-sublis (extend-bindings (car pair) subs) (rule-consequence (cdr pair)))))
			     it)
		     (list (bindings-list nil))))))
	   filtered-rules))

(defun rule-inference(pattern)
  (cond
    ((eq pattern t)
     (values (bindings-list nil) t))
    ((null pattern)
     nil)
    (t
     (aif (append
	   (with-subs subs (find-known pattern)
	     (or subs (bindings-list nil)))
	   (let-be [rules (filter-rules pattern)]
	     (aif (rules-bindings pattern rules)
		  (values (or it (bindings-list nil)) t))))
	  (values it t)))))

(defun evaluate(expr)
  (eval-pattern (expr-predicate expr)))
