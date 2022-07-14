(in-package :modus)

(defun variablep(expr)
  (and (symbolp expr) (char= #\? (char (symbol-name expr) 0))))

(defun wildcardp(expr)
  (eq expr '_))

(defun atom-match(pattern expr &optional substituted)
  (cond
    ((variablep pattern)
     (aif (cdr (find pattern substituted :key #'car))
	  (when (equal it expr) (values substituted t))
	  ;;(when (not (car (rassoc expr substituted)))
	  (values (acons pattern expr substituted) t)))
    ((wildcardp pattern) (values substituted t))
    (t (values substituted (eql pattern expr)))))

(defun pattern-match(pattern expr &optional substituted)
  (cond
    ((and (null pattern) (null expr)) (values substituted t))
    ((null pattern) nil)
    ((atom pattern) (atom-match pattern expr substituted))
    ((consp pattern)
     (when (consp expr)
       (multiple-value-bind (subs matchesp) (pattern-match (car pattern) (car expr) substituted)
	 (when matchesp
	   (pattern-match (cdr pattern) (cdr expr) subs)))))
    (t nil)))

(defun matchesp(pattern expr)
  (multiple-value-bind (subs matchesp) (pattern-match pattern expr)
    matchesp))

(defun partialp(pattern expr)
  (matchesp expr pattern))

;;Predicates

(defstruct (predicate (:constructor make-predicate(args body)))
  (args nil :type list)
  (body nil :type list))

(defun extract-variables(expr)
  (remove-duplicates
   (alet ((e expr))
     (cond ((variablep e) (list e))
	   ((consp e) (append (self (car e)) (self (cdr e))))))))

(defun expr-predicate(expr)
  (make-predicate (extract-variables expr) expr))

(defun complete-subs(subs vars)
  (awith (remove-if (lambda (var) (find-if (lambda (bnd) (eq var (car bnd))) subs)) vars)
    (append (mapcar (lambda (var) (cons var (gensym "?"))) it) subs)))

(defun unify-predicates(pred1 pred2 &optional subs)
  (let-be [clashing (intersection (predicate-args pred1) (predicate-args pred2) :test #'eq)
	   clash-substitution (mapcar (lambda (sym) (cons sym (gensym "?"))) clashing)
	   pred2 (predicate-sublis clash-substitution pred2)]
    (mvb (subs succ) (unify-match (predicate-body pred1) (predicate-body pred2) subs)
	 (when succ
	   (values (mapcar (lambda (bnd) (cons (car bnd) (sublis subs (cdr bnd)))) subs) t)))))

(defun predicate-sublis(subs pred) ;Fix this
  (expr-predicate (sublis subs (predicate-body pred) :test (lambda (s1 s2) (and (variablep s2) (eq s1 s2))))))

(defun subunf(pred1 pred2 &optional subs)
  (mvb (subs succ) (unify-predicates pred1 pred2 subs)
       (if succ
	   (predicate-sublis subs pred1))))

;;; Unification
;;; Based on SICP unification

(defun depends-on?(expr var frame)
  (alet ((e expr))
    (cond ((variablep e)
	   (or (equal e var)
	       (aif (assoc e frame)
		    (self (cdr it)))))
	  ((consp e)
	   (or (self (car e))
	       (self (cdr e))))
	  (t nil))))

(defun unify-match(p1 p2 &optional frame)
  (cond ((equal p1 p2) (values frame t))
	((variablep p1) (extend-if-possible p1 p2 frame))
	((variablep p2) (extend-if-possible p2 p1 frame))
	((and (consp p1) (consp p2))
	 (mvb (frame succ) (unify-match (car p1) (car p2) frame)
	      (when succ
		(unify-match (cdr p1) (cdr p2) frame))))
	((or (wildcardp p1) (wildcardp p2)) (values frame t))
	(t nil)))

(defun extend-if-possible(var val frame)
  (acond
    ((assoc var frame) (unify-match (cdr it) val frame))
    ((variablep val)
     (aif (assoc val frame)
	  (unify-match var (cdr it) frame)
	  (values (acons val var frame) t)))
    ((depends-on? val var frame) nil)
    (t (values (acons var val frame) t))))

(defun unify(p1 p2 &optional subs)
  (unify-match p1 p2 subs))

(defun unifyesp(pattern1 pattern2 &optional substitutions)
  (value-second (unify-match pattern1 pattern2 substitutions)))
