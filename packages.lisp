
(defpackage :modus
  (:use :cl :cl-user)
  (:export :evaluate :*known* :*rules* :rule)
  (:shadow :cl :evaluate :*rules* :*known* :pattern-match :matchesp))
