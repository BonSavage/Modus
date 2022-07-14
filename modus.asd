(in-package :asdf-user)

(defsystem "Modus"
    :description "Prolog-like language implementation."
    :version "0.8"
    :depends-on ("BonSavage")
    :components ((:file "packages")
		 (:file "pattern-matching" :depends-on ("packages"))
		 (:file "modus" :depends-on ("pattern-matching"))))
