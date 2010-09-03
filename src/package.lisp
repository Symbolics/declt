;;; package.lisp --- Package documentation

;; Copyright (C) 2010 Didier Verna

;; Author:        Didier Verna <didier@lrde.epita.fr>
;; Maintainer:    Didier Verna <didier@lrde.epita.fr>
;; Created:       Wed Sep  1 16:04:00 2010
;; Last Revision: Wed Sep  1 17:44:46 2010

;; This file is part of Declt.

;; Declt is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License version 3,
;; as published by the Free Software Foundation.

;; Declt is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


;;; Commentary:


;;; Code:

(in-package :com.dvlsoft.declt)


;; ==========================================================================
;; Utilities
;; ==========================================================================

;; We need to protect against read-time errors. Let's just hope that nothing
;; fancy occurs in IN-PACKAGE or DEFPACKAGE.
(defun safe-read (stream)
  "Read once from STREAM protecting against errors."
  (handler-case (read stream nil :eof)
    (error ())))

(defun file-packages (file)
  "Return the list of all packages involved in FILE."
  (with-open-file (stream file :direction :input)
    (loop :for form := (safe-read stream) :then (safe-read stream)
	  :until (eq form :eof)
	  :if (and (consp form)
		   (eq (car form) 'defpackage))
	  :collect (find-package (cadr form)))))

;; #### FIXME: see how to handle shadowed symbols (not sure what happens with
;; the home package).
(defun external-symbols (package &aux external-symbols)
  "Return the list of symbols external to PACKAGE that need documenting."
  (do-external-symbols (symbol package)
    (when (and (eq (symbol-package symbol) package)
	       (symbol-needs-rendering symbol))
      (push symbol external-symbols)))
  (sort external-symbols #'string-lessp))

;; #### FIXME: see how to handle shadowed symbols (not sure what happens with
;; the home package).
(defun internal-symbols
    (package &aux (external-symbols (external-symbols package))
		  internal-symbols)
  "Return the list of symbols internal to PACKAGE that need documenting."
  (do-symbols (symbol package)
    (when (and (not (member symbol external-symbols))
	       (eq (symbol-package symbol) package)
	       (symbol-needs-rendering symbol))
      (push symbol internal-symbols)))
  (sort internal-symbols #'string-lessp))



;; ==========================================================================
;; Rendering Protocols
;; ==========================================================================

;; -----------------
;; Indexing protocol
;; -----------------

(defmethod index (stream (package package))
  (format stream "@packageindex{~A}@c~%"
    (string-downcase (package-name package))))


;; --------------------
;; Itemization protocol
;; --------------------

(defmethod itemize (stream (package package))
  (write-string "package" stream))


;; ---------------------
;; Tableization protocol
;; ---------------------

(defmethod tableize (stream (package package) relative-to)
  "Describe PACKAGE's components."
  (when (package-nicknames package)
    (format stream "@item Nicknames~%~A~%"
      (list-to-string
       (mapcar (lambda (nickname)
		 (format nil "@t{~A}" (string-downcase nickname)))
	       (package-nicknames package)))))
  (when (package-use-list package)
    (format stream "@item Use List~%~A~%"
      (list-to-string
       (mapcar (lambda (package)
		 (format nil "@t{~A}" (string-downcase
				       (package-name package))))
	       (package-use-list package))))))



;; ==========================================================================
;; Package Nodes
;; ==========================================================================

(defun add-packages-node
    (node system
     &aux (files
	   (cons (asdf:system-definition-pathname system)
		 (mapcar #'asdf:component-pathname
			 (collect-components (asdf:module-components system)
					     'asdf:cl-source-file))))
	  (packages-node
	   (add-child node (make-node :name "Packages"
				      :synopsis "The system's packages"
				      :before-menu-contents (format nil "~
Packages are listed by definition order."))))
	  (packages (remove-duplicates (mapcan #'file-packages files))))
  "Add SYSTEM's packages node to NODE."
  (dolist (package packages)
    (let ((package-node
	   (add-child packages-node
		      (make-node :name (package-name package)
				 :section-name (format nil "@t{~A}"
						 (string-downcase
						  (package-name package)))
				 :before-menu-contents
				 (with-output-to-string (str)
				   (tableize str package nil)))))
	  (external-symbols (external-symbols package))
	  (internal-symbols (internal-symbols package)))
      (when external-symbols
	(add-child package-node
		   (make-node
		    :name (format nil "@t{~A} External Symbols"
			    (string-downcase (package-name package)))
		    :section-name "External Symbols"
		    :before-menu-contents
		    "Symbols are listed by lexicographic order."
		    :after-menu-contents
		    (with-output-to-string (str)
		      (dolist (symbol external-symbols)
			(render-symbol str symbol))))))
      (when internal-symbols
	(add-child package-node
		   (make-node
		    :name (format nil "@t{~A} Internal Symbols"
			    (string-downcase (package-name package)))
		    :section-name "Internal Symbols"
		    :before-menu-contents
		    "Symbols are listed by lexicographic order."
		    :after-menu-contents
		    (with-output-to-string (str)
		      (dolist (symbol internal-symbols)
			(render-symbol str symbol)))))))))


;;; package.lisp ends here