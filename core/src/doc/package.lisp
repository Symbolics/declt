;;; package.lisp --- Package documentation

;; Copyright (C) 2010-2013, 2015-2017, 2020 Didier Verna

;; Author: Didier Verna <didier@didierverna.net>

;; This file is part of Declt.

;; Permission to use, copy, modify, and distribute this software for any
;; purpose with or without fee is hereby granted, provided that the above
;; copyright notice and this permission notice appear in all copies.

;; THIS SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
;; WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
;; MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
;; ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
;; WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
;; ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
;; OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


;;; Commentary:



;;; Code:

(in-package :net.didierverna.declt)
(in-readtable :net.didierverna.declt)


;; ==========================================================================
;; Documentation Protocols
;; ==========================================================================

(defmethod type-name ((definition package-definition))
  "Return \"package\"."
  "package")

(defmethod index-command-name ((definition package-definition))
  "Return \"packageindex\"."
  "packageindex")

(defmethod document ((definition package-definition) context &key)
  "Render package DEFINITION's documentation in context."
  (anchor-and-index definition)
  (render-docstring definition)
  (@table ()
    (when-let (source (source-file definition))
      (@tableitem "Source" (reference source)))
    (when-let* ((nicknames (nicknames definition))
		(length (length nicknames)))
      (@tableitem (format nil "Nickname~p" length)
	(if (eq length 1)
	  (format t "@t{~(~A~)}" (escape (first nicknames)))
	  (@itemize-list nicknames :format "@t{~(~A~)}" :key #'escape))))
    (render-references
     (use-definitions definition) "Use List")
    (render-references
     (used-by-definitions definition) "Used By List")
    ;; #### NOTE: classoids and their slots are documented in a singel bloc.
    ;; As a consequence, if a classoid belongs to this package, there's no
    ;; need to also reference (sone of) its slots. On the other hand, we need
    ;; to reference slots for which the classoid is elsewhere (admittedly, and
    ;; for the same reason, only one would suffice). In the case of generic
    ;; functions, methods don't need to be referenced at all methods share the
    ;; same name.
    (flet ((organize-definitions (definitions)
	     (sort (remove-if
		       (lambda (definition)
			 (or (typep definition 'method-definition)
			     (and (typep definition 'slot-definition)
				  (eq (package-definition definition)
				      (package-definition
				       (classoid-definition definition))))))
		       definitions)
		 #'string-lessp ;; #### WARNING: casing policy.
	       :key #'definition-symbol)))
      (render-references (organize-definitions (public-definitions definition))
			 "Public Interface")
      (render-references (organize-definitions (private-definitions definition))
			 "Internals"))))



;; ==========================================================================
;; Package Nodes
;; ==========================================================================

(defun add-packages-node (parent extract context)
  "Add the packages node to PARENT in EXTRACT."
  (when-let (definitions
	     (remove-if-not #'package-definition-p (definitions extract)))
    (let ((packages-node
	    (add-child parent
	      (make-node :name "Packages"
			 :synopsis "The packages documentation"
			 :before-menu-contents (format nil "~
Packages are listed by definition order.")))))
      (dolist (definition definitions)
	#+()(remove-if #'foreignp package-definitions)
	(add-child packages-node
	  (make-node :name (long-title definition)
		     :section-name (format nil "@t{~(~A~)}"
				     (escape (safe-name definition t)))
		     :before-menu-contents
		     (render-to-string (document definition context))))))))

;;; package.lisp ends here
