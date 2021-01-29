;;; asdf.lisp --- ASDF items documentation

;; Copyright (C) 2010-2013, 2015-2017, 2019, 2020 Didier Verna

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
;; Utilities
;; ==========================================================================

(defun render-packages-references (packages)
  "Render a list of PACKAGES references."
  (render-references packages "Packages"))



;; ==========================================================================
;; Components
;; ==========================================================================

;; #### NOTE: a simpler route to this is to use ASDF:COMPONENT-FIND-PATH.
;; The merit of this approach, however, is to stay at the definitions level
;; and not access the underlying objects.
(defmethod safe-name ((definition component-definition) &optional qualified)
  "Reveal component DEFINITION's name, possibly QUALIFIED.
A QUALIFIED component's name is of the form \"path/to/component\", each
element being the name of a component's parent."
  (if (and qualified (parent-definition definition))
    (concatenate 'string (safe-name (parent-definition definition) t)
		 "/"
		 (call-next-method definition))
    (call-next-method definition)))

(defmethod index ((definition component-definition))
  "Render component DEFINITION's indexing command."
  (format t "@~Aindex{~A}@c~%"
    (etypecase definition
      ;; #### WARNING: the order is important!
      (system-definition "system")
      (module-definition "module")
      (lisp-file-definition "lispfile")
      (c-file-definition "cfile")
      (java-file-definition "javafile")
      (html-file-definition "htmlfile")
      (doc-file-definition "docfile")
      (static-file-definition "staticfile")
      (source-file-definition "sourcefile")
      (file-definition "otherfile"))
    (escape (safe-name definition t))))

(defmethod reference ((definition component-definition))
  "Render component DEFINITION's reference."
  (@ref (anchor-name definition) (safe-name definition))
  (format t " (~A)~%" (type-name definition)))

;; #### FIXME: dependencies should be represented as potentially foreign
;; definitions.
(defgeneric render-dependency (dependency-def component relative-to)
  (:documentation "Render COMPONENT's DEPENDENCY-DEF RELATIVE-TO.
Dependencies are referenced only if they are RELATIVE-TO the system being
documented. Otherwise, they are just listed.")
  (:method (simple-component-name component relative-to
	    &aux (dependency
		  (resolve-dependency-name component simple-component-name)))
    "Render COMPONENT's SIMPLE-COMPONENT-NAME dependency RELATIVE-TO."
    (if (sub-component-p dependency relative-to)
	(reference dependency)
	(format t "@t{~(~A}~)" (escape simple-component-name))))
  ;; #### NOTE: this is where I'd like more advanced pattern matching
  ;; capabilities.
  (:method ((dependency-def list) component relative-to)
    "Render COMPONENT's DEPENDENCY-DEF (a list) RELATIVE-TO."
    (cond ((eq (car dependency-def) :feature)
	   (render-dependency (caddr dependency-def) component relative-to)
	   (format t " (for feature @t{~(~A}~))"
	     (escape (cadr dependency-def))))
	  ((eq (car dependency-def) :version)
	   (render-dependency (cadr dependency-def) component relative-to)
	   (format t " (at least version @t{~(~A}~))"
	     (escape (caddr dependency-def))))
	  ((eq (car dependency-def) :require)
	   (format t "required module @t{~(~A}~)"
		   (escape (cadr dependency-def))))
	  (t
	   (warn "Invalid ASDF dependency.")
	   (format t "@t{~(~A}~)"
	     (escape (princ-to-string dependency-def)))))))

(defun render-dependencies (dependencies component relative-to
			    &optional (prefix "")
			    &aux (length (length dependencies)))
  "Render COMPONENT's DEPENDENCIES RELATIVE-TO.
Optionally PREFIX the title."
  (@tableitem (format nil "~ADependenc~@p" prefix length)
    (if (eq length 1)
	(render-dependency (first dependencies) component relative-to)
	(@itemize-list dependencies
	  :renderer (lambda (dependency)
		      (render-dependency dependency component
					 relative-to))))))

(defmethod document :around
    ((component-definition component-definition) extract &key)
  "Anchor, index and document EXTRACT's COMPONENT-DEFINITION.
Documentation is done in a @table environment."
  (anchor-and-index component-definition)
  (@table () (call-next-method)))

(defmethod document ((definition component-definition) extract
		     &key
		     &aux (relative-to (location extract)))
  "Render ASDF component DEFINITION's documentation in EXTRACT."
  (when-let (description (description definition))
    (@tableitem "Description"
      (render-text description)
      (fresh-line)))
  (when-let (long-description (long-description definition))
    (@tableitem "Long Description"
      (render-text long-description)
      (fresh-line)))
  ;; #### FIXME: why is it not a @tableitem? Or the other way around?
  (format t "~@[@item Version~%~
		  ~A~%~]"
	  (escape (version-string definition)))
  (when-let (if-feature (if-feature definition))
    (@tableitem "If Feature"
      (format t "@t{~(~A}~)" (escape if-feature))))
  (when-let (dependencies
	     (when (typep definition 'system-definition) ;; Yuck!
	       (system-defsystem-depends-on (system definition))))
    (render-dependencies
     dependencies (component definition) relative-to "Defsystem "))
  (when-let
      (dependencies (component-sideway-dependencies (component definition)))
    (render-dependencies dependencies (component definition) relative-to))
  (when-let (parent (parent definition))
    (@tableitem "Parent" (reference parent)))
  (cond ((typep definition 'system-definition) ;; Yuck!
	 ;; #### WARNING: the system file is not an ASDF component per-se, so
	 ;; I need to fake a reference to a CL-SOURCE-FILE. This is done by
	 ;; reproducing the effect of REFERENCE-COMPONENT.
	 (let ((system (system definition)))
	   (when (system-source-file system)
	     (@tableitem "Source"
	       (let ((system-base-name (escape (system-base-name system))))
		 (format t "@ref{go to the ~A file, , @t{~(~A}~)} (file)~%"
		   (escape-anchor system-base-name)
		   (escape-label system-base-name)))))
	   (when (hyperlinksp extract)
	     (let ((system-source-directory
		     (escape (system-source-directory system))))
	       (@tableitem "Directory"
		 (format t "@url{file://~A, ignore, @t{~A}}~%"
		   system-source-directory
		   system-source-directory))))))
	(t
	 (render-location (component-pathname (component definition))
			  extract))))



;; ==========================================================================
;; Files
;; ==========================================================================

;; -------------------
;; Rendering protocols
;; -------------------

(defmethod type-name ((definition file-definition))
  "Return \"file\""
  "file")

(defmethod safe-name :around
    ((definition file-definition)
     &optional qualify
     &aux (name (call-next-method))
	  (extension (reveal (asdf:file-type (file definition)))))
  "Append DEFINITION's file extension at the end."
  (declare (ignore qualify))
  (when extension (setq name (concatenate 'string name "." extension)))
  name)


;; -----------------------
;; Documentation protocols
;; -----------------------

;; #### NOTE: other kinds of files are only documented as simple components.
(defmethod document ((definition lisp-file-definition) extract &key)
  "Render lisp file DEFINITION's documentation in EXTRACT."
  #+()(call-next-method)
  #+()(when (typep definition 'system-file-definition)
    (render-references (system-definitions definition) "Systems"))
  #+()(render-packages-references (package-definitions definition))
  #+()(render-external-definitions-references (external-definitions definition))
  #+()(render-internal-definitions-references (internal-definitions definition)))


;; -----
;; Nodes
;; -----

(defun file-node (definition extract)
  "Create and return a file DEFINITION node in EXTRACT."
  (make-node :name (long-title definition)
	     :section-name
	     (format nil "@t{~A}" (escape (safe-name definition t)))
	     :before-menu-contents
	     (render-to-string (document definition extract))))

(defun add-files-node
    (parent extract
     &aux lisp-file-definitions c-file-definitions java-file-definitions
	  html-file-definitions doc-file-definitions
	  static-file-definitions source-file-definitions file-definitions
	  (files-node (add-child parent
			(make-node
			 :name "Files"
			 :synopsis "The files documentation"
			 :before-menu-contents (format nil "~
Files are sorted by type and then listed depth-first from the systems
components trees.")))))
  "Add the files node to PARENT in EXTRACT."
  (dolist (definition
	   (remove-if-not #'file-definition-p (definitions extract)))
    (etypecase definition
      ;; #### WARNING: the order is important!
      (lisp-file-definition (push definition lisp-file-definitions))
      (c-file-definition (push definition c-file-definitions))
      (java-file-definition (push definition java-file-definitions))
      (html-file-definition (push definition html-file-definitions))
      (doc-file-definition (push definition doc-file-definitions))
      (static-file-definition (push definition static-file-definitions))
      (source-file-definition (push definition source-file-definitions))
      (file-definition (push definition file-definitions))))
  ;; #### FIXME: Arnesi lists the asd file as a static-file, so it appears
  ;; twice.
  (loop :with node
	:for definitions
	  :in (mapcar #'nreverse
		(list lisp-file-definitions
		      c-file-definitions java-file-definitions
		      html-file-definitions doc-file-definitions
		      static-file-definitions source-file-definitions
		      file-definitions))
	:for name
	  :in '("Lisp files" "C files" "Java files" "HTML files" "Doc files"
		"Static files" "Source files" "Other files")
	:for section-name
	  :in '("Lisp" "C" "Java" "HTML" "Doc" "Static" "Source" "Other")
	:when definitions
	  :do (setq node
		    (add-child files-node
		      (make-node :name name :section-name section-name)))
	  :and :do (dolist (definition definitions)
		     (add-child node (file-node definition extract)))))



;; ==========================================================================
;; Modules
;; ==========================================================================

(defmethod type-name ((definition module-definition))
  "Return \"module\""
  "module")

(defmethod document ((definition module-definition) extract &key)
  "Render module DEFINITION's documentation in EXTRACT."
  #+()(call-next-method)
  (when-let* ((children (child-definitions definition))
	      (length (length children)))
    (@tableitem (format nil "Component~p" length)
      (if (eq length 1)
	(reference (first children))
	(@itemize-list children :renderer #'reference)))))


;; -----
;; Nodes
;; -----

(defun add-modules-node
    (parent extract
     &aux (module-definitions
	   (remove-if-not
	       ;; This is to handle module subclasses, although I don't really
	       ;; know if we're going to face it some day.
	       (lambda (definition)
		 (and (module-definition-p definition)
		      (not (system-definition-p definition))))
	       (definitions extract))))
  "Add the modules node to PARENT in EXTRACT."
  (when module-definitions
    (let ((modules-node (add-child parent
			  (make-node :name "Modules"
				     :synopsis "The modules documentation"
				     :before-menu-contents
				     (format nil "~
Modules are listed depth-first from the system components tree.")))))
      (dolist (definition module-definitions)
	(add-child modules-node
	  (make-node :name (long-title definition)
		     :section-name (format nil "@t{~A}"
				     (escape (safe-name definition t)))
		     :before-menu-contents
		     (render-to-string (document definition extract))))))))



;; ==========================================================================
;; System
;; ==========================================================================

(defmethod type-name ((definition system-definition))
  "Return \"system\""
  "system")

(defmethod document ((definition system-definition) extract &key)
  "Render system DEFINITION's documentation in EXTRACT."
  (when-let (long-name (long-name definition))
    (@tableitem "Long Name" (format t "~A~%" (escape long-name))))
  (flet ((render-contacts (names emails category)
	   "Render a CATEGORY contact list of NAMES and EMAILS."
	   ;; Both names and emails are null or not at the same time.
	   (when names
	     (@tableitem
		 (format nil (concatenate 'string category "~P") (length names))
	       ;; #### FIXME: @* and map ugliness. I'm sure FORMAT can do all
	       ;; #### this.
	       (format t "~@[~A~]~:[~; ~]~@[<@email{~A}>~]"
		 (escape (car names)) (car emails) (escape (car emails)))
	       (mapc (lambda (name email)
		       (format t "@*~%~@[~A~]~:[~; ~]~@[<@email{~A}>~]"
			 (escape name) email (escape email)))
		 (cdr names) (cdr emails)))
	     (terpri))))
    (render-contacts
     (maintainer-names definition) (maintainer-emails definition) "Maintainer")
    (render-contacts
     (author-names definition) (author-emails definition) "Author"))
  (when-let (mailto (mailto definition))
    (@tableitem "Contact" (format t "@email{~A}~%" (escape mailto))))
  (when-let (homepage (homepage definition))
    (@tableitem "Home Page" (format t "@uref{~A}~%" (escape homepage))))
  (when-let (source-control (source-control definition))
    (@tableitem "Source Control"
      (etypecase source-control
	(string
	 (format t "@~:[t~;uref~]{~A}~%"
		 (search "://" source-control)
		 (escape source-control)))
	(t
	 ;; #### FIXME: why this before ?
	 ;; (escape (format nil "~(~S~)" source-control))
	 (format t "@t{~A}~%" source-control)))))
  (when-let (bug-tracker (bug-tracker definition))
    (@tableitem "Bug Tracker" (format t "@uref{~A}~%" (escape bug-tracker))))
  (when-let (license-name (license-name definition))
    (@tableitem "License" (format t "~A~%" (escape license-name))))
  (call-next-method))


;; -----
;; Nodes
;; -----

(defun add-systems-node
    (parent extract
     &aux (systems-node (add-child parent
			  (make-node :name "Systems"
				     :synopsis "The systems documentation"
				     :before-menu-contents
				     (format nil "~
The main system appears first, followed by any subsystem dependency.")))))
  "Add the systems node to PARENT in EXTRACT."
  (dolist (definition
	   (remove-if-not #'system-definition-p (definitions extract)))
    (add-child systems-node
      (make-node :name (long-title definition)
		 :section-name (format nil "@t{~A}"
				 (escape (safe-name definition t)))
		 :before-menu-contents
		 (render-to-string (document definition extract))))))

;;; asdf.lisp ends here
