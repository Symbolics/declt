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

;; #### NOTE: the only ASDF components documented by Declt are source files,
;; #### modules and systems. This function is used by the corresponding
;; #### REFERENCE methods because the code is the same. The reason we don't do
;; #### this as a method on COMPONENT directly is that such a method (see
;; #### below) handles other components, such as extensions, that we don't
;; #### know about.
(defun reference-component (component)
  "Render COMPONENT's reference."
  (@ref (anchor-name component) component)
  (format t " (~A)~%" (type-name component)))

(defun reference-asdf-definition (definition)
  "Render ASDF DEFINITION's reference."
  (@ref (anchor-name definition) definition)
  (format t " (~A)~%" (type-name definition)))

(defgeneric virtual-path (component)
  (:documentation "Return CONMPONENT's virtual path.
This is the string of successive component names to access COMPONENT from the
toplevel system, separated by slashes. File components also get their
extension at the end.")
  (:method (component)
    "Default method for all components."
    (format nil "~{~A~^/~}" (component-find-path component)))
  (:method :around ((source-file asdf:source-file)
		    &aux (virtual-path (call-next-method))
			 (extension (asdf:file-type source-file)))
    "Potentially add SOURCE-FILE's extension at the end of the virtual path."
    (when extension
      (setq virtual-path (concatenate 'string virtual-path "." extension)))
    virtual-path))



;; ==========================================================================
;; Components
;; ==========================================================================

;; -------------------
;; Rendering protocols
;; -------------------

;; #### FIXME: remove when we have all definitions.
(defmethod name ((component asdf:component))
  "Return COMPONENT's name."
  (reveal (component-name component)))

(defmethod name ((component-definition component-definition))
  "Return COMPONENT-DEFINITION's name."
  (reveal (component-name (component component-definition))))


;; -----------------------
;; Documentation protocols
;; -----------------------

;; #### FIXME: remove when we have all definitions.
(defmethod title ((component asdf:component))
  "Return COMPONENT's title."
  (virtual-path component))

(defmethod title ((component-definition component-definition))
  "Return COMPONENT-DEFINITION's title."
  (virtual-path (component component-definition)))

;; #### FIXME: remove when we have all definitions.
(defmethod anchor-name ((component asdf:component))
  "Return COMPONENT's anchor name."
  (virtual-path component))

(defmethod anchor-name ((component-definition component-definition))
  "Return COMPONENT-DEFINITION's anchor name."
  (virtual-path (component component-definition)))

;; #### NOTE: this method is needed as a default method for potential ASDF
;; extensions. I'm not willing to hard-code all possible such extensions, past
;; present and future. Besides, those components would not be related to code,
;; so Declt will not document them.
(defmethod reference ((component asdf:component))
  "Render unreferenced COMPONENT."
  (format t "@t{~(~A}~) (other component)~%" (escape component)))

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
  (@table ()
    (call-next-method)))

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

;; #### FIXME: remove in the end.
(defmethod name ((source-file asdf:source-file)
		 &aux (name (component-name source-file))
		      (extension (asdf:file-type source-file)))
  "Return SOURCE-FILE's name, possibly adding its extension."
  (when extension (setq name (concatenate 'string name "." extension)))
  (reveal name))

;; #### FIXME: reveal mess. Reveal should be in an around method as far
;; outside as possible.
(defmethod name :around
    ((definition file-definition)
     &aux (name (call-next-method))
	  (extension (reveal (asdf:file-type (component definition)))))
  "Return file DEFINITION's name, possibly adding its extension."
  (when extension (setq name (concatenate 'string name "." extension)))
  name)


;; -----------------------
;; Documentation protocols
;; -----------------------

;; #### FIXME: need more factoring.
(defmethod index ((definition lisp-file-definition))
  "Render Lisp file DEFINITION's indexing command."
  (format t "@lispfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition c-file-definition))
  "Render C file DEFINITION's indexing command."
  (format t "@cfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition java-file-definition))
  "Render Java file DEFINITION's indexing command."
  (format t "@javafileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition html-file-definition))
  "Render HTML file DEFINITION's indexing command."
  (format t "@htmlfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition doc-file-definition))
  "Render doc file DEFINITION's indexing command."
  (format t "@docfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition static-file-definition))
  "Render static file DEFINITION's indexing command."
  (format t "@staticfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition source-file-definition))
  "Render source file DEFINITION's indexing command."
  (format t "@sourcefileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

(defmethod index ((definition file-definition))
  "Render other file DEFINITION's indexing command."
  (format t "@otherfileindex{~A}@c~%"
    (escape (virtual-path (file definition)))))

;; #### FIXME: remove this afterwards.
(defmethod reference ((source-file asdf:source-file))
  "Render SOURCE-FILE's reference."
  (reference-component source-file))

(defmethod reference ((definition source-file-definition))
  "Render source file DEFINITION's reference."
  (reference-asdf-definition definition))

;; #### NOTE: other kinds of files are only documented as simple components.
(defmethod document ((definition lisp-file-definition) extract &key)
  "Render lisp file DEFINITION's documentation in EXTRACT."
  (call-next-method)
  (render-packages-references (package-definitions definition))
  (render-external-definitions-references (external-definitions definition))
  (render-internal-definitions-references (internal-definitions definition)))


;; -----
;; Nodes
;; -----

;; #### FIXME: one of the casing problem is here. We shouldn't downcase file
;; names!
(defun file-node (definition extract)
  "Create and return a file DEFINITION node in EXTRACT."
  (make-node :name (format nil "~@(~A~)" (title definition))
	     :section-name
	     (format nil "@t{~A}" (escape (virtual-path (file definition))))
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
components trees."))))
	  (lisp-files-node (add-child files-node
			     (make-node :name "Lisp files"
					:section-name "Lisp"))))
  "Add the files node to PARENT in EXTRACT."
  (dolist (definition (file-definitions extract))
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
  ;; #### NOTE: the .asd are Lisp files, but not components. I still want them
  ;; to be listed here (and first) so I need to duplicate some of what the
  ;; DOCUMENT method on lisp files does.
  ;; #### WARNING: multiple systems may be defined in the same .asd file.
  ;; #### FIXME: Arnesi lists the asd file as a static-file, so it appears
  ;; twice.
  (dolist (system (remove-duplicates
		   ;; #### FIXME: when can a system source file be null?
		   (remove-if #'null
		       (mapcar #'system (system-definitions extract))
		     :key #'system-source-file)
		   :test #'equal :key #'system-source-file))
    (let ((system-base-name (escape (system-base-name system)))
	  (system-source-file (system-source-file system)))
      (add-child lisp-files-node
	(make-node :name (format nil "The ~A file" system-base-name)
		   :section-name (format nil "@t{~A}" system-base-name)
		   :before-menu-contents
		   (render-to-string
		     (@anchor
		      (format nil "go to the ~A file" system-base-name))
		     (format t "@lispfileindex{~A}@c~%" system-base-name)
		     (@table ()
		       (render-location system-source-file extract)
		       (render-references
			(loop :for system :in (mapcar #'system
						(system-definitions extract))
			      :when (equal (system-source-file system)
					   system-source-file)
				:collect system)
			"Systems")
		       (render-packages-references
			(file-packages system-source-file))
		       (render-external-definitions-references
			(sort (definitions-from-file system-source-file
						     (external-definitions
						      extract))
			      #'string-lessp
			      :key #'definition-symbol))
		       (render-internal-definitions-references
			(sort (definitions-from-file system-source-file
						     (internal-definitions
						      extract))
			      #'string-lessp
			      :key #'definition-symbol))))))))
  (dolist (definition (nreverse lisp-file-definitions))
    (add-child lisp-files-node (file-node definition extract)))
  (loop :with other-files-node
	:for definitions
	  :in (mapcar #'nreverse
		(list c-file-definitions java-file-definitions
		      html-file-definitions doc-file-definitions
		      static-file-definitions source-file-definitions
		      file-definitions))
	:for name
	  :in '("C files" "Java files" "HTML files" "Doc files"
		"Static files" "Source files" "Other files")
	:for section-name
	  :in '("C" "Java" "HTML" "Doc" "Static" "Source" "Other")
	:when definitions
	  :do (setq other-files-node
		    (add-child files-node
		      (make-node :name name :section-name section-name)))
	  :and :do (dolist (definition definitions)
		     (add-child other-files-node
		       (file-node definition extract)))))



;; ==========================================================================
;; Modules
;; ==========================================================================

;; -----------------------
;; Documentation protocols
;; -----------------------

;; #### FIXME: remove when we have all definitions.
(defmethod index ((module asdf:module))
  "Render MODULE's indexing command."
  (format t "@moduleindex{~A}@c~%" (escape (virtual-path module))))

(defmethod index ((module-definition module-definition))
  "Render MODULE-DEFINITION's indexing command."
  (format t "@moduleindex{~A}@c~%"
    (escape (virtual-path (module module-definition)))))

;; #### FIXME: remove when we have all definitions.
(defmethod reference ((module asdf:module))
  "Render MODULE's reference."
  (reference-component module))

(defmethod reference ((definition module-definition))
  "Render module DEFINITION's reference."
  (reference-asdf-definition definition))

(defmethod document ((definition module-definition) extract &key)
  "Render module DEFINITION's documentation in EXTRACT."
  (call-next-method)
  (when-let* ((children (children definition))
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
     &aux (module-definitions (module-definitions extract)))
  "Add the modules node to PARENT in EXTRACT."
  (when module-definitions
    (let ((modules-node (add-child parent
			  (make-node :name "Modules"
				     :synopsis "The modules documentation"
				     :before-menu-contents
				     (format nil "~
Modules are listed depth-first from the system components tree.")))))
      (dolist (module-definition module-definitions)
	(add-child modules-node
	  (make-node :name (format nil "~@(~A~)" (title module-definition))
		     :section-name (format nil "@t{~A}"
				     (escape
				      ;; #### FIXME: this is unclean and it
				      ;; seems to be the same as title.
				      (virtual-path
				       (module module-definition))))
		     :before-menu-contents
		     (render-to-string
		       (document module-definition extract))))))))



;; ==========================================================================
;; System
;; ==========================================================================

;; -----------------------
;; Documentation protocols
;; -----------------------

;; #### FIXME: remove when we have all definitions.
(defmethod index ((system asdf:system))
  "Render SYSTEM's indexing command."
  (format t "@systemindex{~A}@c~%" (escape system)))

(defmethod index ((system-definition system-definition))
  "Render SYSTEM-DEFINITION's indexing command."
  (format t "@systemindex{~A}@c~%" (escape system-definition)))

;; #### FIXME: remove when we have all definitions.
(defmethod reference ((system asdf:system))
  "Render SYSTEM's reference."
  (reference-component system))

(defmethod reference ((definition system-definition))
  "Render system DEFINITION's reference."
  (reference-asdf-definition definition))

(defmethod document ((definition system-definition) extract &key)
  "Render system DEFINITION's documentation in EXTRACT."
  (when-let (long-name (long-name definition))
    (@tableitem "Long Name"
      (format t "~A~%" (escape long-name))))
  (flet ((render-contacts (names emails category)
	   "Render a CATEGORY contact list of NAMES and EMAILS."
	   (when (and names emails) ;; both are null or not at the same time.
	     (@tableitem (format nil (concatenate 'string category "~P")
			   (length names))
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
    (@tableitem "Contact"
      (format t "@email{~A}~%" (escape mailto))))
  (when-let (homepage (homepage definition))
    (@tableitem "Home Page"
      (format t "@uref{~A}~%" (escape homepage))))
  (when-let (source-control (source-control definition))
    (@tableitem "Source Control"
      (etypecase source-control
	(string
	 (format t "@~:[t~;uref~]{~A}~%"
		 (search "://" source-control)
		 (escape source-control)))
	(t
	 (format t "@t{~A}~%"
		 (escape (format nil "~(~S~)" source-control)))))))
  (when-let (bug-tracker (bug-tracker definition))
    (@tableitem "Bug Tracker"
      (format t "@uref{~A}~%" (escape bug-tracker))))
  (format t "~@[@item License~%~
	     ~A~%~]" (escape (license definition)))
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
  (dolist (system-definition (system-definitions extract))
    (add-child systems-node
      (make-node :name (format nil "~@(~A~)" (title system-definition))
		 :section-name (format nil "@t{~(~A~)}"
				 (escape system-definition))
		 :before-menu-contents
		 (render-to-string (document system-definition extract))))))

;;; asdf.lisp ends here
