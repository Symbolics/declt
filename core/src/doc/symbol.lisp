;;; symbol.lisp --- Symbol based documentation

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
;; Rendering protocols
;; ==========================================================================

(defmethod safe-name
    ((definition symbol-definition)
     &optional qualified
     &aux (name (reveal (princ-to-string (name definition)))))
  "Reveal symbol DEFINITION's name, possibly QUALIFIED.
A QUALIFIED name is of the form \"package:[:]symbol\"."
  (when qualified
    (setq name (concatenate 'string
		 (reveal (name (home-package definition)))
		 (if (publicp definition) ":" "::")
		 name)))
  name)

;; #### NOTE: spaces in symbol names are revealed (see above), but not the
;; ones between SETF and the symbol in a setf name, because that would look
;; rather weird in the output. Consequently, Declt must expect to get names
;; with unescaped spaces. @DEFFN, @DEFFNX, AND @DEFTP take care of protecting
;; their NAME argument with braces because of that.
(defmethod safe-name
    ((definition setf-mixin)
     &optional qualified
     &aux (name (reveal (princ-to-string (second (name definition))))))
  "Reveal setf DEFINITION's name, possibly QUALIFIED.
A QUALIFIED name is of the form \"(setf package:[:]symbol)\"."
  (when qualified
    (setq name (concatenate 'string
		 (reveal (name (home-package definition)))
		 (if (publicp definition) ":" "::")
		 name)))
  ;; Hack for future case-preserving implementation.
  (format nil "(~A ~A)" 'setf name))



;; ==========================================================================
;; Utilities
;; ==========================================================================

(defun render-definition-core (definition context)
  "Render DEFINITION's documentation core in CONTEXT.
The documentation core includes all common definition attributes:
  - package,
  - source location.

Each element is rendered as a table item."
  (@tableitem "Package"
    (reference (home-package definition) t))
  (when-let (source (source-file definition))
    (@tableitem "Source" (reference source t))))




;; ==========================================================================
;; Documentation Protocols
;; ==========================================================================

;; #### NOTE: all the indexing methods below perform sub-indexing only,
;; because the main index entries are created automatically in Texinfo by the
;; @defXXX routines.

;; -------
;; Varoids
;; -------

(defmacro render-varoid (definition context
			 &body body
			 &aux (the-definition (gensym "definition"))
			      (the-context (gensym "context")))
  "Execute BODY within a varoid DEFINITION documentation in CONTEXT.
BODY is executed within a @table environement."
  `(let ((,the-definition ,definition)
	 (,the-context ,context))
     (@defvr (string-capitalize (category-name ,the-definition))
	 ;; #### WARNING: casing policy.
	 (string-downcase (safe-name ,the-definition))
       (anchor-and-index ,the-definition)
       (render-docstring ,the-definition)
       (@table () ,@body))))

(defmethod document ((definition varoid-definition) context &key)
  "Render varoid DEFINITION's documentation in CONTEXT.
This is the default method used for simple varoids,
providing only basic information."
  (render-varoid definition context
    (render-definition-core definition context)))



;; Constants
(defmethod category-name ((definition constant-definition))
  "Return \"constant\"."
  "constant")

(defmethod index-command-name ((definition constant-definition))
  "Return \"constantsubindex\"."
  "constantsubindex")



;; Special variables
(defmethod category-name ((definition special-definition))
  "Return \"special variable\"."
  "special variable")

(defmethod index-command-name ((definition special-definition))
  "Return \"specialsubindex\"."
  "specialsubindex")



;; Symbol macros
(defmethod category-name ((definition symbol-macro-definition))
  "Return \"symbol macro\"."
  "symbol macro")

(defmethod index-command-name ((definition symbol-macro-definition))
  "Return \"symbolmacrosubindex\"."
  "symbolmacrosubindex")


;; Slots
(defmethod safe-name :around
    ((definition slot-definition)
     &optional qualified
     &aux (safe-name (call-next-method)))
  "When QUALIFIED, prepend slot DEFINITION's classoid safe name."
  (if qualified
    (concatenate 'string (safe-name (owner definition) t) "->" safe-name)
    safe-name))

(defmethod category-name ((definition slot-definition))
  "Return \"slot\"."
  "slot")

(defmethod index-command-name ((definition slot-definition))
  "Return \"slotsubindex\"."
  "slotsubindex")

(defmethod document ((definition clos-slot-definition) context &key)
  "Render CLOS slot DEFINITION's documentation in CONTEXT.
- The source file is not documented at all, since it is lexically the same as
  that of the parent classoid.
- The package is not documented, unless it differs from that of the parent
  classoid."
  (render-varoid definition context
    (unless (eq (home-package definition) (home-package (owner definition)))
      (@tableitem "Package" (reference (home-package definition) t)))
    (flet ((render (value)
	     (format t "@t{~A}~%"
	       ;; #### WARNING: casing policy.
	       (escape (format nil "~(~S~)" value)))))
      ;; #### FIXME: not rendering standard / default values should be a
      ;; context choice.
      (when-let (value-type (value-type definition))
	(unless (eq value-type t)
	  (@tableitem "Type" (render value-type))))
      (when-let (allocation (allocation definition))
	(unless (eq allocation :instance)
	  (@tableitem "Allocation" (render allocation))))
      (when-let (initform (initform definition))
	(@tableitem "Initform" (render initform)))
      (when-let (initargs (initargs definition))
	(@tableitem "Initargs"
	  ;; #### FIXME: format mess. There's gotta be a better way.
	  (let ((values (mapcar (lambda (val)
				  ;; #### WARNING: casing policy.
				  (escape (format nil "~(~S~)" val)))
			  initargs)))
	    (format t "@t{~A}~{, @t{~A}~}"
	      (first values)
	      (rest values))))))
    (render-references "Readers"
      ;; #### WARNING: casing policy.
      (sort (readers definition) #'string-lessp :key #'definition-symbol)
      t)
    (if (and (readers definition) (not (writers definition)))
      (@tableitem "Writers" (format t "@i{This slot is read-only.}~%"))
      (render-references "Writers"
	;; #### WARNING: casing policy.
	(sort (writers definition) #'string-lessp :key #'definition-symbol)
	t))))

(defmethod document
    ((definition typed-structure-slot-definition) context &key)
  "Render typed structure slot DEFINITION's documentation in CONTEXT.
- The source file is unavailable, but not documented at all anyway, since it
  is lexically the same as that of the parent classoid.
- The package is not documented, unless it differs from that of the parent
  classoid."
  (render-varoid definition context
    (unless (eq (home-package definition) (home-package (owner definition)))
      (@tableitem "Package" (reference (home-package definition) t)))
    ;; #### FIXME: not rendering standard / default values should be a context
    ;; choice.
    (unless (eq (value-type definition) t)
      (@tableitem "Type"
	(format t "@t{~A}~%"
	  ;; #### WARNING: casing policy.
	  (escape (format nil "~(~S~)" (value-type definition))))))
    (render-references "Reader" (readers definition) t)
    (if (and (readers definition) (not (writers definition)))
      (@tableitem "Writer" (format t "@i{This slot is read-only.}~%"))
      (render-references "Writer" (writers definition) t))))



;; --------
;; Funcoids
;; --------

(defun merge-expander-p (definition expander)
  "Return T if function DEFINITION and setf EXPANDER can be documented jointly."
  ;; #### NOTE: a function and its expander share the same symbol, hence
  ;; package. The rest needs to be checked. Also, we don't want to merge short
  ;; form setf expanders because we have additional implementation details to
  ;; advertise (the writer operator).
  (and definition expander
       (typep expander 'long-expander-definition)
       (equal (source-file definition) (source-file expander))
       (equal (docstring definition) (docstring expander))))

;; #### TODO: there's the question of offering the option to qualify symbols.
(defun safe-lambda-list (lambda-list)
  "Return a safe LAMBDA-LIST, suitable to pass to Texinfo.
The original lambda-list's structure is preserved, but all symbols are
converted to revealed strings, and initform / supplied-p data is removed."
  (loop :with post-mandatory
	:for rest :on lambda-list
	:for element := (if (and (listp (car rest)) post-mandatory)
			  (first (car rest))
			  (car rest))
	:if (listp element)
	  :collect (safe-lambda-list element) :into safe-lambda-list
	:else :if (member element '(&optional &rest &key &allow-other-keys
				    &aux &environment &whole &body))
		;; #### WARNING: casing policy.
		:collect (string-downcase element) :into safe-lambda-list
		:and :do (setq post-mandatory t)
			 ;; #### WARNING: casing policy.
	:else :collect (reveal (string-downcase element))
		:into safe-lambda-list
	:finally (progn (when rest ;; dotted list
			  (setf (cdr (last safe-lambda-list))
				;; #### WARNING: casing policy.
				(reveal (string-downcase rest))))
			(return safe-lambda-list))))

(defun render-headline (definition)
  "Render a headline for DEFINITION. Also anchor and index it."
  (@deffnx (string-capitalize (category-name definition))
      (string-downcase (safe-name definition))
    (safe-lambda-list (lambda-list definition)))
  (anchor-and-index definition))

(defmacro render-funcoid
    (|definition(s)| context
     &body body
     &aux (the-definition (gensym "definition"))
	  (the-context (gensym "context")))
  "Render funcoid DEFINITION(S) documentation in CONTEXT."
  `(let ((,the-definition ,(if (consp |definition(s)|)
			     (car |definition(s)|)
			     |definition(s)|))
	 (,the-context ,context))
     (@deffn ((string-capitalize (category-name ,the-definition))
	      ;; #### WARNING: casing policy.
	      (string-downcase (safe-name ,the-definition))
	      (safe-lambda-list (lambda-list ,the-definition)))
	 (anchor-and-index ,the-definition)
       ,@(mapcar (lambda (funcoid) `(render-headline ,funcoid))
	   (when (consp |definition(s)|) (cdr |definition(s)|)))
       (render-docstring ,the-definition)
       (@table ()
	 (render-definition-core ,the-definition ,the-context)
	 ,@body))))

(defmethod document ((definition funcoid-definition) context &key)
  "Render funcoid DEFINITION's documentation in CONTEXT.
This is the default method used for simple funcoids,
providing only basic information."
  (render-funcoid definition context))



;; Macros
(defmethod category-name ((definition macro-definition))
  "Return \"macro\"."
  "macro")

(defmethod index-command-name ((definition macro-definition))
  "Return \"macrosubindex\"."
  "macrosubindex")

(defmethod document
    ((definition macro-definition) context
     &key
     &aux (expander-for (expander-for definition)))
  "Render macro DEFINITION's documentation in CONTEXT."
  (if (merge-expander-p definition expander-for)
    (render-funcoid (definition expander-for) context
      (when-let (expanders-to (expanders-to definition))
	(render-references "Setf expanders to this macro"
	  ;; #### WARNING: casing policy.
	  (sort expanders-to #'string-lessp :key #'definition-symbol)
	  t)))
    (render-funcoid definition context
      (when-let (expander-for (expander-for definition))
	(@tableitem "Setf expander for this macro"
	  (reference expander-for t)))
      (when-let (expanders-to (expanders-to definition))
	(render-references "Setf expanders to this macro"
	  ;; #### WARNING: casing policy.
	  (sort expanders-to #'string-lessp :key #'definition-symbol)
	  t)))))



;; Compiler macros
(defmethod category-name ((definition compiler-macro-definition))
  "Return \"compiler macro\"."
  "compiler macro")

(defmethod index-command-name ((definition compiler-macro-definition))
  "Return \"compilermacrosubindex\"."
  "compilermacrosubindex")



;; Types
(defmethod category-name ((definition type-definition))
  "Return \"type\"."
  "type")

(defmethod index-command-name ((definition type-definition))
  "Return \"typesubindex\"."
  "typesubindex")

;; #### WARNING: a type is a funcoid because it has a lambda list, but it's
;; really a @deftp, not a @deffn.
(defmethod document ((definition type-definition) context &key)
  "Render type DEFINITION's documentation in CONTEXT."
  ;; #### WARNING: casing policy.
  (@deftype (string-downcase (safe-name definition))
      (safe-lambda-list (lambda-list definition))
    (anchor-and-index definition)
    (render-docstring definition)
    (@table ()
      (render-definition-core definition context))))



;; Setf expanders
(defmethod category-name ((expander expander-definition))
  "Return \"setf expander\"."
  "setf expander")

(defmethod index-command-name ((expander expander-definition))
  "Return \"expandersubindex\"."
  "expandersubindex")

(defmethod document ((definition short-expander-definition) context &key)
  "Render short setf expander DEFINITION's documentation in CONTEXT."
  (render-funcoid definition context
    (when-let (standalone-reader (standalone-reader definition))
      (@tableitem "Reader"
	(reference standalone-reader)))
    (let ((standalone-writer (standalone-writer definition)))
      (cond (standalone-writer
	     (@tableitem "Writer"
	       (reference (standalone-writer definition))))
	    ((not (foreignp definition))
	     (@tableitem "Writer" (princ "@i{missing}")))))))

(defmethod document
    ((definition long-expander-definition) context
     &key
     &aux (standalone-reader (standalone-reader definition)))
  "Render long setf expander DEFINITION's documentation in CONTEXT."
  (unless (merge-expander-p standalone-reader definition)
    (render-funcoid definition context
      (when-let (standalone-reader (standalone-reader definition))
	(@tableitem "Reader"
	  (reference standalone-reader))))))



;; Method combinations
(defmethod category-name ((definition combination-definition))
  "Return \"method combination\"."
  "method combination")

(defmethod index-command-name ((definition combination-definition))
  "Return \"combinationsubindex\"."
  "combinationsubindex")

(defmethod document ((definition combination-definition) context &key)
  "Render method combination DEFINITION's documentation in CONTEXT."
  (render-funcoid definition context
    (render-references "Client Functions"
      ;; #### WARNING: casing policy.
      (sort (clients definition) #'string-lessp :key #'definition-symbol)
      t)))

(defmethod document ((definition short-combination-definition) context &key)
  "Render short method combination DEFINITION's documentation in CONTEXT."
  (render-funcoid definition context
    (let ((standalone-combinator (standalone-combinator definition)))
      (cond (standalone-combinator
	     (@tableitem "Operator" (reference standalone-combinator)))
	    ((not (foreignp definition))
	     (@tableitem "Operator" (princ "@i{missing}")))))
    (@tableitem "Identity with one argument"
      (format t "@t{~(~A~)}" (identity-with-one-argument definition)))
    (render-references "Client Functions"
      ;; #### WARNING: casing policy.
      (sort (clients definition) #'string-lessp :key #'definition-symbol)
      t)))



;; Methods
(defmethod safe-name :around
    ((definition method-definition)
     &optional qualified
     &aux (safe-name (call-next-method)))
  "When QUALIFIED, append method DEFINITION's qualifiers and specializers."
  (if qualified
    (concatenate 'string
      safe-name
      ;; #### NOTE: I'm using an S for qualifiers, assuming they'll always be
      ;; symbols, in order to distinguish keywords from the rest.
      (format nil "~{ ~S~} (~{~A~^ ~})"
	(method-qualifiers (definition-method definition))
	(mapcar (lambda (specializer)
		  (typecase specializer
		    (definition (safe-name specializer t))
		    (otherwise specializer))) ;; EQL specializer
	  (specializers definition))))
    safe-name))

(defmethod category-name ((definition method-definition))
  "Return \"method\"."
  "method")

(defmethod category-name ((definition reader-method-definition))
  "Return \"reader method\"."
  "reader method")

(defmethod category-name ((definition writer-method-definition))
  "Return \"writer method\"."
  "writer method")

(defmethod index-command-name ((definition method-definition))
  "Return \"methodsubindex\"."
  "methodsubindex")

(defun safe-specializers (specializers)
  (loop :for rest :on specializers
	:for specializer := (car rest)
	:collect (typecase specializer
		   (definition
		    (with-output-to-string (*standard-output*)
		      (reference specializer t (when (cdr rest) #\,))))
		   ;; #### WARNING: casing policy.
		   (otherwise (format nil "~(~A~)" specializer)))))

(defmacro render-method
    (|definition(s)| context
     &body body
     &aux (the-definition (gensym "definition")))
  "Execute BODY within a method DEFINITION(S) documentation in CONTEXT."
  `(let ((,the-definition ,(if (consp |definition(s)|)
			     (car |definition(s)|)
			     |definition(s)|)))
     (@defmethod (string-capitalize (category-name ,the-definition))
	 ;; #### WARNING: casing policy.
	 (string-downcase (safe-name ,the-definition))
       (when-let (qualifiers
		  (method-qualifiers (definition-method ,the-definition)))
	 (format nil "~(~{~S~^ ~}~)" qualifiers))
       (safe-specializers (specializers ,the-definition))
       (anchor-and-index ,the-definition)
       ,@(mapcar (lambda (definition)
		   (let ((the-definition (gensym "definition")))
		     `(let ((,the-definition ,definition))
			(@defmethodx
			    (string-capitalize (category-name ,the-definition))
			    ;; #### WARNING: casing policy.
			    (string-downcase (safe-name ,the-definition))
			  (when-let (qualifiers
				     (method-qualifiers
				      (definition-method ,the-definition)))
			    (format nil "~(~{~S~^ ~}~)" qualifiers))
			  (safe-specializers (specializers ,the-definition)))
			(anchor-and-index ,the-definition))))
	   (when (consp |definition(s)|) (cdr |definition(s)|)))
       (render-docstring ,the-definition)
       (when-let (source-file (source-file ,the-definition))
	 (unless (equal source-file
			(source-file (owner ,the-definition)))
	   (@table () (@tableitem "Source" (reference source-file t)))))
       ,@body)))

(defmethod document ((definition method-definition) context &key)
  "Render METHOD's documentation in CONTEXT."
  (render-method definition context))

(defmethod document ((definition reader-method-definition) context &key)
  "Render reader METHOD's documentation in CONTEXT."
  (render-method definition context
    (@table ()
      (@tableitem "Target Slot"
	(reference (target-slot definition) t)))))

(defmethod document ((definition writer-method-definition) context &key)
  "Render writer METHOD's documentation in CONTEXT."
  (render-method definition context
    (@table ()
      (@tableitem "Target Slot"
	(reference (target-slot definition) t)))))



;; Ordinary functions
(defmethod category-name ((definition ordinary-function-definition))
  "Return \"function\"."
  "function")

(defmethod index-command-name ((definition ordinary-function-definition))
  "Return \"functionsubindex\"."
  "functionsubindex")

(defmethod document
    ((definition simple-function-definition) context
     &key
     &aux (expander-for (expander-for definition)))
  "Render simple function DEFINITION's documentation in CONTEXT."
  (if (merge-expander-p definition expander-for)
    (render-funcoid (definition expander-for)
	(when-let (expanders-to (expanders-to definition))
	  (render-references "Setf expanders to this function"
	    ;; #### WARNING: casing policy.
	    (sort expanders-to #'string-lessp :key #'definition-symbol) t)))
    (render-funcoid definition context
      (when-let (expander-for (expander-for definition))
	(@tableitem "Setf expander for this function"
	  (reference expander-for t)))
      (when-let (expanders-to (expanders-to definition))
	(render-references "Setf expanders to this function"
	  ;; #### WARNING: casing policy.
	  (sort expanders-to #'string-lessp :key #'definition-symbol) t)))))


(defun merge-accessors-p (reader writer)
  "Return T if READER and WRITER definitions can be documented jointly."
  ;; #### NOTE: structure accessors necessarily share the same package and
  ;; source. The rest needs to be checked.
  (and reader writer
       (not (expander-for reader))
       (not (expanders-to reader))
       (equal (docstring reader) (docstring writer))))

(defmethod category-name ((definition reader-definition))
  "Return \"reader\"."
  "reader")

(defmethod document
    ((definition reader-definition) context
     &key
     &aux (writer (first (writers (target-slot definition)))))
  "Render function DEFINITION's documentation in CONTEXT."
  (if (merge-accessors-p definition writer)
    (render-funcoid (definition writer) context
      (@tableitem "Target Slot"
	(reference (target-slot definition) t)))
    (render-funcoid definition context
      (@tableitem "Target Slot"
	(reference (target-slot definition) t))
      (when-let (expander-for (expander-for definition))
	(@tableitem "Setf expander for this function"
	  (reference expander-for t)))
      (when-let (expanders-to (expanders-to definition))
	(render-references "Setf expanders to this function"
	  ;; #### WARNING: casing policy.
	  (sort expanders-to #'string-lessp :key #'definition-symbol) t)))))


(defmethod category-name ((definition writer-definition))
  "Return \"writer\"."
  "writer")

(defmethod document ((definition writer-definition) context &key)
  "Render writer DEFINITION's documentation in CONTEXT."
  (unless (merge-accessors-p (first (readers (target-slot definition)))
			     definition)
    (render-funcoid definition context
      (@tableitem "Target Slot"
	(reference (target-slot definition) t)))))



;; Generic functions
(defmethod category-name ((definition generic-function-definition))
  "Return \"generic function\"."
  "generic function")

(defmethod index-command-name ((definition generic-function-definition))
  "Return \"genericsubindex\"."
  "genericsubindex")

(defun render-method-combination (definition)
  "Render generic function DEFINITION's method combination documentation."
  (@tableitem "Method Combination"
    (reference (combination definition) t)
    (terpri)
    (when-let (options (mapcar (lambda (option)
				 ;; #### FIXME: see TODO on format-tables.
				 ;; #### WARNING: casing policy.
				 (escape (format nil "~(~S~)" option)))
			 (combination-options definition)))
      (@table ()
	(@tableitem "Options"
	  (format t "~{@t{~A}~^, ~}" options))))))

(defmethod document ((definition simple-generic-definition) context &key)
  "Render simple generic function DEFINITION's documentation in CONTEXT."
  (render-funcoid definition context
    (when-let (expander-for (expander-for definition))
      (@tableitem "Setf expander for this function"
	(reference expander-for t)))
    (when-let (expanders-to (expanders-to definition))
      (render-references "Setf expanders to this function"
	;; #### WARNING: casing policy.
	(sort expanders-to #'string-lessp :key #'definition-symbol)
	t))
    (render-method-combination definition)
    (when-let ((methods (methods definition)))
      (@tableitem "Methods"
	(dolist (method methods)
	  (document method context))))))

(defmethod document ((definition generic-setf-definition) context &key)
  "Render generic setf DEFINITION's documentation in CONTEXT."
  (render-funcoid definition context
    (render-method-combination definition)
    (when-let ((methods (methods definition)))
      (@tableitem "Methods"
	(dolist (method methods)
	  (document method context))))))



;; ---------
;; Classoids
;; ---------

(defun render-initargs (definition context)
  "Render classoid DEFINITION's direct default initargs in CONTEXT."
  (when-let (initargs (direct-default-initargs definition))
    (@tableitem "Direct Default Initargs"
      ;; #### FIXME: we should rather compute the longest initarg name and use
      ;; that as a template size for the @headitem specification.
      (@multitable (.3f0 .5f0)
	(format t "@headitem Initarg @tab Value~%")
	(dolist (initarg initargs)
	  (format t "@item @t{~A}~%@tab @t{~A}~%"
	    ;; #### WARNING: casing policy.
	    ;; The ~S is to preserve the appearance of keywords.
	    (escape (format nil "~(~S~)" (first initarg)))
	    (escape (format nil "~(~A~)" (second initarg)))))))))

(defmacro render-clos-classoid (definition context &body body)
  "Execute BODY within a CLOS classoid DEFINITION documentation in CONTEXT."
  (let ((the-definition (gensym "definition"))
	(the-context (gensym "context")))
    `(let ((,the-definition ,definition)
	   (,the-context ,context))
       (@deftp ((string-capitalize (category-name ,the-definition))
		;; #### WARNING: casing policy.
		(string-downcase (safe-name ,the-definition)))
	   (anchor-and-index ,the-definition)
	 (render-docstring ,the-definition)
	 ;; #### TODO: we may want to change the titles below to display not
	 ;; only "classes", but "structures" and "conditions" directly.
	 (@table ()
	   (render-definition-core ,the-definition ,the-context)
	   (render-references "Direct superclasses"
	     ;; #### WARNING: casing policy.
	     (sort (direct-superclassoids ,the-definition) #'string-lessp
	       :key #'definition-symbol)
	     t)
	   (render-references "Direct subclasses"
	     ;; #### WARNING: casing policy.
	     (sort (direct-subclassoids ,the-definition) #'string-lessp
	       :key #'definition-symbol)
	     t)
	   (render-references "Direct methods"
	     ;; #### WARNING: casing policy.
	     (sort (direct-methods ,the-definition) #'string-lessp
	       :key #'definition-symbol)
	     t)
	   (when-let (direct-slots (direct-slots ,the-definition))
	     (@tableitem "Direct slots"
	       (dolist (direct-slot direct-slots)
		 (document direct-slot ,the-context))))
	   ,@body)))))

(defmethod document ((definition classoid-definition) context &key)
  "Render classoid DEFINITION's documentation in CONTEXT.
This is the default method used for conditions and classes,
which also documents direct default initargs."
  (render-clos-classoid definition context
    (render-initargs definition context)))



;; Structures
(defmethod category-name ((definition structure-definition))
  "Return \"structure\"."
  "structure")

(defmethod index-command-name ((definition structure-definition))
  "Return \"structuresubindex\"."
  "structuresubindex")

(defmethod document ((definition clos-structure-definition) context &key)
  "Render CLOS structure DEFINITION's documentation in CONTEXT."
  (render-clos-classoid definition context))

(defmethod document ((definition typed-structure-definition) context &key)
  "Render typed structure DEFINITION's documentation in CONTEXT."
  (@deftp ("Structure"
	   ;; #### WARNING: casing policy.
	   (string-downcase (safe-name definition)))
      (anchor-and-index definition)
    (render-docstring definition)
    (@table ()
      (render-definition-core definition context)
      (@tableitem "Type"
	(if (eq (element-type definition) t)
	  ;; #### WARNING: casing policy.
	  (format t "@t{~(~S~)}~%" (structure-type definition))
	  (format t "@t{(vector ~(~A~))}~%" (element-type definition))))
      (when-let (direct-slots (direct-slots definition))
	(@tableitem "Direct slots"
	  (dolist (direct-slot direct-slots)
	    (document direct-slot context)))))))



;; Conditions
(defmethod category-name ((definition condition-definition))
  "Return \"condition\"."
  "condition")

(defmethod index-command-name ((definition condition-definition))
  "Return \"conditionsubindex\"."
  "conditionsubindex")



;; Classes
(defmethod category-name ((definition class-definition))
  "Return \"class\"."
  "class")

(defmethod index-command-name ((definition class-definition))
  "Return \"classsubindex\"."
  "classsubindex")



;; ==========================================================================
;; Definition Nodes
;; ==========================================================================

;; ----------
;; Categories
;; ----------

;; #### NOTE: the order in *CATEGORIES* is important (see
;; ADD-CATEGORIES-NODE). It conditions the order of appearance of the
;; definitions in the generated manual.

(defparameter *categories*
  '((constant-definition          "constants")
    (special-definition           "special variables")
    (symbol-macro-definition      "symbol macros")
    (macro-definition             "macros")
    (compiler-macro-definition    "compiler macros")
    (expander-definition          "setf expanders")
    (ordinary-function-definition "ordinary functions")
    (generic-function-definition  "generic functions")
    (combination-definition       "method combinations")
    (condition-definition         "conditions")
    (structure-definition         "structures")
    (class-definition             "classes")
    (type-definition              "types"))
  "The list of definition categories.
Each category is of type (TYPE DESCRIPTION-STRING).")

(defun add-category-node (parent context status category definitions)
  "Add the STATUS CATEGORY node to PARENT for DEFINITIONS in CONTEXT."
  (add-child parent
    (make-node :name (format nil "~@(~A ~A~)" status category)
	       :section-name (format nil "~@(~A~)" category)
	       :before-menu-contents
	       (render-to-string
		 (dolist (definition (sort definitions #'string-lessp
					   :key #'definition-symbol))
		   (document definition context))))))

(defun add-categories-node (parent context status definitions)
  "Add the STATUS DEFINITIONS categories nodes to PARENT in CONTEXT."
  (dolist (category *categories*)
    (when-let (type-definitions
	       (remove-if-not (lambda (definition)
				(typep definition (first category)))
		   definitions))
      ;; #### WARNING: hack alert. A setf expander merged with its reader
      ;; funcoid will disappear from the Setf Expanders section. So we need to
      ;; filter those out as well here.
      (when (eq (first category) 'expander-definition)
	(setq type-definitions
	      (remove-if (lambda (definition)
			   (merge-expander-p (standalone-reader definition)
					     definition))
		  type-definitions)))
      (when type-definitions
	(add-category-node parent context status (second category)
			   type-definitions)))))

(defun add-definitions-node
    (parent extract context
     &aux (public-definitions (public-definitions extract))
	  (public-definitions-number (length public-definitions))
	  (private-definitions (private-definitions extract))
	  (private-definitions-number (length private-definitions)))
  "Add EXTRACT's definitions node to PARENT in CONTEXT."
  (unless (zerop (+ public-definitions-number private-definitions-number))
    (let ((definitions-node
	    (add-child parent
	      (make-node :name "Definitions"
			 :synopsis "The symbols documentation"
			 :before-menu-contents(format nil "~
Definitions are sorted by export status, category, package, and then by
lexicographic order.")))))
      (unless (zerop public-definitions-number)
	(let ((node (add-child definitions-node
		      (make-node :name "Public Interface"))))
	  (add-categories-node node context "public" public-definitions)))
      (unless (zerop private-definitions-number)
	(let ((node (add-child definitions-node
		      (make-node :name "Internals"))))
	  (add-categories-node node context "private" private-definitions))))))

;;; symbol.lisp ends here
