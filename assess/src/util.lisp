;;; util.lisp --- Utilities

;; Copyright (C) 2010, 2011, 2013, 2016-2017, 2020-2022 Didier Verna

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

(in-package :net.didierverna.declt.assess)
(in-readtable :net.didierverna.declt)


;; ==========================================================================
;; Introspection
;; ==========================================================================

;; #### NOTE: SB-INTROSPECT:FIND-DEFINITION-SOURCES-BY-NAME may return
;; multiple sources (e.g. if we were to ask it for methods) so we take the
;; first one. This is okay because we actually use it only when there can be
;; only one definition source.

;; #### NOTE: CCL's FIND-DEFINITION-SOURCES returns a list of entries of the
;; form ((TYPE . NAME) SOURCE ...) where SOURCE is either a source note, or
;; directly a file name. Also, CCL may record logical pathnames (e.g. for
;; files loaded from Quicklisp), which would never be EQUAL to the physical
;; ones that ASDF knows about, so we need to translate them.
#+ccl
(defun ccl-source-pathname (sources)
  "Return the physical pathname of the first of CCL's SOURCES, or NIL."
  (when-let* ((source (second (first sources)))
	      (file (if (ccl:source-note-p source)
		      (ccl:source-note-filename source)
		      source)))
    (translate-logical-pathname (pathname file))))

;; #### PORTME.
(defun source-by-name (name type)
  "Return source pathname for NAMEd object of TYPE."
  #+sbcl
  (when-let (sources (sb-introspect:find-definition-sources-by-name name type))
    (sb-introspect:definition-source-pathname (first sources)))
  ;; #### NOTE: CCL records setf expanders under the accessor's name.
  #+ccl
  (ccl-source-pathname
   (ccl:find-definition-sources
       (if (and (eq type :setf-expander) (consp name)) (second name) name)
     (ecase type
       (:constant 'ccl::constant)
       (:variable 'variable)
       (:symbol-macro 'ccl::symbol-macro)
       (:setf-expander 'ccl::setf-expander)
       (:method-combination 'method-combination)
       (:type 'type)
       (:structure 'structure)))))

;; #### PORTME.
(defun source-by-object (object)
  "Return OBJECT's source pathname."
  #+sbcl
  (when-let (source (sb-introspect:find-definition-source object))
    (sb-introspect:definition-source-pathname source))
  ;; #### NOTE: CCL doesn't record the source of structure classes (nor of
  ;; typed structure descriptions) under the object itself, but only under the
  ;; structure's name.
  #+ccl
  (ccl-source-pathname
   (typecase object
     (structure-class
      (ccl:find-definition-sources (class-name object) 'structure))
     (simple-vector
      (ccl:find-definition-sources (ccl::sd-name object) 'structure))
     (otherwise (ccl:find-definition-sources object)))))

;; #### PORTME.
(defun variable-kind (symbol)
  "Return SYMBOL's variable kind.
Only :constant, :special, and :macro (for symbol macros) are of interest."
  #+sbcl
  (sb-int:info :variable :kind symbol)
  #+ccl
  (cond ((constantp symbol) :constant)
	((ccl::proclaimed-special-p symbol) :special)
	((nth-value 1 (macroexpand-1 symbol)) :macro)))

;; #### PORTME.
(defun setf-expander (symbol)
  "Return SYMBOL's setf expander, or NIL.
A short form expander is a list the CAR of which is the name of its update
function."
  #+sbcl
  (sb-int:info :setf :expander symbol)
  ;; #### NOTE: for the short form of DEFSETF, CCL only stores the name of the
  ;; update function, so we wrap it in a list.
  #+ccl
  (let ((expander (ccl::%setf-method symbol)))
    (if (and expander (symbolp expander)) (list expander) expander)))

;; #### PORTME.
(defun function-lambda-list (function)
  "Return FUNCTION's lambda list.
FUNCTION may be a function, a generic function, or a macro function."
  #+sbcl
  (sb-introspect:function-lambda-list function)
  ;; #### WARNING: CCL only keeps the lambda lists of macros (by name) and
  ;; generic functions. For ordinary functions, it reconstructs one from the
  ;; compiled code (which loses default values, and supplied-p parameters).
  ;; For compiler macros, we cannot get it at all, so we return NIL.
  #+ccl
  (let ((name (ccl:function-name function)))
    (cond ((and (consp name) (eq (first name) 'compiler-macro-function))
	   nil)
	  ((and (symbolp name) (eq function (macro-function name)))
	   (values (ccl:arglist name)))
	  (t
	   (values (ccl:arglist function))))))

;; #### PORTME.
(defun combination-by-name (name)
  "Return the method combination object for NAME, or NIL.
This object represents the method combination as a general entity, as opposed
to any of its instantiations with specific options."
  #+sbcl
  (gethash name sb-pcl::**method-combinations**)
  ;; #### NOTE: in CCL, this is an information vector, except for the standard
  ;; method combination, which doesn't have any (and is a regular instance).
  #+ccl
  (if (eq name 'standard)
    ccl::*standard-method-combination*
    (ccl::method-combination-info name)))

;; #### NOTE: CCL's structure descriptions (CCL::SD-... accessors) are used for
;; both typed and CLOS structures. They don't have a dedicated object
;; representing a slot, and the reader names are kept in a separate list, so
;; we reconstruct slot descriptions for them.
#+ccl
(defun structure-slots (description)
  "Return structure DESCRIPTION's slots.
Each slot is a list of the form (NAME TYPE READER-NAME)."
  (mapcar (lambda (slot reader-name)
	    (list (ccl::ssd-name slot) (ccl::ssd-type slot) reader-name))
      ;; Typed structures may have an extra slot for their name, which is
      ;; identified by a number instead of a symbol.
      (remove-if-not #'symbolp (ccl::sd-slots description)
		     :key (lambda (slot) (ccl::ssd-name slot)))
    (ccl::sd-refnames description)))




;; ==========================================================================
;; ASDF
;; ==========================================================================

(defun reorder-dependency-def (dependency-def)
  "Reorder information in DEPENDENCY-DEF so that the system is always first.
More specifically:
- simple component names are returned as-is,
- :version expressions are returned as (system :version version-specifier),
- :feature expressions are returned as (... :feature feature-expression),
- :require expressions are returned as (system :require).

Note that because a feature expression is defined recursively, the first
element in the reordered list may be another reordered sub-list rather than a
simple component name directly. In any case, the system name will always be
in the deepest first position."
  (typecase dependency-def ;; RTE to the rescue!
    (list (ecase (car dependency-def)
	    (:feature
	     (list (reorder-dependency-def (third dependency-def))
		   :feature (second dependency-def)))
	    (:version
	     (list (second dependency-def)
		   :version (third dependency-def)))
	    (:require
	     (list (second dependency-def) :require))))
    (otherwise dependency-def)))

(defun reordered-dependency-def-system (reordered-dependency-def)
  "Extract the system name from REORDERED-DEPENDENCY-DEF.
See `reorder-dependency-def' for more information."
  (typecase reordered-dependency-def
    (list (reordered-dependency-def-system (car reordered-dependency-def)))
    (otherwise reordered-dependency-def)))




;; ==========================================================================
;; Miscellaneous
;; ==========================================================================

(defun one-liner-p (string)
  "Return T if STRING is non empty and does not span multiple lines."
  (and string (not (or (zerop (length string)) (find #\Newline string)))))


;; #### NOTE: the functions below are relatively robust, without using the
;; whole regexp artillery.
(defun validate-email
    (string
     &aux (string (string-trim '(#\Space #\Tab) string))
	  (@-position (position #\@ string)))
  "Check that STRING is of the form nonblank@nonblank, after trimming.
Return that string, or issue a warning and return NIL."
  (if (and @-position (> @-position 0) (< @-position (1- (length string))))
    string
    (warn "Invalid email address: ~A." string)))

(defun parse-contact-string
    (string &aux (pos-< (position #\< string)) (pos-> (position #\> string)))
  "Parse STRING of the form \"My Name <my@address>\".
Both name and address are optional. If only an address is provided, the angle
brackets may be omitted.
If neither a name nor an address can be extracted, return NIL. Otherwise,
return the list (\"My Name\" . \"my@address\"). In such a case, either the CAR
or the CDR may be null, but not both."
  (when (one-liner-p string)
    (cond ((and pos-< pos-> (< pos-< pos->))
	   (let ((name (if (zerop pos-<)
			 ""
			 (string-trim '(#\Space #\Tab)
				      (subseq string 0 (1- pos-<)))))
		 (email (validate-email (subseq string (1+ pos-<) pos->))))
	     (when (zerop (length name)) (setq name nil))
	     (when (or name email) (cons name email))))
	  ((position #\@ string)
	   (let ((email (validate-email string) ))
	     (when email (cons nil email))))
	  (t
	   (let ((name (string-trim '(#\Space #\Tab) string)))
	     (unless (zerop (length name)) (list name)))))))

(defun |parse-contact(s)| (|contact(s)|)
  "Parse CONTACT(S) as either a contact string, or a list of such.
Return a list of parsed contacts. See `parse-contact-string' for more
information."
  (when (stringp |contact(s)|) (setq |contact(s)| (list |contact(s)|)))
  (remove nil
	  (mapcar #'parse-contact-string
	    (remove-duplicates |contact(s)| :from-end t :test #'string=))))

;;; util.lisp ends here
