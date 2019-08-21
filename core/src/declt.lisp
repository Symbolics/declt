;;; declt.lisp --- Entry points

;; Copyright (C) 2010-2013, 2015-2018 Didier Verna

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


;; #### FIXME: when we make this a customizable variable instead of a
;; constant, we need to decide on whether this should be raw Texinfo contents,
;; or whether to escape the notices before using them.
(defparameter *licenses*
  '((:mit
     "The MIT License"
     "Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THIS SOFTWARE IS PROVIDED \"AS IS\" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.")
    (:boost
     "The Boost Software License - Version 1.0"
"Permission is hereby granted, free of charge, to any person or organization
obtaining a copy of the software and accompanying documentation covered by
this license (the \"Software\") to use, reproduce, display, distribute,
execute, and transmit the Software, and to prepare derivative works of the
Software, and to permit third-parties to whom the Software is furnished to
do so, all subject to the following:

The copyright notices in the Software and this entire statement, including
the above license grant, this restriction and the following disclaimer,
must be included in all copies of the Software, in whole or in part, and
all derivative works of the Software, unless such copies or derivative
works are solely in the form of machine-executable object code generated by
a source language processor.

THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE, TITLE AND NON-INFRINGEMENT. IN NO EVENT
SHALL THE COPYRIGHT HOLDERS OR ANYONE DISTRIBUTING THE SOFTWARE BE LIABLE
FOR ANY DAMAGES OR OTHER LIABILITY, WHETHER IN CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.")
    (:bsd
     "The BSD License"
     "Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THIS SOFTWARE IS PROVIDED \"AS IS\" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.")
    (:gpl
     "The GNU GPL License"
     "This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.")
      (:lgpl
       "The GNU LGPL License"
       "This program is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.")))

(defun render-header (library-name tagline version contact-names contact-emails
		      copyright-years license
		      texi-name info-name declt-notice
		      current-time-string)
  "Render the header of the Texinfo file."
  (format t "\\input texinfo~2%@c ~A.texi --- Reference manual~2%" texi-name)

  (when copyright-years
    (mapc (lambda (name)
	    (format t "@c Copyright (C) ~A ~A~%" copyright-years name))
      ;; #### NOTE: we already removed the duplicates in the original contact
      ;; list, but there may still be duplicates in the names, for instance if
      ;; somebody used his name several times, with a different email
      ;; address.
      (remove-duplicates contact-names :from-end t :test #'string=))
    (terpri))

  (format t "@c This file is part of ~A.~2%" library-name)

  (when license
    (with-input-from-string (str (caddr license))
      (loop :for line := (read-line str nil str)
	    :until (eq line str)
	    :do (format t "@c ~A~%" line))))

  (terpri)
  (terpri)

  (format t "@c Commentary:~2%~
	     @c Generated automatically by Declt version ~A~%~
	     @c on ~A.~3%"
    (version :long) current-time-string)

  (format t "~
@c ====================================================================
@c Header
@c ====================================================================
@c %**start of header
@setfilename ~A.info
@settitle The ~A Reference Manual
@afourpaper
@documentencoding UTF-8
@c %**end of header~4%"
    (escape info-name) (escape library-name))

  (format t "~
@c ====================================================================
@c Format Specific Tweaks
@c ====================================================================
@tex
%% Declt uses several Unicode characters to \"reveal\" blanks. This
%% works fine in HTML or Info output, but TeX will have problems with
%% these. The code below translates those characters to something that
%% TeX can handle.

%% U+23B5 (Bottom Square Bracket), used to reveal white spaces, is
%% translated to its Computer Modern teletype version.
\\DeclareUnicodeCharacter{23B5}{{\\tt\\char'040}}

%% U+21B5 (Downwards Arrow With Corner Leftwards), used to reveal
%% carriage returns, is translated to \\hookleftarrow in math mode.
\\DeclareUnicodeCharacter{21B5}{\\ensuremath\\hookleftarrow}

%% U+21E5 (Rightwards Arrow To Bar), used to reveal tabs, is
%% translated to something that looks similar, based on a rightarrow
%% and a vertical bar from the math extension font.
\\DeclareUnicodeCharacter{21E5}{%
  \\ensuremath{\\rightarrow\\kern-.5em\\mathchar\\\"130C}}


%% Declt uses several Unicode characters to replace \"fragile\" ones in
%% anchor names and references. These characters are chosen to resemble
%% the original ones, without interfering with Info syntax. In TeX
%% however, we can switch them back to the original versions, because
%% cross-references are done differently. In theory, I think we could do
%% something similar for HTML output (again, only the Info syntax poses
%% problems), but I don't know how to do something similar to what's
%% below.

%% U+2024 (One Dot Leader) replaces periods.
\\DeclareUnicodeCharacter{2024}{.}

%% U+201A (Single Low-9 Quotation Mark) replaces commas, but it seems to be
%% already declared in PDFTeX, so we can't change it back.
%% \\DeclareUnicodeCharacter{201A}{,}

%% U+2236 (Ratio) replaces colons.
\\DeclareUnicodeCharacter{2236}{:}

%% U+2768 (Medium Left Parenthesis Ornament) replaces left parenthesis.
\\DeclareUnicodeCharacter{2768}{(}

%% U+2769 (Medium Right Parenthesis Ornament) replaces right parenthesis.
\\DeclareUnicodeCharacter{2769}{)}
@end tex~4%")

  (format t "~
@c ====================================================================
@c Settings
@c ====================================================================
@setchapternewpage odd
@documentdescription
The ~A Reference Manual~@[, version ~A~].
@end documentdescription~4%"
    (escape library-name) (escape version))

  (format t "~
@c ====================================================================
@c New Commands
@c ====================================================================

@c ---------------
@c Indexing macros
@c ---------------

@c Packages
@macro packageindex{name}
@tpindex \\name\\
@tpindex @r{Package, }\\name\\
@end macro

@c Systems
@macro systemindex{name}
@tpindex \\name\\
@tpindex @r{System, }\\name\\
@end macro

@c Modules
@macro moduleindex{name}
@cindex @t{\\name\\}
@cindex Module, @t{\\name\\}
@end macro

@c Lisp files
@macro lispfileindex{name}
@cindex @t{\\name\\}
@cindex Lisp File, @t{\\name\\}
@cindex File, Lisp, @t{\\name\\}
@end macro

@c C files
@macro cfileindex{name}
@cindex @t{\\name\\}
@cindex C File, @t{\\name\\}
@cindex File, C, @t{\\name\\}
@end macro

@c Java files
@macro javafileindex{name}
@cindex @t{\\name\\}
@cindex Java File, @t{\\name\\}
@cindex File, Java, @t{\\name\\}
@end macro

@c Other files
@macro otherfileindex{name}
@cindex @t{\\name\\}
@cindex Other File, @t{\\name\\}
@cindex File, other, @t{\\name\\}
@end macro

@c Doc files
@macro docfileindex{name}
@cindex @t{\\name\\}
@cindex Doc File, @t{\\name\\}
@cindex File, doc, @t{\\name\\}
@end macro

@c HTML files
@macro htmlfileindex{name}
@cindex @t{\\name\\}
@cindex HTML File, @t{\\name\\}
@cindex File, html, @t{\\name\\}
@end macro

@c The following macros are meant to be used within @defxxx environments.
@c Texinfo performs half the indexing job and we do the other half.

@c Constants
@macro constantsubindex{name}
@vindex @r{Constant, }\\name\\
@end macro

@c Special variables
@macro specialsubindex{name}
@vindex @r{Special Variable, }\\name\\
@end macro

@c Symbol macros
@macro symbolmacrosubindex{name}
@vindex @r{Symbol Macro, }\\name\\
@end macro

@c Slots
@macro slotsubindex{name}
@vindex @r{Slot, }\\name\\
@end macro

@c Macros
@macro macrosubindex{name}
@findex @r{Macro, }\\name\\
@end macro

@c Compiler Macros
@macro compilermacrosubindex{name}
@findex @r{Compiler Macro, }\\name\\
@end macro

@c Functions
@macro functionsubindex{name}
@findex @r{Function, }\\name\\
@end macro

@c Methods
@macro methodsubindex{name}
@findex @r{Method, }\\name\\
@end macro

@c Generic Functions
@macro genericsubindex{name}
@findex @r{Generic Function, }\\name\\
@end macro

@c Setf Expanders
@macro setfexpandersubindex{name}
@findex @r{Setf Expander, }\\name\\
@end macro

@c Method Combinations
@macro shortcombinationsubindex{name}
@tpindex @r{Short Method Combination, }\\name\\
@tpindex @r{Method Combination, Short, }\\name\\
@end macro

@macro longcombinationsubindex{name}
@tpindex @r{Long Method Combination, }\\name\\
@tpindex @r{Method Combination, Long, }\\name\\
@end macro

@c Conditions
@macro conditionsubindex{name}
@tpindex @r{Condition, }\\name\\
@end macro

@c Structures
@macro structuresubindex{name}
@tpindex @r{Structure, }\\name\\
@end macro

@c Types
@macro typesubindex{name}
@tpindex @r{Type, }\\name\\
@end macro

@c Classes
@macro classsubindex{name}
@tpindex @r{Class, }\\name\\
@end macro~4%")

  (format t "~
@c ====================================================================
@c Info Category and Directory
@c ====================================================================
@dircategory Common Lisp
@direntry
* ~A Reference: (~A). The ~A Reference Manual.
@end direntry~4%"
    (escape library-name) (escape info-name) (escape library-name))

  (when license
    (format t "~
@c ====================================================================
@c Copying
@c ====================================================================
@copying
@quotation~%")

    (when copyright-years
      (mapc (lambda (name)
	      (format t "Copyright @copyright{} ~A ~A~%"
		(escape copyright-years) (escape name)))
	;; #### NOTE: we already removed the duplicates in the original
	;; contact list, but there may still be duplicates in the names, for
	;; instance if somebody used his name several times, with a different
	;; email address.
	(remove-duplicates contact-names :from-end t :test #'string=))
      (terpri))
    (format t "~
Permission is granted to make and distribute verbatim copies of this
manual provided the copyright notice and this permission notice are
preserved on all copies.

@ignore
Permission is granted to process this file through TeX and print the
results, provided the printed document carries a copying permission
notice identical to this one except for the removal of this paragraph
(this paragraph not being relevant to the printed manual).

@end ignore
Permission is granted to copy and distribute modified versions of this
manual under the conditions for verbatim copying, provided also that the
section entitled ``Copying'' is included exactly as in the original.

Permission is granted to copy and distribute translations of this manual
into another language, under the above conditions for modified versions,
except that this permission notice may be translated as well.
@end quotation
@end copying~4%"))

  (format t "~
@c ====================================================================
@c Title Page
@c ====================================================================
@titlepage
@title The ~A Reference Manual
~A~%"
    (escape library-name)
    (if (or tagline version)
	(format nil "@subtitle ~@[~A~]~:[~;, ~]~@[version ~A~]~%"
	  (escape tagline) (and tagline version) (escape version))
	""))
  (mapc (lambda (name email)
	  (format t "@author ~@[~A~]~:[~; ~]~@[<@email{~A}>~]~%"
	    (escape name) email (escape email)))
    contact-names contact-emails)
  (terpri)
  (when (or declt-notice license)
    (format t "@page~%"))

  (when declt-notice
    (format t "~
@quotation
This manual was generated automatically by Declt ~A~@[ on ~A~].
@end quotation~%"
    (escape (version declt-notice))
    (when (eq declt-notice :long) (escape current-time-string))))

  (when license
    (format t "@vskip 0pt plus 1filll~%@insertcopying~%"))

  (format t "@end titlepage~4%")

  (format t "~
@c ====================================================================
@c Table of Contents
@c ====================================================================
@contents~%"))

(defun add-packages (context)
  "Add all package definitions to CONTEXT."
  (setf (context-packages context)
	;; #### NOTE: several subsystems may share the same packages (because
	;; they would share files defining them) so we need to filter
	;; potential duplicates out.
	(remove-duplicates
	 (mapcan #'system-packages (context-systems context)))))

(defun add-external-definitions (context)
  "Add all external definitions to CONTEXT."
  (dolist (symbol (mapcan #'system-external-symbols (context-systems context)))
    (add-symbol-definitions symbol (context-external-definitions context))))

(defun add-internal-definitions (context)
  "Add all internal definitions to CONTEXT."
  (dolist (symbol (mapcan #'system-internal-symbols (context-systems context)))
    (add-symbol-definitions symbol (context-internal-definitions context))))

(defun add-definitions (context)
  "Add all definitions to CONTEXT."
  (add-external-definitions context)
  (add-internal-definitions context)
  (finalize-definitions
   (context-external-definitions context)
   (context-internal-definitions context)))

(defun declt (system-name
	      &key (library-name (if (stringp system-name)
				   system-name
				   (string-downcase system-name)))
		   (tagline nil taglinep)
		   (version nil versionp)
		   (contact nil contactp)

		   copyright-years
		   license
		   introduction
		   conclusion

		   (texi-name (if (stringp system-name)
				system-name
				(string-downcase system-name)))
		   (texi-directory #p"./")
		   (info-name texi-name)
		   hyperlinks
		   (declt-notice :long)

	      &aux (system (find-system system-name))
		   (current-time-string (current-time-string))
		   contact-names contact-emails)
  "Generate a reference manual in Texinfo format for ASDF SYSTEM-NAME.
SYSTEM-NAME is an ASDF system designator.

The following keyword arguments are available.
- LIBRARY-NAME: name of the library being documented. Defaults to the system
  name.
- TAGLINE: small text to be used as the manual's subtitle. Defaults to the
  system long name or description.
- VERSION: version information. Defaults to the system version.
- CONTACT: contact information. Defaults to the system maintainer(s) and
  author(s), or \"John Doe\". Accepts an author string of the form
  \"My Name[ <my@address>]\", or a list of such.

- COPYRIGHT-YEARS: copyright years information or NIL. Defaults to the current
  year.
- LICENSE: license information. Defaults to NIL. Also accepts :mit, :boost,
  :bsd, :gpl, and :lgpl.
- INTRODUCTION: introduction chapter contents or NIL. Defaults to NIL.
- CONCLUSION: conclusion chapter contents or NIL. Defaults to NIL.

- TEXI-NAME: Texinfo file basename sans extension. Defaults to the system
  name.
- TEXI-DIRECTORY: Texinfo file directory. Defaults to the current directory.
- INFO-NAME: Info file basename sans extension. Defaults to TEXI-NAME.
- HYPERLINKS: create hyperlinks to files or directories. Defaults to NIL.
- DECLT-NOTICE: small credit paragraph to Declt, or NIL. Defaults to
  :long. Also accepts :short.

INTRODUCTION and CONCLUSION are currently expected to be in Texinfo format."

  ;; First load the target system. If this fails, there's no point in working
  ;; hard on the rest. Because of some bootstrapping issues, ASDF and UIOP
  ;; need some special-casing.
  (cond ((string= (asdf:coerce-name system-name) "uiop")
	 (load (merge-pathnames "uiop/uiop.asd"
				(system-source-directory
				 (asdf:find-system :asdf))))
	 (mapc #'load
	   (asdf:input-files :monolithic-concatenate-source-op
			     "asdf/driver")))
	((string= (asdf:coerce-name system-name) "asdf")
	 (setq system (find-system "asdf/defsystem"))
	 (mapc #'load
	   (asdf:input-files :monolithic-concatenate-source-op
			     "asdf/defsystem")))
	(t
	 (asdf:load-system system-name)))

  ;; Next, post-process some parameters.
  (unless taglinep
    (setq tagline (or (system-long-name system)
		      (component-description system))))
  (when (and tagline (zerop (length tagline)))
    (setq tagline nil))
  (when (and tagline (char= (aref tagline (1- (length tagline))) #\.))
    (setq tagline (subseq tagline 0 (1- (length tagline)))))
  (unless versionp
    (setq version (component-version system)))
  (when (and version (zerop (length version)))
    (setq version nil))
  (unless contact
    (setq contact (system-author system))
    (when (stringp contact) (setq contact (list contact)))
    (cond ((stringp (system-maintainer system))
	   (push (system-maintainer system) contact))
	  ((consp (system-maintainer system))
	   (setq contact (append (system-maintainer system) contact))))
    (unless contact (setq contact (list "John Doe"))))
  (setq contact (remove-duplicates contact :from-end t :test #'string=))
  (multiple-value-bind (names emails) (|parse-contact(s)| contact)
    (setq contact-names names
	  contact-emails emails))
  (when (and (= (length contact-names) 1)
	     (not contactp)
	     (null (car contact-emails))
	     (system-mailto system))
    (setq contact-emails (list (system-mailto system))))

  (setq copyright-years
	(or copyright-years
	    (multiple-value-bind (second minute hour date month year)
		(get-decoded-time)
	      (declare (ignore second minute hour date month))
	      (format nil "~A" year))))
  (when license
    (setq license (assoc license *licenses*))
    (unless license
      (error "License not found.")))

  ;; Construct the nodes hierarchy.
  (with-standard-io-syntax
    (let ((context (make-context
		    :systems
		    (cons system
			  (remove-duplicates
			   (subsystems system (system-directory system))))
		    :external-definitions (make-definitions-pool)
		    :internal-definitions (make-definitions-pool)
		    :hyperlinksp hyperlinks))
	  (top-node
	    (make-node :name "Top"
		       :section-name (format nil "The ~A Reference Manual"
				       (escape library-name))
		       :section-type :unnumbered
		       :before-menu-contents (format nil "~

This is the ~A Reference Manual~@[, version ~A~]~@[,
generated automatically by Declt version ~A~@[
on ~A~]~]."
					       (escape library-name)
					       (escape version)
					       (when declt-notice
						 (escape
						  (version declt-notice)))
					       (when (eq declt-notice :long)
						 (escape current-time-string)))
		       :after-menu-contents (when license "@insertcopying"))))
      (add-packages context)
      (add-definitions context)
      (when license
	(add-child top-node
	  (make-node :name "Copying"
		     :synopsis (cadr license)
		     :section-type :unnumbered
		     :before-menu-contents (format nil "@quotation~@
						    ~A~@
						    @end quotation"
					     (escape (caddr license))))))
      (when introduction
	(add-child top-node
	  (make-node :name "Introduction"
		     :synopsis (format nil "What ~A is all about"
				 (escape library-name))
		     :before-menu-contents introduction)))
      (add-systems-node     top-node context)
      (add-modules-node     top-node context)
      (add-files-node       top-node context)
      (add-packages-node    top-node context)
      (add-definitions-node top-node context)
      (when conclusion
	(add-child top-node
	  (make-node :name "Conclusion"
		     :synopsis "Time to go"
		     :before-menu-contents conclusion)))
      (let ((indexes-node (add-child top-node
			    (make-node :name "Indexes"
				       :synopsis (format nil "~
Concepts, functions, variables and data types")
				       :section-type :appendix))))
	(add-child indexes-node
	  (make-node :name "Concept index"
		     :section-type :appendix
		     :section-name "Concepts"
		     :before-menu-contents "@printindex cp"
		     :after-menu-contents "@page"))
	(add-child indexes-node
	  (make-node :name "Function index"
		     :section-type :appendix
		     :section-name "Functions"
		     :before-menu-contents "@printindex fn"
		     :after-menu-contents "@page"))
	(add-child indexes-node
	  (make-node :name "Variable index"
		     :section-type :appendix
		     :section-name "Variables"
		     :before-menu-contents "@printindex vr"
		     :after-menu-contents "@page"))
	(add-child indexes-node
	  (make-node :name "Data type index"
		     :section-type :appendix
		     :section-name "Data types"
		     :before-menu-contents "@printindex tp")))
      (with-open-file (*standard-output*
		       (merge-pathnames (make-pathname :name texi-name
						       :type "texi")
					texi-directory)
		       :direction :output
		       :if-exists :supersede
		       :if-does-not-exist :create
		       :external-format :utf8)
	(render-header library-name tagline version contact-names contact-emails
		       copyright-years license
		       texi-name info-name declt-notice
		       current-time-string)
	(render-top-node top-node)
	(format t "~%@bye~%~%@c ~A.texi ends here~%" texi-name))))
  (values))


;;; declt.lisp ends here
