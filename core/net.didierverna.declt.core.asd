;;; net.didierverna.declt.core.asd --- Declt core ASDF system definition

;; Copyright (C) 2015, 2021, 2022 Didier Verna

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

;; #### PORTME.
(defsystem :net.didierverna.declt.core
  :long-name
  "Documentation Extractor from Common Lisp to Texinfo, core library"
  :description "Declt's core functionality"
  :long-description "\
The Declt core library provides the main functionality of Declt. For a more
complete description of Declt, see the `net.didierverna.declt' system."
  :author "Didier Verna"
  :mailto "didier@didierverna.net"
  :homepage
  "http://www.lrde.epita.fr/~didier/software/lisp/typesetting.php#declt"
  :source-control "https://github.com/didierverna/declt"
  :license "BSD"
   :version (:read-file-line #p"../make/version.make"
	     :at (1 (lambda (str) (subseq str 19))))
  :if-feature :sbcl
  :depends-on ((:feature :sbcl (:require :sb-introspect))
	       :net.didierverna.declt.setup :net.didierverna.declt.assess)
  :serial t
  :components ((:file "package")
	       (:module "src"
		:serial t
		:components ((:module "util"
			      :serial t
			      :components ((:file "misc")))
			     (:module "doc"
			      :serial t
			      :components ((:file "texi")
					   (:file "doc")
					   (:file "symbol")
					   (:file "package")
					   (:file "asdf")))
			     (:file "declt")))))

;;; net.didierverna.declt.core.asd ends here
