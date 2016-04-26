;;; smedl-mode.el --- Major mode for editing SMEDL.

;; Copyright © 2016, by BAE Systems

;; Author: Theophilos Giannakopoulos (theo.giannakopoulos@baesystems.com)
;; Version: 0.0.1
;; Created: 25 April 2016
;; Keywords: languages
;; Homepage: 

;; This file is not part of GNU Emacs.

;;; License:

;; All rights reserved.

;;; Commentary:

;; short description here

;; full doc on how to use here


;;; Code:

;; define several category of keywords
(setq smedl-sections '("state" "events" "scenarios"))
(setq smedl-keywords '("object" "imported" "exported" "when" "else"))
(setq smedl-types '("int" "float"))
(setq smedl-constants '("Error"))
(setq smedl-functions '("raise"))

;; generate reg ex string for each category of keywords
(setq smedl-sections-regexp (regexp-opt smedl-sections 'words))
(setq smedl-keywords-regexp (regexp-opt smedl-keywords 'words))
(setq smedl-type-regexp (regexp-opt smedl-types 'words))
(setq smedl-constant-regexp (regexp-opt smedl-constants 'words))
(setq smedl-functions-regexp (regexp-opt smedl-functions 'words))

;; create the list for font-lock.
;; each category of keyword is given a particular face
(setq smedl-font-lock-keywords
      `(
        (,smedl-type-regexp . font-lock-type-face)
        (,smedl-constant-regexp . font-lock-constant-face)
        (,smedl-functions-regexp . font-lock-builtin-face)
        (,smedl-keywords-regexp . font-lock-keyword-face)
        (,smedl-sections-regexp . font-lock-keyword-face)
        ;; numeric constants
        ("[+-]?[[:digit:]]+\\(\\.[[:digit:]]+\\)?\\>" . font-lock-constant-face)
        ;; scenario names
        ("^[[:blank:]]*\\([[:word:]_]+\\):" 1 font-lock-function-name-face)
        ;; transition source state names
        ("^[[:blank:]]*\\([[:word:]_]+\\)[[:blank:]]*->" 1 font-lock-variable-name-face)
        ;; transition destination state names
        ("->[[:blank:]]*\\<\\([[:word:]_]+\\)[[:blank:]]*$" 1 font-lock-variable-name-face)
        ;; note: order above matters, because once colored, that part won't change.
        ;; in general, longer words first
        ))

;;;###autoload
(define-derived-mode smedl-mode fundamental-mode
  "smedl mode"
  "Major mode for editing SMEDL (Stateful Meta-Event Description Language)…"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((smedl-font-lock-keywords))))

;; clear memory. no longer needed
(setq smedl-sections nil)
(setq smedl-keywords nil)
(setq smedl-types nil)
(setq smedl-constants nil)
(setq smedl-functions nil)

;; clear memory. no longer needed
(setq smedl-sections-regexp nil)
(setq smedl-keywords-regexp nil)
(setq smedl-types-regexp nil)
(setq smedl-constants-regexp nil)
(setq smedl-functions-regexp nil)

;; add the mode to the `features' list
(provide 'smedl-mode)

;; Local Variables:
;; coding: utf-8
;; End:

;;; smedl-mode.el ends here
