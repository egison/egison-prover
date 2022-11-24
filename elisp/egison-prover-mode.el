;;; egison-prover-mode.el --- Egison editing mode

;; Copyright (C) 2011-2022 Satoshi Egi

;; Permission is hereby granted, free of charge, to any person obtaining
;; a copy of this software and associated documentation files (the "Software"),
;; to deal in the Software without restriction, including without limitation
;; the rights to use, copy, modify, merge, publish, distribute, sublicense,
;; and/or sell copies of the Software, and to permit persons to whom the Software
;; is furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included
;; in all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
;; INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR
;; A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
;; CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
;; OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;; Author: Satoshi Egi <egisatoshi@gmail.com>
;;; URL: https://github.com/egisatoshi/egison3/blob/master/elisp/egison-mode.el
;;; Version: 0.1.5

;;; Commentary:

;; Emacs Mode for Egison Prover
;;
;; Please put it in your load-path of Emacs. Then, add the following
;; lines in your .emacs.
;;
;;   (autoload 'egison-prover-mode "egison-prover-mode" "Major mode for editing Egison Prover code." t)
;;   (setq auto-mode-alist (cons `("\\.pegi$" . egison-prover-mode) auto-mode-alist))

;;; Code:

(defconst egison-prover-font-lock-keywords-1
  (eval-when-compile
    (list
     "\\<define\\>"
     "\\<data\\>"
     "\\<lambda\\>"
     "\\<Universe\\>"
     "\\<undefined\\>"
     "\\<something\\>"

     "\\\.\\\.\\\."
     "\\\,"
;     "'"
     "`"
     "\\\#"
     "|"
     "\\\&"
     "Π"
     "λ"
     "→"
     ":"
     "@"
     "!"
     "\\<_\\>"
     ))
  "Subdued expressions to highlight in Egison prover modes.")

(defconst egison-prover-font-lock-keywords-2
  (append egison-prover-font-lock-keywords-1
   (eval-when-compile
     (list
      (cons "\\\$\\\w*" font-lock-variable-name-face)
      (cons "\\\%\\\w*" font-lock-variable-name-face)
      )))
  "Gaudy expressions to highlight in Egison prover modes.")

(defvar egison-prover-font-lock-keywords egison-prover-font-lock-keywords-1
  "Default expressions to highlight in Egison prover modes.")


(defun egison-prover-open-paren-p ()
  (let ((c (string-to-char (thing-at-point 'char))))
    (or (eq c 40) (eq c 60) (eq c 91) (eq c 123))))

(defun egison-prover-close-paren-p ()
  (let ((c (string-to-char (thing-at-point 'char))))
    (or (eq c 41) (eq c 62) (eq c 93) (eq c 125))))

(defun egison-prover-last-unclosed-paren ()
  (save-excursion
    (let ((pc 0))
      (while (<= pc 0)
        (if (bobp)
            (setq pc 2)
          (backward-char)
          (if (egison-prover-open-paren-p)
              (progn
                (setq pc (+ pc 1))
                (if (and (= pc 0) (= (current-column) 0))
                    (setq pc 2)))
            (if (egison-prover-close-paren-p)
                (setq pc (- pc 1))))))
      (if (= pc 2)
          nil
        (point)))))

(defun egison-prover-indent-point ()
  (save-excursion
    (beginning-of-line)
    (let ((p (egison-prover-last-unclosed-paren)))
      (if p
          (progn
            (goto-char (egison-prover-last-unclosed-paren))
            (let ((cp (current-column)))
              (cond ((eq (string-to-char (thing-at-point 'char)) 40)
                     (forward-char)
                     (let* ((op (current-word))
                            (ip (egison-prover-keyword-indent-point op)))
                       (if ip
                           (+ ip cp)
                         (progn (forward-sexp)
                                (+ 1 (current-column))))))
                    ((eq (string-to-char (thing-at-point 'char)) 60)
                     (forward-char)
                     (let ((op (current-word)))
                       (+ 2 (length op) cp)))
                    ((eq (string-to-char (thing-at-point 'char)) 91)
                     (forward-char)
                     (if (eq (string-to-char (thing-at-point 'char)) 124)
                         (+ 2 cp)
                       (+ 1 cp)))
                    (t (+ 1 cp)))))
        0))))

(defun egison-prover-keyword-indent-point (name)
  (cond ((equal "define" name) 2)
        ((equal "data" name) 2)
        ((equal "λ" name) 2)
        ((equal "Π" name) 2)
        ))

(defun egison-prover-indent-line ()
  "indent current line as Egison-Prover code."
  (interactive)
  (indent-line-to (egison-prover-indent-point)))


(defvar egison-prover-mode-map
  (let ((smap (make-sparse-keymap)))
    (define-key smap "\C-j" 'newline-and-indent)
    smap)
  "Keymap for Egison-Prover mode.")


(defvar egison-prover-mode-syntax-table
  (let ((egison-prover-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?< "(>" egison-prover-mode-syntax-table)
    (modify-syntax-entry ?> ")<" egison-prover-mode-syntax-table)
    (modify-syntax-entry ?\; "<" egison-prover-mode-syntax-table)
    (modify-syntax-entry ?\n ">" egison-prover-mode-syntax-table)
    (modify-syntax-entry ?\? "w" egison-prover-mode-syntax-table)
    (modify-syntax-entry ?# ". 14bn" egison-prover-mode-syntax-table)
    ;(modify-syntax-entry ?| ". 23bn" egison-prover-mode-syntax-table)
    egison-prover-mode-syntax-table)
  ;; (copy-syntax-table lisp-mode-syntax-table)
  "Syntax table for Egison-Prover mode")

(defun egison-prover-mode-set-variables ()
  (set-syntax-table egison-prover-mode-syntax-table)
  (set (make-local-variable 'font-lock-defaults)
       '((egison-prover-font-lock-keywords
          egison-prover-font-lock-keywords-1 egison-prover-font-lock-keywords-2)
         nil t (("+-*/=!?%:_~.'∂∇α-ωΑ-Ω" . "w") ("<" . "(") (">" . ")"))
         ))
  (set (make-local-variable 'indent-line-function) 'egison-prover-indent-line)
  (set (make-local-variable 'comment-start) ";")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-start-skip) ";+ *")
  (set (make-local-variable 'comment-add) 1)
  (set (make-local-variable 'comment-end-skip) nil)
  )


;;;###autoload
(defun egison-prover-mode ()
  "Major mode for editing Egison-Prover code.

Commands:
\\{egison-prover-mode-map}
Entry to this mode calls the value of `egison-prover-mode-hook'
if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (setq indent-tabs-mode nil)
  (use-local-map egison-prover-mode-map)
  (setq major-mode 'egison-prover-mode)
  (setq mode-name "Egison-Prover")
  (egison-prover-mode-set-variables)
  (run-mode-hooks 'egison-prover-mode-hook))


(defgroup egison-prover nil
  "Editing Egison-Prover code."
  :link '(custom-group-link :tag "Font Lock Faces group" font-lock-faces)
  :group 'lisp)

(defcustom egison-prover-mode-hook nil
  "Normal hook run when entering `egison-prover-mode'.
See `run-hooks'."
  :type 'hook
  :group 'egison-prover)

(provide 'egison-prover-mode)

;;; egison-prover-mode.el ends here
