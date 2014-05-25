;;; nial-mode.el --- nial mode for emacs

; a simple mode for editing scarlet files
; based on tutorial from:
; http://www.emacswiki.org/emacs/ModeTutorial

;;; Commentary:
;; 

;;; History:
;; 

;;; Code:

(defvar nial-mode-hook nil)

(defvar nial-mode-map (make-keymap)
  "keymap for nial mode")

(add-to-list 'auto-mode-alist '("\\.ndf\\'" . nial-mode))

(defun make-optre (words)
  (concat "\\<" (regexp-opt words t) "\\>"))

(defconst nial-font-lock-keywords
  (list

   ; keywords
   (cons (make-optre '("if" "else" "elseif" "end" "endif" "then" "case" "from"))
	 font-lock-keyword-face)
   


   ; predefined words
   (cons (make-optre '(":=" "<" ">" "is" ))
	 font-lock-function-name-face)

   ; predefined words
   (cons (make-optre '("op" "tr" "ex"))
	 font-lock-builtin-face))

  "highlighting for nial mode")


(defvar nial-indent 4)

; @TODO: define logic for un-indenting!
(defun nial-indent-line ()
  "indent current line as nial code"
  (interactive)
  (beginning-of-line)
  (if (bobp)
      (indent-line-to 0) ; beginning of buffer
    (let ((not-indented t) cur-indent)
      (progn
	(save-excursion
	  (forward-line -1)
	  (if (looking-at ".*:$")
	      (setq cur-indent (+ (current-indentation) nial-indent))))))))




; syntax table
(defvar nial-mode-syntax-table
  (let ((nial-mode-syntax-table (make-syntax-table)))

    ; underscores okay
    (modify-syntax-entry ?_ "w" nial-mode-syntax-table)

  ;; Add operator symbols misassigned in the std table
    (modify-syntax-entry ?\$ "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\% "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\& "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\* "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\+ "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\- "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\/ "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\< "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\= "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\> "."  nial-mode-syntax-table)
    (modify-syntax-entry ?\| "."  nial-mode-syntax-table)
  
    ; comments
    (modify-syntax-entry ?% "<" nial-mode-syntax-table)
    (modify-syntax-entry ?\n ">" nial-mode-syntax-table)

    ; strings and symbols
    (modify-syntax-entry ?' "\"" nial-mode-syntax-table)
    (modify-syntax-entry ?\" "'" nial-mode-syntax-table)
    
    nial-mode-syntax-table)
  "syntax table for nial-mode")

(defun nial-mode ()
  "major mode for nial"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table nial-mode-syntax-table)
  (use-local-map nial-mode-map)
  (set (make-local-variable 'font-lock-defaults)  '(nial-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'nial-indent-line)
  (setq major-mode 'nial-mode)
  (setq mode-name "Nial")
  (run-hooks 'nial-mode-hook))


(provide 'nial-mode)

;;; nial-mode.el ends here
