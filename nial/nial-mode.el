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

(defface nial-punctuation-face
  '((default (:foreground "magenta" )))
  "Face for punctuation.")
(defvar nial-punctuation-face 'nial-punctuation-face
  "Face for punctuation.")



(defconst nial-font-lock-keywords
  (list

   ; keywords
   (cons (make-optre
	  '("is" "gets" "op" "tr"  ";"
	    "if" "then" "elseif" "else" "endif"
	    "case"  "from" "endcase"
	    "begin" "end"
	    "for"  "with" "endfor"
	    "while" "do" "endwhile"
	    "repeat" "until" "endrepeat"))
	 font-lock-keyword-face)

   ; punctuation
   (cons (make-optre '(":="))
	 'nial-punctuation-face)

   ; operators
   (cons (make-optre
	  '("." "(" "!" "#" ")" "," "+" "*" "-" "<<"
	    "/" "<" ">>" "<=" ">" "=" ">=" "@" "["
	    "]" "{" "}" "|" "~=" ))
	 font-lock-builtin-face)

   ; symbols
   (cons "\"[[:word:]]+"
	 font-lock-constant-face)

   ; predefined words
   (cons (make-optre '(
	 "operation" "expression"
	 "and" "abs" "allbools" "accumulate" "across" "allints"
	 "allchars" "allin" "allreals" "allnumeric" "append"
	 "arcsin" "arccos" "appendfile" "apply" "arctan" "atomic"
	 "assign" "atversion" "axes" "cart" "bykey" "break" "blend"
	 "breaklist" "breakin" "bye" "bycols" "callstack" "byrows"
	 "choose" "char" "ceiling" "catenate" "charrep" "check_socket"
	 "cos" "content" "close" "clearws" "clearprofile" "cols"
	 "converse" "continue" "copyright" "cosh" "cull" "count"
	 "diverse" "deepplace" "cutall" "cut" "display" "deparse"
	 "deepupdate" "descan" "depth" "diagram" "div" "divide"
	 "drop" "down" "eachboth" "eachall" "each" "dropright"
	 "eachleft" "eachright" "edit"
	 "empty" "expression" "exit"
	 "except" "erase" "equal" "eval" "eraserecord" "execute"
	 "exp" "external" "exprs" "findall" "find" "false" "fault"
	 "falsehood" "filestatus" "filelength" "filepath" "filetally"
	 "filter" "floor" "first" "flip" "fold" "from" "fork" "fuse"
	 "fromraw" "front" "gage" "getfile" "getdef" "getcommandline"
	 "getenv" "getname" "hitch" "grid" "grade" "getsyms" "gradeup"
	 "gt" "gte" "host" "in" "inverse" "innerproduct" "inner" "inv"
	 "ip" "ln" "link" "isboolean" "isinteger" "ischar" "isfault"
         "isreal" "isphrase" "isstring" "iterate" "istruthvalue" "leaf"
         "last" "laminate" "like" "libpath" "library" "list" "load"
         "loaddefs" "nonlocal" "max" "match" "log" "lt" "lower" "lte"
	 "mate" "min" "maxlength" "mod" "mix" "minus" "nialroot" "mold"
	 "not" "numeric" "null" "no_op" "no_expr" "notin" "no_tr"
	 "operation" "open" "or" "opposite" "opp" "ops" "plus" "pick"
	 "pack" "outer" "pass" "pair" "parse" "partition" "paste"
	 "phrase" "pi" "place" "picture" "placeall" "power" "positions"
	 "post" "quotient" "putfile" "profile" "prod" "product"
	 "profiletree" "profiletable" "quiet_fault" "raise" "reach"
	 "random" "rank" "reciprocal" "read" "readfile" "readchar"
	 "readarray" "readfield" "readscreen" "readrecord" "recip"
	 "reduce" "recur" "reducerows" "reducecols" "reshape" "seek"
	 "second" "rest" "reverse" "restart" "return_status" "scan"
	 "save" "rows" "rotate" "seed" "see" "sublist" "sin" "simple"
	 "shape" "setformat" "setdeftrace" "set" "seeusercalls"
	 "seeprimcalls" "separator" "setwidth" "settrigger" "setmessages"
	 "setlogname" "setinterrupts" "setprompt" "setprofile" "sinh"
	 "single" "sqrt" "solitary" "sketch" "sleep" "socket_listen"
	 "socket_accept" "socket_close" "socket_bind"
	 "socket_connect" "socket_getline" "socket_receive"
	 "socket_peek" "socket_read" "socket_send" "socket_write"
	 "solve" "sort" "split" "sortup" "string" "status" "take"
	 "symbols" "sum" "system" "tan" "tally" "takeright" "tanh"
	 "tell" "team" "tr" "times" "third" "time"
	 "timeit" "toupper" "tolower" "timestamp" "tonumber"
	 "toraw" "toplevel" "transformer" "type" "transpose"
	 "true" "trs" "twig" "truth" "unequal" "variable"
	 "valence" "up" "updateall" "update" "vacate" "value"
	 "version" "vars" "watchlist" "watch" "void"
	 "write" "writechars" "writearray" "writefile"
	 "writefield" "writescreen" "writerecord"
	 )) font-lock-function-name-face)

   ) "highlighting for nial mode")


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
	  (setq cur-indent (+ (current-indentation) nial-indent)))))))


; syntax table
(defun nial-update-syntax-table (group chars)
  (mapcar (lambda (c) (modify-syntax-entry c group nial-mode-syntax-table))
	  chars))

(defvar nial-mode-syntax-table
  (let ((nial-mode-syntax-table (make-syntax-table)))

    ; underscores okay in names
    (modify-syntax-entry ?_ "w" nial-mode-syntax-table)

    ;; Add operator symbols misassigned in the std table
    (nial-update-syntax-table "w"
	'(?& ?: ?* ?+ ?- ?/ ?< ?= ?> ?| ?~))

    ; comments
    (modify-syntax-entry ?% "<" nial-mode-syntax-table)
    (modify-syntax-entry ?# "<" nial-mode-syntax-table)
    (modify-syntax-entry ?\n ">" nial-mode-syntax-table)

    ; ' starts a string
    (modify-syntax-entry ?' "\"" nial-mode-syntax-table)

    ; " represents a symbol
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
