#lang br
(require jsonic/parser
         jsonic/tokenizer
         brag/support
         rackunit)

(check-equal?
 (parse-to-datum
  (apply-tokenizer-maker make-tokenizer "// line commment\n"))
 '(jsonic-program))

(check-equal?
 (parse-to-datum
  (apply-tokenizer-maker make-tokenizer "@$ 42 $@"))
 '(jsonic-program (jsonic-sexp " 42 ")))

(check-equal?
 (parse-to-datum
  (apply-tokenizer-maker make-tokenizer "hi"))
 '(jsonic-program
   (jsonic-char "h")
   (jsonic-char "i")))

(check-equal?
 (parse-to-datum
  (apply-tokenizer-maker make-tokenizer
                         "hi\n// comment\n@$ 42 $@"))
 '(jsonic-program
   (jsonic-char "h")
   (jsonic-char "i")
   (jsonic-char "\n")
   (jsonic-sexp " 42 ")))