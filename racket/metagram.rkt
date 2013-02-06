#lang racket
;;
;; this is a metagrammar for my grammar files
;;

;; top level introduces the language:
'(> grammar ebnf
    
    ;; grammars are lists composed of term-pattern definitions
    (= definition
       (: '= term pattern))
    
    ;; patterns are either atomic or higher-order
    (= pattern
       (| atom-pattern
          list-pattern))
    
    (= atom-pattern
       (| TERM
          LITERAL))
    
    ;; @TODO How do I express the fact that lists are already lists?
    ;; ebnf deals with one flat stream but in lisp you've already got a tree
    ;; and you can't match on the parentheses
    (= list-pattern
       (| one-or-more
          zero-or-more
          ;; exactly-n 
          any-from-list
          any-from-string
          maybe
          not))
    
    (= one-or-more 
       (: '+ pattern))
    
    (= zero-or-more
       (: '* pattern))

    ;; (= exactly-n
    ;;    (: '# int pattern))
    ;; (= INT
    ;;    (+ ($ "0123456789")))
    
    (= any-from-list
       (: '| (+ pattern)))
    
    (= any-from-string
       (: '$ string))
    
    (= maybe
       (: '? pattern))
    
    (= not
       (: '~ pattern)))
