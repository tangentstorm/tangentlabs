#lang racket
;
; This program demonstrates how to use the graph features of the
; racket GUI
;
; Ref:  http://docs.racket-lang.org/mrlib/Graphs.html
;
(require racket/gui/base)
(require mrlib/graph)

;; this is our model:
(define box% (graph-snip-mixin string-snip%))
(define a (make-object box% "A"))
(define b (make-object box% "B"))
(define c (make-object box% "C"))
(add-links a b)
(add-links b c)
(add-links c a)

;; the graph editor does all the magic:
(define graph-editor% (graph-pasteboard-mixin pasteboard%))
(define graph-ed
    (new graph-editor%
         [cache-arrow-drawing? #f]))

(send* graph-ed
  (insert a 5 5)
  (insert b 105 5)
  (insert c 55 75))


;; the frame and canvas just display the graph editor
(define frame (new frame% [label "hello world"]))
(send* frame
  (move 800 0)
  (show #t))

(define canvas (new editor-canvas% 
                    [parent frame]
                    [editor graph-ed]
                    [min-width 500]
                    [min-height 300]))
