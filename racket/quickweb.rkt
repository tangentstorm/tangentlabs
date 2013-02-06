#lang racket
;; http://docs.racket-lang.org/more/

(require xml net/url racket/control)

(define (serve port-no)
  (define main-cust (make-custodian))
  (parameterize ([current-custodian main-cust])
    (define listener (tcp-listen port-no 5 #t))
    (define (loop)
      (accept-and-handle listener)
      (loop))
    (thread loop))
  (lambda ()
    (custodian-shutdown-all main-cust)))

(define (accept-and-handle listener)
  (define cust (make-custodian))
  (custodian-limit-memory cust (* 50 1024 1024))
  (parameterize ([current-custodian cust])
    (define-values (in out) (tcp-accept listener))
    (thread
     (lambda ()
       (handle in out)
       (close-input-port in)
       (close-output-port out))))
    ; watcher thread
    (thread (lambda ()
              (sleep 10)
              (custodian-shutdown-all cust))))
  
  
(define (handle in out)
  (define req
    ; discard request header up to blank line
    (regexp-match #rx"^GET (.+) HTTP/[0-9]+\\.[0-9]+"
                  (read-line in)))
  (when req
    ; discard rest of the header (up to blank line):
    (regexp-match #rx"(\r\n|^)\r\n" in)
    ; dispatch:
    (let ([xexpr (prompt (dispatch (list-ref req 1)))])
      ; send reply:
      (display "HTTP/1.0 200 Okay\r\n" out)
      (display "Server: k\r\nContent-Type: text/html\r\n\r\n" out)
      (display (xexpr->string xexpr) out))))



(define (dispatch str-path)
  ; parse the request as a URL
  (define url (string->url str-path))
  ; extract the path part:
  (define path (map path/param-path (url-path url)))
  ; find a handler based on the path's first element:
  (define h (hash-ref dispatch-table (car path) #f))
  (if h
      ; call a handler:
      (h (url-query url))
      ; no handler found:
      `(html (head (title "error"))
             (body
              (font ((color "red"))
                    "unknown page: " ,str-path)))))


(define (build-request-page label next-url hidden)
  `(html
    (head (title "enter a number to add"))
    (body ()
          (form ([action ,next-url] [method "get"])
                 (label ,label)
                 (input ([type "text"] [name "number"]
                                       [value ""]))
                 (input ([type "hidden"] [name "hidden"]
                                         [value ,hidden]))
                 (input ([type "submit"] [name "enter"]
                                         [value "enter"]))))))


(define (many query)
  (build-request-page "number of greetings:" "/reply" ""))

(define (reply query)
  (define n (string->number (cdr (assq 'number query))))
  `(html (body ,@(for/list ([i (in-range n)])
                   " hello"))))




;; non-continuation example
(define (sum query)
  (build-request-page "first number:" "/one" ""))

(define (one query)
  (build-request-page "second number:" "/two"
                      (cdr (assq 'number query))))

(define (two query)
  (let ([n (string->number (cdr (assq 'hidden query)))]
        [m (string->number (cdr (assq 'number query)))])
    `(html (body "the sum is " ,(number->string (+ m n))))))


;; continuation version
(define (sum2 query)
  (define m (get-number "first number:"))
  (define n (get-number "second number:"))
  `(html (body "the sum is " ,(number->string (+ m n)))))


(define (get-number label)
  (define query
    ; generate a url for the current computation:
    (send/suspend
     ; receive the computation-as-url here:
     (lambda (k-url)
       ; generate the query-page result for this connection.
       ; send the query result to the saved-computation url:
       (build-request-page label k-url ""))))
  ; we arrive here later, in a new connection
  (string->number (cdr (assq 'number query))))



(define (send/suspend mk-page)
  (let/cc k
    (define tag (format "k~a" (current-inexact-milliseconds)))
    (hash-set! dispatch-table tag k)
    (abort (mk-page (string-append "/" tag)))))


;; url map
(define dispatch-table (make-hash))
(hash-set! dispatch-table "many" many)
(hash-set! dispatch-table "reply" reply)
(hash-set! dispatch-table "sum" sum)
(hash-set! dispatch-table "one" one)
(hash-set! dispatch-table "two" two)
(hash-set! dispatch-table "sum2" sum2)

;; run the server on port 8081
(define stop (serve 8081))