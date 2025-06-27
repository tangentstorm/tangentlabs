#lang racket

(require sdl2 ffi/unsafe)

(define NUM-STARS 200)
(define STAR-SPEED 2)
(define SCREEN-WIDTH 1366)
(define SCREEN-HEIGHT 768)
(define current-char #\space)

; Dvorak key mapping for common letters
(define dvorak-map
  (hash 'SDLK_q #\' 'SDLK_w #\, 'SDLK_e #\. 'SDLK_r #\p 'SDLK_t #\y
        'SDLK_y #\f 'SDLK_u #\g 'SDLK_i #\c 'SDLK_o #\r 'SDLK_p #\l
        'SDLK_a #\a 'SDLK_s #\o 'SDLK_d #\e 'SDLK_f #\u 'SDLK_g #\i
        'SDLK_h #\d 'SDLK_j #\h 'SDLK_k #\t 'SDLK_l #\n 'SDLK_SEMICOLON #\s
        'SDLK_z #\; 'SDLK_x #\q 'SDLK_c #\j 'SDLK_v #\k 'SDLK_b #\x
        'SDLK_n #\b 'SDLK_m #\m 'SDLK_COMMA #\w 'SDLK_PERIOD #\v 'SDLK_SLASH #\z))

(struct star (x y z) #:mutable)

(define stars
  (for/list ([i NUM-STARS])
    (star (random SCREEN-WIDTH)
          (random SCREEN-HEIGHT)
          (+ 1 (random 100)))))

(define (update-star! s)
  (set-star-z! s (- (star-z s) STAR-SPEED))
  (when (<= (star-z s) 0)
    (set-star-x! s (random SCREEN-WIDTH))
    (set-star-y! s (random SCREEN-HEIGHT))
    (set-star-z! s 100)))

(define (draw-star renderer s)
  (let* ([x (star-x s)]
         [y (star-y s)]
         [z (star-z s)]
         [screen-x (inexact->exact
                    (round (+ (/ SCREEN-WIDTH 2)
                              (* (- x (/ SCREEN-WIDTH 2)) (/ 100 z)))))]
         [screen-y (inexact->exact
                    (round (+ (/ SCREEN-HEIGHT 2)
                              (* (- y (/ SCREEN-HEIGHT 2)) (/ 100 z)))))]
         [brightness (inexact->exact (round (* 255 (/ (- 100 z) 100))))]
         [size (max 1 (inexact->exact (round (/ (- 100 z) 25))))])

    (when (and (>= screen-x 0) (< screen-x SCREEN-WIDTH)
               (>= screen-y 0) (< screen-y SCREEN-HEIGHT))
      (SDL_SetRenderDrawColor renderer brightness brightness brightness 255)
      ; Draw multiple points to make bigger stars
      (for* ([dx (in-range (- size) (+ size 1))]
             [dy (in-range (- size) (+ size 1))])
        (let ([px (+ screen-x dx)]
              [py (+ screen-y dy)])
          (when (and (>= px 0) (< px SCREEN-WIDTH)
                     (>= py 0) (< py SCREEN-HEIGHT))
            (SDL_RenderDrawPoint renderer px py)))))))

; Load VGA font data
(define vga-font-data
  (call-with-input-file "ibmvga437.fnt"
    (lambda (port)
      (read-bytes (* 256 16) port))))

(define (draw-char renderer char x y)
  (SDL_SetRenderDrawColor renderer 255 255 255 255) ; White
  (define char-code (char->integer char))
  (define size 3) ; Scale factor
  (define font-offset (* char-code 16)) ; 16 bytes per character

  ; Draw the 8x16 character bitmap
  (for ([row (in-range 16)])
    (define byte-val (bytes-ref vga-font-data (+ font-offset row)))
    (for ([bit (in-range 8)])
      (when (bitwise-bit-set? byte-val (- 7 bit)) ; MSB is leftmost pixel
        (for* ([dx (in-range size)]
               [dy (in-range size)])
          (SDL_RenderDrawPoint renderer
                               (+ x (* bit size) dx (- (* 4 size))) ; Center horizontally
                               (+ y (* row size) dy (- (* 8 size)))))))))

(define (run-starfield)
  (define event-ptr (cast (malloc (ctype-sizeof _SDL_Event)) _pointer _SDL_Event*))
  (SDL_Init 'SDL_INIT_VIDEO)

  (let* ([window (SDL_CreateWindow "Starfield Demo"
                                   SDL_WINDOWPOS_CENTERED SDL_WINDOWPOS_CENTERED
                                   SCREEN-WIDTH SCREEN-HEIGHT
                                   '(SDL_WINDOW_FULLSCREEN))]
         [renderer (SDL_CreateRenderer window -1 '())])

    (printf "Starfield Demo - Screen: ~ax~a - Type keys to change character\n" SCREEN-WIDTH SCREEN-HEIGHT)
    (SDL_StartTextInput)

    (let loop ([frames 0])
      (when (< frames 600) ; Run for 10 seconds at 60fps


        ; Handle keyboard events
        (unless (zero? (SDL_PollEvent event-ptr))
          (define event (ptr-ref event-ptr _SDL_Event))
          (case (union-ref event 0)
            [(SDL_KEYDOWN)
             (case (SDL_Keysym-sym
                    (SDL_KeyboardEvent-keysym
                     (union-ref event 4)))
               [(SDLK_ESCAPE) (set! frames 999)]
               [(SDLK_SPACE) (set! current-char #\space)]
               [else
                (let ([key-char (SDL_GetKeyName (SDL_Keysym-sym
                                               (SDL_KeyboardEvent-keysym
                                                (union-ref event 4))))])
                  (when (and (string? key-char)
                             (= (string-length key-char) 1))
                    (let ([ch (string-ref key-char 0)])
                      (cond
                        [(char-alphabetic? ch) (set! current-char (char-upcase ch))]
                        [(char-numeric? ch) (set! current-char ch)]
                        [(char? ch) (set! current-char ch)]))))])]
            [(SDL_QUIT) (set! frames 999)]))

        ; Clear screen (black)
        (SDL_SetRenderDrawColor renderer 0 0 0 255)
        (SDL_RenderClear renderer)

        ; Update and draw stars
        (for-each (lambda (s)
                    (update-star! s)
                    (draw-star renderer s))
                  stars)

        ; Draw character in center (simple bitmap)
        (draw-char renderer current-char (/ SCREEN-WIDTH 2) (/ SCREEN-HEIGHT 2))

        ; Present the rendered frame
        (SDL_RenderPresent renderer)

        ; Small delay for ~60 FPS
        (SDL_Delay 16)

        (loop (+ frames 1))))

    (SDL_DestroyRenderer renderer)
    (SDL_DestroyWindow window)
    (SDL_Quit)))

(run-starfield)
