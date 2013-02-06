
(define-condition malformed-log-entry-error (error)
  ((text :initarg :text :reader text)))


(defun parse-log-file (file)
  (with-open-file (in file :direction :input)
    (loop for text = (read-line in nil nil) while text
	  for entry = (restart-case (parse-log-entry text)
			(skip-log-entry () nil))
	  when entry collect it)))
