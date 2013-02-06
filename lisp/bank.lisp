
(defgeneric withdraw (account amount)
  (:documentation "withdraw the specified amount from the account.
     signal an error if the current balance is less than amount"))


(defmethod withdraw ((account bank-account) amount)
  (when (< (balance account) amount)
    (error "account overdrawn"))
  (decf (balance account) amount))


(defmethod withdraw ((account checking-account) amount)
  (let ((overdraft (- amount (balance account))))
    (when (plusp overdraft)
      (withdraw (overdraft-account account) overdraft)
      (incf (balance account) overdraft)))
  (call-next-method))


(defvar *account-numbers* 0)

(defclass bank-account ()
  ((customer-name
    :initarg :customer-name)
   (balance
    :initarg :balance
    :initform 0)
   (account-number
    :initform (incf *account-numbers*))))


(defgeneric balance (account))
(defmethod balance ((account bank-account))
  (slot-value account 'balance))

(defgeneric (setf customer-name) (value account))
(defmethod (setf customer-name) (value (account bank-account))
  (setf (slot-value account 'customer-name) value))

;----
