;; Thermostat SMT without ODE
(set-option :print-success false)

(set-logic QF_UFLRA)
(define-sort Int () Real)

;(set-logic AUFLIRA)

(define-fun off () Int 0)
(define-fun on () Int 1)

(define-fun jump ((mode Int) (mode_new Int) (x Real)) Bool (or
  (and (= mode off) (= mode_new off) (> x 73.0))
  (and (= mode off) (= mode_new on) (<= x 73.0))
  (and (= mode on) (= mode_new on) (< x 77.0))
  (and (= mode on) (= mode_new off) (>= x 77.0))
))

(define-fun mode_0 () Int off)

(declare-fun mode_1 () Int)
(declare-fun mode_2 () Int)
(declare-fun mode_3 () Int)
(declare-fun mode_4 () Int)
(declare-fun mode_5 () Int)
(declare-fun mode_6 () Int)
(declare-fun mode_7 () Int)
(declare-fun mode_8 () Int)
(declare-fun mode_9 () Int)
(declare-fun mode_10 () Int)
(declare-fun mode_11 () Int)
(declare-fun mode_12 () Int)

(define-fun x_1 () Real 25.0)
(define-fun x_2 () Real 45.0)
(define-fun x_3 () Real 55.0)
(define-fun x_4 () Real 65.0)
(define-fun x_5 () Real 70.0)
(define-fun x_6 () Real 72.5)
(define-fun x_7 () Real 73.0)
(define-fun x_8 () Real 74.0)
(define-fun x_9 () Real 77.0)
(define-fun x_10 () Real 77.5)
(define-fun x_11 () Real 75.0)
(define-fun x_12 () Real 73.0)

(assert (and
  (jump mode_0 mode_1 x_1)
  (jump mode_1 mode_2 x_2)
  (jump mode_2 mode_3 x_3)
  (jump mode_3 mode_4 x_4)
  (jump mode_4 mode_5 x_5)
  (jump mode_5 mode_6 x_6)
  (jump mode_6 mode_7 x_7)
  (jump mode_7 mode_8 x_8)
  (jump mode_8 mode_9 x_9)
  (jump mode_9 mode_10 x_10)
  (jump mode_10 mode_11 x_11)
  (jump mode_11 mode_12 x_12)
))

(check-sat)

(exit)
