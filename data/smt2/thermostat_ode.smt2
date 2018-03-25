;;;; Thermostat in SMT format with ODE simulation

(set-option :print-success false)
(set-option :produce-models true)
;(set-logic QF_UFLRA)
(set-logic QF_UFNRA)

;;; Constants

(define-fun t0 () Real 0.0)
(define-fun x0 () Real 60.0)
(define-fun on0 () Bool false)

(define-fun T () Real 0.25)

;;; Declarations

(declare-fun t_0 () Real)
(declare-fun t_1 () Real)
(declare-fun t_2 () Real)
(declare-fun t_3 () Real)
(declare-fun t_4 () Real)
(declare-fun t_5 () Real)
(declare-fun t_6 () Real)
(declare-fun t_7 () Real)
(declare-fun t_8 () Real)
(declare-fun t_9 () Real)

(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)

(declare-fun on_0 () Bool)
(declare-fun on_1 () Bool)
(declare-fun on_2 () Bool)
(declare-fun on_3 () Bool)
(declare-fun on_4 () Bool)
(declare-fun on_5 () Bool)
(declare-fun on_6 () Bool)
(declare-fun on_7 () Bool)
(declare-fun on_8 () Bool)
(declare-fun on_9 () Bool)

(declare-fun dx_0 () Real)
(declare-fun dx_1 () Real)
(declare-fun dx_2 () Real)
(declare-fun dx_3 () Real)
(declare-fun dx_4 () Real)
(declare-fun dx_5 () Real)
(declare-fun dx_6 () Real)
(declare-fun dx_7 () Real)
(declare-fun dx_8 () Real)

;;; Initializations

(assert (and (= t_0 t0) (= x_0 x0) (= on_0 on0)))

;;; Steps definition

(assert (and (= t_1 (+ t_0 T))
             (= t_2 (+ t_1 T))
             (= t_3 (+ t_2 T))
             (= t_4 (+ t_3 T))
             (= t_5 (+ t_4 T))
             (= t_6 (+ t_5 T))
             (= t_7 (+ t_6 T))
             (= t_8 (+ t_7 T))
             (= t_9 (+ t_8 T))
))

;;; Derivatives definition

;(define-dt dx_on  x (- 100.0 x))
;(define-dt dx_off x (-  50.0 x))
(define-fun dx_on  () Real 1.0)
(define-fun dx_off () Real 0.0)

;;; Derivatives connection

(declare-fun dt-int (Real Real Real Real) Real)

(define-fun connect ((on1 Bool) (dx1 Real)
                     (t1 Real)  (t2 Real)
                     (x1 Real)  (x2 Real)) Bool
    (and (or (and      on1  (= dx1 dx_on ))
             (and (not on1) (= dx1 dx_off)) )
         (= x2 (dt-int dx1 t1 t2 x1))
    )
)

(assert (and (connect on_0 dx_0 t_0 t_1 x_0 x_1)
             (connect on_1 dx_1 t_1 t_2 x_1 x_2)
             (connect on_2 dx_2 t_2 t_3 x_2 x_3)
             (connect on_3 dx_3 t_3 t_4 x_3 x_4)
             (connect on_4 dx_4 t_4 t_5 x_4 x_5)
             (connect on_5 dx_5 t_5 t_6 x_5 x_6)
             (connect on_6 dx_6 t_6 t_7 x_6 x_7)
             (connect on_7 dx_7 t_7 t_8 x_7 x_8)
             (connect on_8 dx_8 t_8 t_9 x_8 x_9)
))

;;; Jump conditions

(define-fun jump ((on1 Bool) (on2 Bool) (x2 Real)) Bool
    (or (and      on1       on2  (<  x2 77.0))
        (and      on1  (not on2) (>= x2 77.0))
        (and (not on1) (not on2) (>  x2 73.0))
        (and (not on1)      on2  (<= x2 73.0)) )
)

(assert (and (jump on_0 on_1 x_1)
             (jump on_1 on_2 x_2)
             (jump on_2 on_3 x_3)
             (jump on_3 on_4 x_4)
             (jump on_4 on_5 x_5)
             (jump on_5 on_6 x_6)
             (jump on_6 on_7 x_7)
             (jump on_7 on_8 x_8)
             (jump on_8 on_9 x_9)
))

;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ODE simulation functions

(define-fun e^-t ((t Real)) Real
    (+ 1 (- t)
       (/    (* t t)            2.0)
       (/ (- (* t t t))         6.0)
       (/    (* t t t t)       24.0)
;      (/ (- (* t t t t t))   120.0)
;      (/    (* t t t t t t)  720.0)
    )
)

(define-fun eval-dx ((dx1 Real) (t1 Real) (t2 Real) (x1 Real)) Real
(let ((C (ite (= dx1 dx_on) 100.0 50.0)))
    (- C (* (- C x1) (e^-t (- t2 t1)) ) )
))

;;; Additional assertions

(assert (= (dt-int dx_0 t_0 t_1 x_0) (eval-dx dx_0 t_0 t_1 x_0)))
(assert (= (dt-int dx_1 t_1 t_2 x_1) (eval-dx dx_1 t_1 t_2 x_1)))
(assert (= (dt-int dx_2 t_2 t_3 x_2) (eval-dx dx_2 t_2 t_3 x_2)))
(assert (= (dt-int dx_3 t_3 t_4 x_3) (eval-dx dx_3 t_3 t_4 x_3)))
(assert (= (dt-int dx_4 t_4 t_5 x_4) (eval-dx dx_4 t_4 t_5 x_4)))
(assert (= (dt-int dx_5 t_5 t_6 x_5) (eval-dx dx_5 t_5 t_6 x_5)))
(assert (= (dt-int dx_6 t_6 t_7 x_6) (eval-dx dx_6 t_6 t_7 x_6)))
(assert (= (dt-int dx_7 t_7 t_8 x_7) (eval-dx dx_7 t_7 t_8 x_7)))
(assert (= (dt-int dx_8 t_8 t_9 x_8) (eval-dx dx_8 t_8 t_9 x_8)))

;;; Evaluation

(check-sat)

(get-model)

; 60
(get-value (x_0))
; 53.679
(get-value (x_1))
; 82.959
(get-value (x_2))
; 62.125
(get-value (x_3))
; 86.065
(get-value (x_4))
; 63.266
(get-value (x_5))
(get-value (x_6))
(get-value (x_7))
(get-value (x_8))
(get-value (x_9))

(exit)
