;;;; Thermostat in SMT format with ODEs not yet interpreted

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

(declare-fun _dx_0 () Real)
(declare-fun _dx_1 () Real)
(declare-fun _dx_2 () Real)
(declare-fun _dx_3 () Real)
(declare-fun _dx_4 () Real)
(declare-fun _dx_5 () Real)
(declare-fun _dx_6 () Real)
(declare-fun _dx_7 () Real)
(declare-fun _dx_8 () Real)

(declare-fun _dx_0_int () Real)
(declare-fun _dx_1_int () Real)
(declare-fun _dx_2_int () Real)
(declare-fun _dx_3_int () Real)
(declare-fun _dx_4_int () Real)
(declare-fun _dx_5_int () Real)
(declare-fun _dx_6_int () Real)
(declare-fun _dx_7_int () Real)
(declare-fun _dx_8_int () Real)

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

;;; Derivatives declaration and definition

;(declare-ode x ((dx_on mode_on) (dx_off mode_off)))

;(define-dt dx_on  (- 100.0 x))
;(define-dt dx_off (-  50.0 x))
(define-fun _dx_on  () Real 1.0)
(define-fun _dx_off () Real 0.0)

(define-fun mode_on  ((on Bool)) Bool on)
(define-fun mode_off ((on Bool)) Bool (not on))

(define-fun _connect ((dx Real) (on Bool)) Bool
    (or (and (mode_on  on) (= dx _dx_on))
        (and (mode_off on) (= dx _dx_off)))
)

;;; Integration

;(int-ode x (t_0 t_1) (x_0 x_1) (on_0))
;(int-ode x (t_1 t_2) (x_1 x_2) (on_1))
;(int-ode x (t_2 t_3) (x_2 x_3) (on_2))
;(int-ode x (t_3 t_4) (x_3 x_4) (on_3))
;(int-ode x (t_4 t_5) (x_4 x_5) (on_4))
;(int-ode x (t_5 t_6) (x_5 x_6) (on_5))
;(int-ode x (t_6 t_7) (x_6 x_7) (on_6))
;(int-ode x (t_7 t_8) (x_7 x_8) (on_7))
;(int-ode x (t_8 t_9) (x_8 x_9) (on_8))

(assert (and (_connect _dx_0 on_0)
             (_connect _dx_1 on_1)
             (_connect _dx_2 on_2)
             (_connect _dx_3 on_3)
             (_connect _dx_4 on_4)
             (_connect _dx_5 on_5)
             (_connect _dx_6 on_6)
             (_connect _dx_7 on_7)
             (_connect _dx_8 on_8)
))

(assert (and (= x_1 _dx_0_int)
             (= x_2 _dx_1_int)
             (= x_3 _dx_2_int)
             (= x_4 _dx_3_int)
             (= x_5 _dx_4_int)
             (= x_6 _dx_5_int)
             (= x_7 _dx_6_int)
             (= x_8 _dx_7_int)
             (= x_9 _dx_8_int)
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
