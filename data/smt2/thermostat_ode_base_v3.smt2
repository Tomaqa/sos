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

(define-sort Dt () Real)
(declare-fun dx_0 () Dt)
(declare-fun dx_1 () Dt)
(declare-fun dx_2 () Dt)
(declare-fun dx_3 () Dt)
(declare-fun dx_4 () Dt)
(declare-fun dx_5 () Dt)
(declare-fun dx_6 () Dt)
(declare-fun dx_7 () Dt)
(declare-fun dx_8 () Dt)

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

;(declare-ode x (dx_on dx_off) ())
;(define-dt dx_on  () (- 100.0 x))
;(define-dt dx_off () (-  50.0 x))
(define-fun dx_on  () Dt 0)
(define-fun dx_off () Dt 1)

;;; Integration

;(assert (and (= x_1 (int-ode x dx_0 (x_0 t_0 t_1) ()))
;             (= x_2 (int-ode x dx_1 (x_1 t_1 t_2) ()))
;             (= x_3 (int-ode x dx_1 (x_1 t_1 t_3) ()))
;             (= x_4 (int-ode x dx_3 (x_3 t_3 t_4) ()))
;             (= x_5 (int-ode x dx_4 (x_4 t_4 t_5) ()))
;             (= x_6 (int-ode x dx_5 (x_5 t_5 t_6) ()))
;             (= x_7 (int-ode x dx_6 (x_6 t_6 t_7) ()))
;             (= x_8 (int-ode x dx_7 (x_7 t_7 t_8) ()))
;             (= x_9 (int-ode x dx_8 (x_8 t_8 t_9) ()))
;))

(declare-fun _dx_0_int () Real)
(declare-fun _dx_1_int () Real)
(declare-fun _dx_2_int () Real)
(declare-fun _dx_3_int () Real)
(declare-fun _dx_4_int () Real)
(declare-fun _dx_5_int () Real)
(declare-fun _dx_6_int () Real)
(declare-fun _dx_7_int () Real)
(declare-fun _dx_8_int () Real)

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

;;; Derivatives connection

(define-fun connect ((dx Dt) (on Bool)) Bool
    (and (=>      on  (= dx dx_on ))
         (=> (not on) (= dx dx_off))
))

(assert (and (connect dx_0 on_0)
             (connect dx_1 on_1)
             (connect dx_2 on_2)
             (connect dx_3 on_3)
             (connect dx_4 on_4)
             (connect dx_5 on_5)
             (connect dx_6 on_6)
             (connect dx_7 on_7)
             (connect dx_8 on_8)
))

;;; Jump conditions

(define-fun jump ((on1 Bool) (on2 Bool) (x2 Real)) Bool
    (and (=> (and      on1  (<  x2 77.0) )      on2  )
         (=> (and      on1  (>= x2 77.0) ) (not on2) )
         (=> (and (not on1) (>  x2 73.0) ) (not on2) )
         (=> (and (not on1) (<= x2 73.0) )      on2  )
))

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
