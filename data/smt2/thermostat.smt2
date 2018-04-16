(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_UFNRA)
(define-sort Dt () Real)
( define-fun t0 ( ) Real 0 )
( define-fun x0 ( ) Real 60 )
( define-fun on0 ( ) Bool false )
( define-fun T ( ) Real 0.25 )
( declare-fun t_0 ( ) Real )
( declare-fun t_1 ( ) Real )
( declare-fun t_2 ( ) Real )
( declare-fun t_3 ( ) Real )
( declare-fun t_4 ( ) Real )
( declare-fun t_5 ( ) Real )
( declare-fun t_6 ( ) Real )
( declare-fun t_7 ( ) Real )
( declare-fun t_8 ( ) Real )
( declare-fun t_9 ( ) Real )
( declare-fun x_0 ( ) Real )
( declare-fun x_1 ( ) Real )
( declare-fun x_2 ( ) Real )
( declare-fun x_3 ( ) Real )
( declare-fun x_4 ( ) Real )
( declare-fun x_5 ( ) Real )
( declare-fun x_6 ( ) Real )
( declare-fun x_7 ( ) Real )
( declare-fun x_8 ( ) Real )
( declare-fun x_9 ( ) Real )
( declare-fun on_0 ( ) Bool )
( declare-fun on_1 ( ) Bool )
( declare-fun on_2 ( ) Bool )
( declare-fun on_3 ( ) Bool )
( declare-fun on_4 ( ) Bool )
( declare-fun on_5 ( ) Bool )
( declare-fun on_6 ( ) Bool )
( declare-fun on_7 ( ) Bool )
( declare-fun on_8 ( ) Bool )
( declare-fun on_9 ( ) Bool )
( declare-fun dx_0 ( ) Dt )
( declare-fun dx_1 ( ) Dt )
( declare-fun dx_2 ( ) Dt )
( declare-fun dx_3 ( ) Dt )
( declare-fun dx_4 ( ) Dt )
( declare-fun dx_5 ( ) Dt )
( declare-fun dx_6 ( ) Dt )
( declare-fun dx_7 ( ) Dt )
( declare-fun dx_8 ( ) Dt )
( assert ( and ( = t_0 t0 ) ( = x_0 x0 ) ( = on_0 on0 ) ) )
( assert ( and ( = t_1 ( + t_0 T ) ) ( = t_2 ( + t_1 T ) ) ( = t_3 ( + t_2 T ) ) ( = t_4 ( + t_3 T ) ) ( = t_5 ( + t_4 T ) ) ( = t_6 ( + t_5 T ) ) ( = t_7 ( + t_6 T ) ) ( = t_8 ( + t_7 T ) ) ( = t_9 ( + t_8 T ) ) ) )
( declare-fun int-ode_x ( Real ) Real )
( define-fun dx_on ( ) Dt 0 )
( define-fun dx_off ( ) Dt 1 )
( assert ( and ( = x_1 ( int-ode_x 0 ) ) ( = x_2 ( int-ode_x 1 ) ) ( = x_3 ( int-ode_x 2 ) ) ( = x_4 ( int-ode_x 3 ) ) ( = x_5 ( int-ode_x 4 ) ) ( = x_6 ( int-ode_x 5 ) ) ( = x_7 ( int-ode_x 6 ) ) ( = x_8 ( int-ode_x 7 ) ) ( = x_9 ( int-ode_x 8 ) ) ) )
( define-fun connect ( ( dx Dt ) ( on Bool ) ) Bool ( and ( => on ( = dx dx_on ) ) ( => ( not on ) ( = dx dx_off ) ) ) )
( assert ( and ( connect dx_0 on_0 ) ( connect dx_1 on_1 ) ( connect dx_2 on_2 ) ( connect dx_3 on_3 ) ( connect dx_4 on_4 ) ( connect dx_5 on_5 ) ( connect dx_6 on_6 ) ( connect dx_7 on_7 ) ( connect dx_8 on_8 ) ) )
( define-fun jump ( ( on1 Bool ) ( on2 Bool ) ( x2 Real ) ) Bool ( and ( => ( and on1 ( < x2 77 ) ) on2 ) ( => ( and on1 ( >= x2 77 ) ) ( not on2 ) ) ( => ( and ( not on1 ) ( > x2 73 ) ) ( not on2 ) ) ( => ( and ( not on1 ) ( <= x2 73 ) ) on2 ) ) )
( assert ( and ( jump on_0 on_1 x_1 ) ( jump on_1 on_2 x_2 ) ( jump on_2 on_3 x_3 ) ( jump on_3 on_4 x_4 ) ( jump on_4 on_5 x_5 ) ( jump on_5 on_6 x_6 ) ( jump on_6 on_7 x_7 ) ( jump on_7 on_8 x_8 ) ( jump on_8 on_9 x_9 ) ) )

(check-sat)
(get-value (dx_0))
(get-value (x_0))
(get-value (t_0))
(get-value (t_1))
(assert (=> (and 
(= dx_0 1.0)
(= x_0 60.0)
(= t_0 0.0)
(= t_1 0.25)
) (= (int-ode_x 0) 57.788008)
))
(push 1)
(assert (= dx_0 1.0))
(check-sat)
(get-value (dx_1))
(get-value (x_1))
(get-value (t_1))
(get-value (t_2))
(assert (=> (and 
(= dx_1 0.0)
(= x_1 57.788008)
(= t_1 0.25)
(= t_2 0.5)
) (= (int-ode_x 1) 67.125267)
))
(push 1)
(assert (= dx_1 0.0))
(check-sat)
(get-value (dx_2))
(get-value (x_2))
(get-value (t_2))
(get-value (t_3))
(assert (=> (and 
(= dx_2 0.0)
(= x_2 67.125267)
(= t_2 0.5)
(= t_3 0.75)
) (= (int-ode_x 2) 74.397132)
))
(push 1)
(assert (= dx_2 0.0))
(check-sat)
(get-value (dx_3))
(get-value (x_3))
(get-value (t_3))
(get-value (t_4))
(assert (=> (and 
(= dx_3 0.0)
(= x_3 74.397132)
(= t_3 0.75)
(= t_4 1.0)
) (= (int-ode_x 3) 80.060466)
))
(push 1)
(assert (= dx_3 0.0))
(check-sat)
(get-value (dx_4))
(get-value (x_4))
(get-value (t_4))
(get-value (t_5))
(assert (=> (and 
(= dx_4 1.0)
(= x_4 80.060466)
(= t_4 1.0)
(= t_5 1.25)
) (= (int-ode_x 4) 73.411115)
))
(push 1)
(assert (= dx_4 1.0))
(check-sat)
(get-value (dx_5))
(get-value (x_5))
(get-value (t_5))
(get-value (t_6))
(assert (=> (and 
(= dx_5 1.0)
(= x_5 73.411115)
(= t_5 1.25)
(= t_6 1.5)
) (= (int-ode_x 5) 68.232595)
))
(push 1)
(assert (= dx_5 1.0))
(check-sat)
(get-value (dx_6))
(get-value (x_6))
(get-value (t_6))
(get-value (t_7))
(assert (=> (and 
(= dx_6 0.0)
(= x_6 68.232595)
(= t_6 1.5)
(= t_7 1.75)
) (= (int-ode_x 6) 75.259520)
))
(push 1)
(assert (= dx_6 0.0))
(check-sat)
(get-value (dx_7))
(get-value (x_7))
(get-value (t_7))
(get-value (t_8))
(assert (=> (and 
(= dx_7 0.0)
(= x_7 75.25952)
(= t_7 1.75)
(= t_8 2.0)
) (= (int-ode_x 7) 80.732094)
))
(push 1)
(assert (= dx_7 0.0))
(check-sat)
(get-value (dx_8))
(get-value (x_8))
(get-value (t_8))
(get-value (t_9))
(assert (=> (and 
(= dx_8 1.0)
(= x_8 80.732094)
(= t_8 2.0)
(= t_9 2.25)
) (= (int-ode_x 8) 73.934179)
))
(push 1)
(assert (= dx_8 1.0))
(check-sat)
(get-value (x_0))
(get-value (x_1))
(get-value (x_2))
(get-value (x_3))
(get-value (x_4))
(get-value (x_5))
(get-value (x_6))
(get-value (x_7))
(get-value (x_8))
(get-value (dx_0))
(get-value (dx_1))
(get-value (dx_2))
(get-value (dx_3))
(get-value (dx_4))
(get-value (dx_5))
(get-value (dx_6))
(get-value (dx_7))
(get-value (dx_8))
(exit)
