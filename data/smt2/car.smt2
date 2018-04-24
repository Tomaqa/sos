(set-logic QF_UFLRA)
(set-option :print-success false)
(set-option :produce-models true)
(define-sort Dt () Real)
( define-fun p_lo ( ) Real ( - 1 ) )
( define-fun p_hi ( ) Real 1 )
( define-fun p_min ( ) Real ( - 1.5 ) )
( define-fun t0 ( ) Real 0 )
( define-fun p0 ( ) Real 0 )
( define-fun gam0 ( ) Real 0.15 )
( define-fun c0 ( ) Real 0 )
( define-fun correct0 ( ) Bool false )
( define-fun left0 ( ) Bool false )
( define-fun ahead0 ( ) Bool true )
( define-fun canal0 ( ) Bool false )
( assert ( and ( > p_hi p_lo ) ( < p_min p_lo ) ( >= p0 p_lo ) ( <= p0 p_hi ) ( >= gam0 ( - ( / 3.14159265 4 ) ) ) ( <= gam0 ( / 3.14159265 4 ) ) ) )
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
( declare-fun t_10 ( ) Real )
( declare-fun p_0 ( ) Real )
( declare-fun p_1 ( ) Real )
( declare-fun p_2 ( ) Real )
( declare-fun p_3 ( ) Real )
( declare-fun p_4 ( ) Real )
( declare-fun p_5 ( ) Real )
( declare-fun p_6 ( ) Real )
( declare-fun p_7 ( ) Real )
( declare-fun p_8 ( ) Real )
( declare-fun p_9 ( ) Real )
( declare-fun p_10 ( ) Real )
( declare-fun gam_0 ( ) Real )
( declare-fun gam_1 ( ) Real )
( declare-fun gam_2 ( ) Real )
( declare-fun gam_3 ( ) Real )
( declare-fun gam_4 ( ) Real )
( declare-fun gam_5 ( ) Real )
( declare-fun gam_6 ( ) Real )
( declare-fun gam_7 ( ) Real )
( declare-fun gam_8 ( ) Real )
( declare-fun gam_9 ( ) Real )
( declare-fun gam_10 ( ) Real )
( declare-fun c_1_0 ( ) Real )
( declare-fun c_1_1 ( ) Real )
( declare-fun c_1_2 ( ) Real )
( declare-fun c_1_3 ( ) Real )
( declare-fun c_1_4 ( ) Real )
( declare-fun c_1_5 ( ) Real )
( declare-fun c_1_6 ( ) Real )
( declare-fun c_1_7 ( ) Real )
( declare-fun c_1_8 ( ) Real )
( declare-fun c_1_9 ( ) Real )
( declare-fun c_1_10 ( ) Real )
( declare-fun c_2_0 ( ) Real )
( declare-fun c_2_1 ( ) Real )
( declare-fun c_2_2 ( ) Real )
( declare-fun c_2_3 ( ) Real )
( declare-fun c_2_4 ( ) Real )
( declare-fun c_2_5 ( ) Real )
( declare-fun c_2_6 ( ) Real )
( declare-fun c_2_7 ( ) Real )
( declare-fun c_2_8 ( ) Real )
( declare-fun c_2_9 ( ) Real )
( declare-fun c_2_10 ( ) Real )
( declare-fun correct_0 ( ) Bool )
( declare-fun correct_1 ( ) Bool )
( declare-fun correct_2 ( ) Bool )
( declare-fun correct_3 ( ) Bool )
( declare-fun correct_4 ( ) Bool )
( declare-fun correct_5 ( ) Bool )
( declare-fun correct_6 ( ) Bool )
( declare-fun correct_7 ( ) Bool )
( declare-fun correct_8 ( ) Bool )
( declare-fun correct_9 ( ) Bool )
( declare-fun correct_10 ( ) Bool )
( declare-fun left_0 ( ) Bool )
( declare-fun left_1 ( ) Bool )
( declare-fun left_2 ( ) Bool )
( declare-fun left_3 ( ) Bool )
( declare-fun left_4 ( ) Bool )
( declare-fun left_5 ( ) Bool )
( declare-fun left_6 ( ) Bool )
( declare-fun left_7 ( ) Bool )
( declare-fun left_8 ( ) Bool )
( declare-fun left_9 ( ) Bool )
( declare-fun left_10 ( ) Bool )
( declare-fun ahead_0 ( ) Bool )
( declare-fun ahead_1 ( ) Bool )
( declare-fun ahead_2 ( ) Bool )
( declare-fun ahead_3 ( ) Bool )
( declare-fun ahead_4 ( ) Bool )
( declare-fun ahead_5 ( ) Bool )
( declare-fun ahead_6 ( ) Bool )
( declare-fun ahead_7 ( ) Bool )
( declare-fun ahead_8 ( ) Bool )
( declare-fun ahead_9 ( ) Bool )
( declare-fun ahead_10 ( ) Bool )
( declare-fun canal_0 ( ) Bool )
( declare-fun canal_1 ( ) Bool )
( declare-fun canal_2 ( ) Bool )
( declare-fun canal_3 ( ) Bool )
( declare-fun canal_4 ( ) Bool )
( declare-fun canal_5 ( ) Bool )
( declare-fun canal_6 ( ) Bool )
( declare-fun canal_7 ( ) Bool )
( declare-fun canal_8 ( ) Bool )
( declare-fun canal_9 ( ) Bool )
( declare-fun canal_10 ( ) Bool )
( declare-fun dp_0 ( ) Dt )
( declare-fun dp_1 ( ) Dt )
( declare-fun dp_2 ( ) Dt )
( declare-fun dp_3 ( ) Dt )
( declare-fun dp_4 ( ) Dt )
( declare-fun dp_5 ( ) Dt )
( declare-fun dp_6 ( ) Dt )
( declare-fun dp_7 ( ) Dt )
( declare-fun dp_8 ( ) Dt )
( declare-fun dp_9 ( ) Dt )
( declare-fun dp_10 ( ) Dt )
( declare-fun dgam_0 ( ) Dt )
( declare-fun dgam_1 ( ) Dt )
( declare-fun dgam_2 ( ) Dt )
( declare-fun dgam_3 ( ) Dt )
( declare-fun dgam_4 ( ) Dt )
( declare-fun dgam_5 ( ) Dt )
( declare-fun dgam_6 ( ) Dt )
( declare-fun dgam_7 ( ) Dt )
( declare-fun dgam_8 ( ) Dt )
( declare-fun dgam_9 ( ) Dt )
( declare-fun dgam_10 ( ) Dt )
( declare-fun dc_0 ( ) Dt )
( declare-fun dc_1 ( ) Dt )
( declare-fun dc_2 ( ) Dt )
( declare-fun dc_3 ( ) Dt )
( declare-fun dc_4 ( ) Dt )
( declare-fun dc_5 ( ) Dt )
( declare-fun dc_6 ( ) Dt )
( declare-fun dc_7 ( ) Dt )
( declare-fun dc_8 ( ) Dt )
( declare-fun dc_9 ( ) Dt )
( declare-fun dc_10 ( ) Dt )
( assert ( and ( = t_0 t0 ) ( = p_0 p0 ) ( = gam_0 gam0 ) ( = c_1_0 c_2_0 c0 ) ( = correct_0 correct0 ) ( = left_0 left0 ) ( = ahead_0 ahead0 ) ( = canal_0 canal0 ) ) )
( assert ( and ( = t_1 ( + t_0 0.35 ) ) ( = t_2 ( + t_1 0.35 ) ) ( = t_3 ( + t_2 0.35 ) ) ( = t_4 ( + t_3 0.35 ) ) ( = t_5 ( + t_4 0.35 ) ) ( = t_6 ( + t_5 0.35 ) ) ( = t_7 ( + t_6 0.35 ) ) ( = t_8 ( + t_7 0.35 ) ) ( = t_9 ( + t_8 0.35 ) ) ( = t_10 ( + t_9 0.35 ) ) ) )
( declare-fun int-ode_p ( Real ) Real )
( define-fun dp_move ( ) Dt 0 )
( define-fun dp_fail ( ) Dt 1 )
( declare-fun int-ode_gam ( Real ) Real )
( define-fun dgam_left ( ) Dt 0 )
( define-fun dgam_right ( ) Dt 1 )
( define-fun dgam_ahead ( ) Dt 2 )
( declare-fun int-ode_c ( Real ) Real )
( define-fun dc_inc ( ) Dt 0 )
( define-fun dc_dec ( ) Dt 1 )
( define-fun dc_idle ( ) Dt 2 )
( assert ( and ( = p_1 ( int-ode_p 0 ) ) ( = p_2 ( int-ode_p 1 ) ) ( = p_3 ( int-ode_p 2 ) ) ( = p_4 ( int-ode_p 3 ) ) ( = p_5 ( int-ode_p 4 ) ) ( = p_6 ( int-ode_p 5 ) ) ( = p_7 ( int-ode_p 6 ) ) ( = p_8 ( int-ode_p 7 ) ) ( = p_9 ( int-ode_p 8 ) ) ( = p_10 ( int-ode_p 9 ) ) ) )
( assert ( and ( = gam_1 ( int-ode_gam 0 ) ) ( = gam_2 ( int-ode_gam 1 ) ) ( = gam_3 ( int-ode_gam 2 ) ) ( = gam_4 ( int-ode_gam 3 ) ) ( = gam_5 ( int-ode_gam 4 ) ) ( = gam_6 ( int-ode_gam 5 ) ) ( = gam_7 ( int-ode_gam 6 ) ) ( = gam_8 ( int-ode_gam 7 ) ) ( = gam_9 ( int-ode_gam 8 ) ) ( = gam_10 ( int-ode_gam 9 ) ) ) )
( assert ( and ( = c_1_1 ( int-ode_c 0 ) ) ( = c_1_2 ( int-ode_c 1 ) ) ( = c_1_3 ( int-ode_c 2 ) ) ( = c_1_4 ( int-ode_c 3 ) ) ( = c_1_5 ( int-ode_c 4 ) ) ( = c_1_6 ( int-ode_c 5 ) ) ( = c_1_7 ( int-ode_c 6 ) ) ( = c_1_8 ( int-ode_c 7 ) ) ( = c_1_9 ( int-ode_c 8 ) ) ( = c_1_10 ( int-ode_c 9 ) ) ) )
( define-fun connect ( ( dp Dt ) ( dgam Dt ) ( dc Dt ) ( correct Bool ) ( left Bool ) ( ahead Bool ) ( canal Bool ) ) Bool ( and ( => canal ( and ( = dp dp_fail ) ( = dgam dgam_ahead ) ( = dc dc_idle ) ) ) ( => ( not canal ) ( = dp dp_move ) ) ( => ahead ( and ( = dgam dgam_ahead ) ( = dc dc_idle ) ) ) ( => ( and left ) ( = dgam dgam_left ) ) ( => ( and ( not canal ) ( not left ) ( not ahead ) ) ( = dgam dgam_right ) ) ( => ( and ( not canal ) ( not ahead ) correct ) ( = dc dc_dec ) ) ( => ( and ( not canal ) ( not ahead ) ( not correct ) ) ( = dc dc_inc ) ) ) )
( assert ( and ( connect dp_0 dgam_0 dc_0 correct_0 left_0 ahead_0 canal_0 ) ( connect dp_1 dgam_1 dc_1 correct_1 left_1 ahead_1 canal_1 ) ( connect dp_2 dgam_2 dc_2 correct_2 left_2 ahead_2 canal_2 ) ( connect dp_3 dgam_3 dc_3 correct_3 left_3 ahead_3 canal_3 ) ( connect dp_4 dgam_4 dc_4 correct_4 left_4 ahead_4 canal_4 ) ( connect dp_5 dgam_5 dc_5 correct_5 left_5 ahead_5 canal_5 ) ( connect dp_6 dgam_6 dc_6 correct_6 left_6 ahead_6 canal_6 ) ( connect dp_7 dgam_7 dc_7 correct_7 left_7 ahead_7 canal_7 ) ( connect dp_8 dgam_8 dc_8 correct_8 left_8 ahead_8 canal_8 ) ( connect dp_9 dgam_9 dc_9 correct_9 left_9 ahead_9 canal_9 ) ( connect dp_10 dgam_10 dc_10 correct_10 left_10 ahead_10 canal_10 ) ) )
( define-fun states ( ( correct Bool ) ( left Bool ) ( ahead Bool ) ( canal Bool ) ) Bool ( and ( => canal ( and ( not correct ) ( not left ) ( not ahead ) ) ) ( => correct ( and ( not canal ) ) ) ( => ahead ( and ( not canal ) ( not left ) ) ) ( => left ( and ( not canal ) ( not ahead ) ) ) ) )
( assert ( and ( states correct_0 left_0 ahead_0 canal_0 ) ( states correct_1 left_1 ahead_1 canal_1 ) ( states correct_2 left_2 ahead_2 canal_2 ) ( states correct_3 left_3 ahead_3 canal_3 ) ( states correct_4 left_4 ahead_4 canal_4 ) ( states correct_5 left_5 ahead_5 canal_5 ) ( states correct_6 left_6 ahead_6 canal_6 ) ( states correct_7 left_7 ahead_7 canal_7 ) ( states correct_8 left_8 ahead_8 canal_8 ) ( states correct_9 left_9 ahead_9 canal_9 ) ( states correct_10 left_10 ahead_10 canal_10 ) ) )
( define-fun jump ( ( correct1 Bool ) ( correct2 Bool ) ( left1 Bool ) ( left2 Bool ) ( ahead1 Bool ) ( ahead2 Bool ) ( canal1 Bool ) ( canal2 Bool ) ( p2 Real ) ( c2_1 Real ) ( c2_2 Real ) ) Bool ( and ( => ( and ( not correct1 ) ( not left1 ) ahead1 ( not canal1 ) ) ( and ( => ( and ( > p2 p_lo ) ( < p2 p_hi ) ) ( and ( not correct2 ) ( not left2 ) ahead2 ( not canal2 ) ( = c2_2 c2_1 ) ) ) ( => ( and ( <= p2 p_lo ) ) ( and ( not correct2 ) left2 ( not ahead2 ) ( not canal2 ) ( = c2_2 0 ) ) ) ( => ( and ( >= p2 p_hi ) ) ( and ( not correct2 ) ( not left2 ) ( not ahead2 ) ( not canal2 ) ( = c2_2 0 ) ) ) ) ) ( => ( and ( not correct1 ) left1 ( not ahead1 ) ( not canal1 ) ) ( and ( => ( and ( > p2 p_min ) ( < p2 p_lo ) ) ( and ( not correct2 ) left2 ( not ahead2 ) ( not canal2 ) ) ) ( => ( and ( >= p2 p_lo ) ) ( and correct2 ( not left2 ) ( not ahead2 ) ( not canal2 ) ) ) ( => ( and ( <= p2 p_min ) ) ( and ( not correct2 ) ( not left2 ) ( not ahead2 ) canal2 ) ) ( = c2_2 c2_1 ) ) ) ( => ( and ( not correct1 ) ( not left1 ) ( not ahead1 ) ( not canal1 ) ) ( and ( => ( and ( < p2 p_hi ) ) ( and ( not correct2 ) ( not left2 ) ( not ahead2 ) ( not canal2 ) ) ) ( => ( and ( >= p2 p_hi ) ) ( and correct2 left2 ( not ahead2 ) ( not canal2 ) ) ) ( = c2_2 c2_1 ) ) ) ( => ( and ( not correct1 ) ( not left1 ) ( not ahead1 ) canal1 ) ( and ( not correct2 ) ( not left2 ) ( not ahead2 ) canal2 ( = c2_2 c2_1 ) ) ) ( => ( and correct1 left1 ( not ahead1 ) ( not canal1 ) ) ( and ( => ( and ( > c2_1 0 ) ( > p2 p_lo ) ) ( and correct2 left2 ( not ahead2 ) ( not canal2 ) ( = c2_2 c2_1 ) ) ) ( => ( and ( <= p2 p_lo ) ) ( and ( not correct2 ) left2 ( not ahead2 ) ( not canal2 ) ( = c2_2 0 ) ) ) ( => ( and ( <= c2_1 0 ) ( > p2 p_lo ) ) ( and correct2 ( not left2 ) ahead2 ( not canal2 ) ( = c2_2 c2_1 ) ) ) ) ) ( => ( and correct1 ( not left1 ) ( not ahead1 ) ( not canal1 ) ) ( and ( => ( and ( > c2_1 0 ) ( < p2 p_hi ) ) ( and correct2 ( not left2 ) ( not ahead2 ) ( not canal2 ) ( = c2_2 c2_1 ) ) ) ( => ( and ( >= p2 p_hi ) ) ( and ( not correct2 ) ( not left2 ) ( not ahead2 ) ( not canal2 ) ( = c2_2 0 ) ) ) ( => ( and ( <= c2_1 0 ) ( < p2 p_hi ) ) ( and correct2 ( not left2 ) ahead2 ( not canal2 ) ( = c2_2 c2_1 ) ) ) ) ) ( => ( and correct1 ( not left1 ) ahead1 ( not canal1 ) ) ( and correct2 ( not left2 ) ahead2 ( not canal2 ) ( = c2_2 c2_1 ) ) ) ) )
( assert ( and ( jump correct_0 correct_1 left_0 left_1 ahead_0 ahead_1 canal_0 canal_1 p_1 c_1_1 c_2_1 ) ( jump correct_1 correct_2 left_1 left_2 ahead_1 ahead_2 canal_1 canal_2 p_2 c_1_2 c_2_2 ) ( jump correct_2 correct_3 left_2 left_3 ahead_2 ahead_3 canal_2 canal_3 p_3 c_1_3 c_2_3 ) ( jump correct_3 correct_4 left_3 left_4 ahead_3 ahead_4 canal_3 canal_4 p_4 c_1_4 c_2_4 ) ( jump correct_4 correct_5 left_4 left_5 ahead_4 ahead_5 canal_4 canal_5 p_5 c_1_5 c_2_5 ) ( jump correct_5 correct_6 left_5 left_6 ahead_5 ahead_6 canal_5 canal_6 p_6 c_1_6 c_2_6 ) ( jump correct_6 correct_7 left_6 left_7 ahead_6 ahead_7 canal_6 canal_7 p_7 c_1_7 c_2_7 ) ( jump correct_7 correct_8 left_7 left_8 ahead_7 ahead_8 canal_7 canal_8 p_8 c_1_8 c_2_8 ) ( jump correct_8 correct_9 left_8 left_9 ahead_8 ahead_9 canal_8 canal_9 p_9 c_1_9 c_2_9 ) ( jump correct_9 correct_10 left_9 left_10 ahead_9 ahead_10 canal_9 canal_10 p_10 c_1_10 c_2_10 ) ) )

(check-sat)
(get-value (dp_0))
(get-value (p_0))
(get-value (t_0))
(get-value (t_1))
(get-value (gam_0))
(get-value (dgam_0))
(get-value (gam_0))
(get-value (t_0))
(get-value (t_1))
(get-value (dc_0))
(get-value (c_2_0))
(get-value (t_0))
(get-value (t_1))
(assert (=> (and 
(= dp_0 0.0)
(= p_0 0.0)
(= t_0 0.0)
(= t_1 0.35)
) (= (int-ode_p 0) (- 0.261517))
))
(assert (=> (and 
(= dgam_0 2.0)
(= gam_0 0.15)
(= t_0 0.0)
(= t_1 0.35)
) (= (int-ode_gam 0) 0.150000)
))
(assert (=> (and 
(= dc_0 2.0)
(= c_2_0 0.0)
(= t_0 0.0)
(= t_1 0.35)
) (= (int-ode_c 0) 0.000000)
))
(push 1)
(assert (= dp_0 0.0))
(assert (= dgam_0 2.0))
(assert (= dc_0 2.0))
(check-sat)
(get-value (dp_1))
(get-value (p_1))
(get-value (t_1))
(get-value (t_2))
(get-value (gam_1))
(get-value (dgam_1))
(get-value (gam_1))
(get-value (t_1))
(get-value (t_2))
(get-value (dc_1))
(get-value (c_2_1))
(get-value (t_1))
(get-value (t_2))
(assert (=> (and 
(= dp_1 0.0)
(= p_1 (- 0.261517))
(= t_1 0.35)
(= t_2 0.7)
) (= (int-ode_p 1) (- 0.523034))
))
(assert (=> (and 
(= dgam_1 2.0)
(= gam_1 0.15)
(= t_1 0.35)
(= t_2 0.7)
) (= (int-ode_gam 1) 0.150000)
))
(assert (=> (and 
(= dc_1 2.0)
(= c_2_1 0.0)
(= t_1 0.35)
(= t_2 0.7)
) (= (int-ode_c 1) 0.000000)
))
(push 1)
(assert (= dp_1 0.0))
(assert (= dgam_1 2.0))
(assert (= dc_1 2.0))
(check-sat)
(get-value (dp_2))
(get-value (p_2))
(get-value (t_2))
(get-value (t_3))
(get-value (gam_2))
(get-value (dgam_2))
(get-value (gam_2))
(get-value (t_2))
(get-value (t_3))
(get-value (dc_2))
(get-value (c_2_2))
(get-value (t_2))
(get-value (t_3))
(assert (=> (and 
(= dp_2 0.0)
(= p_2 (- 0.523034))
(= t_2 0.7)
(= t_3 1.05)
) (= (int-ode_p 2) (- 0.784551))
))
(assert (=> (and 
(= dgam_2 2.0)
(= gam_2 0.15)
(= t_2 0.7)
(= t_3 1.05)
) (= (int-ode_gam 2) 0.150000)
))
(assert (=> (and 
(= dc_2 2.0)
(= c_2_2 0.0)
(= t_2 0.7)
(= t_3 1.05)
) (= (int-ode_c 2) 0.000000)
))
(push 1)
(assert (= dp_2 0.0))
(assert (= dgam_2 2.0))
(assert (= dc_2 2.0))
(check-sat)
(get-value (dp_3))
(get-value (p_3))
(get-value (t_3))
(get-value (t_4))
(get-value (gam_3))
(get-value (dgam_3))
(get-value (gam_3))
(get-value (t_3))
(get-value (t_4))
(get-value (dc_3))
(get-value (c_2_3))
(get-value (t_3))
(get-value (t_4))
(assert (=> (and 
(= dp_3 0.0)
(= p_3 (- 0.784551))
(= t_3 1.05)
(= t_4 1.4)
) (= (int-ode_p 3) (- 1.046068))
))
(assert (=> (and 
(= dgam_3 2.0)
(= gam_3 0.15)
(= t_3 1.05)
(= t_4 1.4)
) (= (int-ode_gam 3) 0.150000)
))
(assert (=> (and 
(= dc_3 2.0)
(= c_2_3 0.0)
(= t_3 1.05)
(= t_4 1.4)
) (= (int-ode_c 3) 0.000000)
))
(push 1)
(assert (= dp_3 0.0))
(assert (= dgam_3 2.0))
(assert (= dc_3 2.0))
(check-sat)
(get-value (dp_4))
(get-value (p_4))
(get-value (t_4))
(get-value (t_5))
(get-value (gam_4))
(get-value (dgam_4))
(get-value (gam_4))
(get-value (t_4))
(get-value (t_5))
(get-value (dc_4))
(get-value (c_2_4))
(get-value (t_4))
(get-value (t_5))
(assert (=> (and 
(= dp_4 0.0)
(= p_4 (- 1.046068))
(= t_4 1.4)
(= t_5 1.75)
) (= (int-ode_p 4) (- 0.705452))
))
(assert (=> (and 
(= dgam_4 0.0)
(= gam_4 0.15)
(= t_4 1.4)
(= t_5 1.75)
) (= (int-ode_gam 4) (- 0.550000))
))
(assert (=> (and 
(= dc_4 0.0)
(= c_2_4 0.0)
(= t_4 1.4)
(= t_5 1.75)
) (= (int-ode_c 4) 0.350000)
))
(push 1)
(assert (= dp_4 0.0))
(assert (= dgam_4 0.0))
(assert (= dc_4 0.0))
(check-sat)
(get-value (dp_5))
(get-value (p_5))
(get-value (t_5))
(get-value (t_6))
(get-value (gam_5))
(get-value (dgam_5))
(get-value (gam_5))
(get-value (t_5))
(get-value (t_6))
(get-value (dc_5))
(get-value (c_2_5))
(get-value (t_5))
(get-value (t_6))
(assert (=> (and 
(= dp_5 0.0)
(= p_5 (- 0.705452))
(= t_5 1.75)
(= t_6 2.1)
) (= (int-ode_p 5) (- 0.364836))
))
(assert (=> (and 
(= dgam_5 1.0)
(= gam_5 (- 0.55))
(= t_5 1.75)
(= t_6 2.1)
) (= (int-ode_gam 5) 0.150000)
))
(assert (=> (and 
(= dc_5 1.0)
(= c_2_5 0.35)
(= t_5 1.75)
(= t_6 2.1)
) (= (int-ode_c 5) (- 0.350000))
))
(push 1)
(assert (= dp_5 0.0))
(assert (= dgam_5 1.0))
(assert (= dc_5 1.0))
(check-sat)
(get-value (dp_6))
(get-value (p_6))
(get-value (t_6))
(get-value (t_7))
(get-value (gam_6))
(get-value (dgam_6))
(get-value (gam_6))
(get-value (t_6))
(get-value (t_7))
(get-value (dc_6))
(get-value (c_2_6))
(get-value (t_6))
(get-value (t_7))
(assert (=> (and 
(= dp_6 0.0)
(= p_6 (- 0.364836))
(= t_6 2.1)
(= t_7 2.45)
) (= (int-ode_p 6) (- 0.626353))
))
(assert (=> (and 
(= dgam_6 2.0)
(= gam_6 0.15)
(= t_6 2.1)
(= t_7 2.45)
) (= (int-ode_gam 6) 0.150000)
))
(assert (=> (and 
(= dc_6 2.0)
(= c_2_6 (- 0.35))
(= t_6 2.1)
(= t_7 2.45)
) (= (int-ode_c 6) (- 0.350000))
))
(push 1)
(assert (= dp_6 0.0))
(assert (= dgam_6 2.0))
(assert (= dc_6 2.0))
(check-sat)
(get-value (dp_7))
(get-value (p_7))
(get-value (t_7))
(get-value (t_8))
(get-value (gam_7))
(get-value (dgam_7))
(get-value (gam_7))
(get-value (t_7))
(get-value (t_8))
(get-value (dc_7))
(get-value (c_2_7))
(get-value (t_7))
(get-value (t_8))
(assert (=> (and 
(= dp_7 0.0)
(= p_7 (- 0.626353))
(= t_7 2.45)
(= t_8 2.8)
) (= (int-ode_p 7) (- 0.887870))
))
(assert (=> (and 
(= dgam_7 2.0)
(= gam_7 0.15)
(= t_7 2.45)
(= t_8 2.8)
) (= (int-ode_gam 7) 0.150000)
))
(assert (=> (and 
(= dc_7 2.0)
(= c_2_7 (- 0.35))
(= t_7 2.45)
(= t_8 2.8)
) (= (int-ode_c 7) (- 0.350000))
))
(push 1)
(assert (= dp_7 0.0))
(assert (= dgam_7 2.0))
(assert (= dc_7 2.0))
(check-sat)
(get-value (dp_8))
(get-value (p_8))
(get-value (t_8))
(get-value (t_9))
(get-value (gam_8))
(get-value (dgam_8))
(get-value (gam_8))
(get-value (t_8))
(get-value (t_9))
(get-value (dc_8))
(get-value (c_2_8))
(get-value (t_8))
(get-value (t_9))
(assert (=> (and 
(= dp_8 0.0)
(= p_8 (- 0.88787))
(= t_8 2.8)
(= t_9 3.15)
) (= (int-ode_p 8) (- 1.149387))
))
(assert (=> (and 
(= dgam_8 2.0)
(= gam_8 0.15)
(= t_8 2.8)
(= t_9 3.15)
) (= (int-ode_gam 8) 0.150000)
))
(assert (=> (and 
(= dc_8 2.0)
(= c_2_8 (- 0.35))
(= t_8 2.8)
(= t_9 3.15)
) (= (int-ode_c 8) (- 0.350000))
))
(push 1)
(assert (= dp_8 0.0))
(assert (= dgam_8 2.0))
(assert (= dc_8 2.0))
(check-sat)
(get-value (dp_9))
(get-value (p_9))
(get-value (t_9))
(get-value (t_10))
(get-value (gam_9))
(get-value (dgam_9))
(get-value (gam_9))
(get-value (t_9))
(get-value (t_10))
(get-value (dc_9))
(get-value (c_2_9))
(get-value (t_9))
(get-value (t_10))
(assert (=> (and 
(= dp_9 0.0)
(= p_9 (- 1.149387))
(= t_9 3.15)
(= t_10 3.5)
) (= (int-ode_p 9) (- 1.410904))
))
(assert (=> (and 
(= dgam_9 2.0)
(= gam_9 0.15)
(= t_9 3.15)
(= t_10 3.5)
) (= (int-ode_gam 9) 0.150000)
))
(assert (=> (and 
(= dc_9 2.0)
(= c_2_9 (- 0.35))
(= t_9 3.15)
(= t_10 3.5)
) (= (int-ode_c 9) (- 0.350000))
))
(push 1)
(assert (= dp_9 0.0))
(assert (= dgam_9 2.0))
(assert (= dc_9 2.0))
(check-sat)
(get-value (p_0))
(get-value (p_1))
(get-value (p_2))
(get-value (p_3))
(get-value (p_4))
(get-value (p_5))
(get-value (p_6))
(get-value (p_7))
(get-value (p_8))
(get-value (p_9))
(get-value (dp_0))
(get-value (dp_1))
(get-value (dp_2))
(get-value (dp_3))
(get-value (dp_4))
(get-value (dp_5))
(get-value (dp_6))
(get-value (dp_7))
(get-value (dp_8))
(get-value (dp_9))
(get-value (gam_0))
(get-value (gam_1))
(get-value (gam_2))
(get-value (gam_3))
(get-value (gam_4))
(get-value (gam_5))
(get-value (gam_6))
(get-value (gam_7))
(get-value (gam_8))
(get-value (gam_9))
(get-value (dgam_0))
(get-value (dgam_1))
(get-value (dgam_2))
(get-value (dgam_3))
(get-value (dgam_4))
(get-value (dgam_5))
(get-value (dgam_6))
(get-value (dgam_7))
(get-value (dgam_8))
(get-value (dgam_9))
(get-value (c_2_0))
(get-value (c_2_1))
(get-value (c_2_2))
(get-value (c_2_3))
(get-value (c_2_4))
(get-value (c_2_5))
(get-value (c_2_6))
(get-value (c_2_7))
(get-value (c_2_8))
(get-value (c_2_9))
(get-value (dc_0))
(get-value (dc_1))
(get-value (dc_2))
(get-value (dc_3))
(get-value (dc_4))
(get-value (dc_5))
(get-value (dc_6))
(get-value (dc_7))
(get-value (dc_8))
(get-value (dc_9))
(exit)
