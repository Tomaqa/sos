#!/bin/bash

SMT_SOLVER=(cvc4 -L smt2 --incremental)
# SMT_SOLVER=(z3 -smt2 -in)

ODE_SOLVER=(bin/euler_app)

EVAL_CMD=(bin/eval_app)

PARSER_CMD=(bin/parser_app)

INPUT_F="$1"

MIN_STEP=
MAX_STEP=

F_IDS=()
DT_IDS=()
T_ID=

declare -A VALUES
ODE_VALUE=()

SMT_IFIFO=`mktemp -u`
SMT_OFIFO=`mktemp -u`

ODE_IFIFO=`mktemp -u`
ODE_OFIFO=`mktemp -u`

##############################

function cleanup {
    printf -- "\nCLOSING ...\n"
    exec 3>&-
    exec 4<&-
    exec 5>&-
    exec 6<&-
    rm -f "$SMT_IFIFO" "$SMT_OFIFO"
    rm -f "$ODE_IFIFO" "$ODE_OFIFO"
}

function failure {
    printf -- "\nFAILURE\n" >&2
    local ret
    if [[ -z $1 ]]; then
        ret=1
    else
        ret=$1
    fi
    exit $1
}

##############################

function parse_input {
    if [[ -z $INPUT_F ]]; then
        "${PARSER_CMD[@]}"
    else
        "${PARSER_CMD[@]}" "$INPUT_F"
    fi | append_smt

    MIN_STEP=0
    MAX_STEP=9

    F_IDS+=(x)
    DT_IDS+=(dx)
    T_ID=t

    # append_ode "( ((- 100 x) (-  50 x)) ) (x)"
    append_ode "( ((-  50 x) (- 100 x)) ) (x)"
}

function append_smt {
    [[ -z $1 ]] && {
        cat >&3
        return
    }
    for i; do
        printf -- "%s\n" "$i" >&3
    done
}

function append_ode {
    for i; do
        printf -- "%s\n" "$i" >&5
    done
}

# Filter
function get_value {
    "${EVAL_CMD[@]}"
}

# 1 - var. identifier
function get_smt_value {
    append_smt "(get-value ($1))"
    local value
    read value <&4
    value="${value#* }"
    value="${value%))}"
    value=`get_value <<<"$value"`
    VALUES[$1]=$value
}

# 1 - step
function get_smt_values {
    local sat values
    append_smt "(check-sat)"
    read sat <&4
    if [[ $sat == sat ]]; then
        :
    elif [[ $sat == unsat ]]; then
        printf -- "%s\nBacktrack ...\n" "$sat"
        return 100
    else
        printf -- "%s\n" "$sat"
        return 1
    fi

    local args=(${T_ID}_${1} ${T_ID}_$(($1+1)) \
                ${F_IDS[@]/%/_$1} ${DT_IDS[@]/%/_$1})
    for var in ${args[@]}; do
        get_smt_value $var
    done
}

# 1 - step
function compute_odes {
    local str_out="("
    for dt_id in ${DT_IDS[@]}; do
        str_out+="${VALUES[${dt_id}_${1}]} "
    done
    str_out+=")  ("
    for i in ${!F_IDS[@]}; do
        str_out+=" ( "
        str_out+="(${VALUES[${T_ID}_${1}]} ${VALUES[${T_ID}_$(($1+1))]})"
        str_out+="(${VALUES[${F_IDS[$i]}_${1}]})"
        str_out+=" ) "
    done
    str_out+=")"
    append_ode "${str_out}"
    read values <&6
    ODE_VALUES=($values)
}

# 1 - step
function add_asserts {
    for i in ${!F_IDS[@]}; do
        append_smt <<KONEC
(assert (=> (and (= ${DT_IDS[$i]}_${1} ${VALUES[${DT_IDS[$i]}_${1}]})
                 (= ${F_IDS[$i]}_${1} ${VALUES[${F_IDS[$i]}_${1}]})
                 (= ${T_ID}_${1} ${VALUES[${T_ID}_${1}]})
                 (= ${T_ID}_$(($1+1)) ${VALUES[${T_ID}_$(($1+1))]})
            ) (= (int-ode_x ${1}) ${ODE_VALUES[$i]})
))
KONEC
# (assert (=> (and (= ${DT_IDS[$i]}_${1} ${VALUES[${DT_IDS[$i]}_${1}]})
#                  (= ${T_ID}_${1} ${VALUES[${T_ID}_${1}]})
#                  (= ${T_ID}_$(($1+1)) ${VALUES[${T_ID}_$(($1+1))]})
#                  (= ${F_IDS[$i]}_${1} ${VALUES[${F_IDS[$i]}_${1}]})
#             ) (= _dx_${1}_int ${ODE_VALUES[$i]})
# ))
    done
}

# 1 - step
function do_step {
    local s=$1
    printf -- "Step %d ...\n" $s
    get_smt_values $s
    local ret=$?
    case $ret in
        1) return 1;;
        100)  if (( $s > 0 )); then
                        do_step $(($s-1))
                        return $?
                    else
                        printf -- "Not satisfiable!\n"
                        append_smt "(get-proof)" "(exit)"
                        cat <&4
                        return 2
                    fi;;
    esac
    compute_odes $s
    add_asserts $s
}

##########################

trap cleanup EXIT
trap 'failure 1' ERR SIGHUP
trap 'failure 2' SIGINT SIGTERM

PIDS=()

mkfifo -m 600 "$SMT_IFIFO"
mkfifo -m 600 "$SMT_OFIFO"

echo "${SMT_SOLVER[@]}"

# "${SMT_SOLVER[@]}" <"$SMT_IFIFO" &>"$SMT_OFIFO" &
"${SMT_SOLVER[@]}" <"$SMT_IFIFO" >"$SMT_OFIFO" 2>/dev/null &
# exec 3>"$SMT_IFIFO"
exec 3> >(tee smt_log >"$SMT_IFIFO")
exec 4<"$SMT_OFIFO"

mkfifo -m 600 "$ODE_IFIFO"
mkfifo -m 600 "$ODE_OFIFO"

"${ODE_SOLVER[@]}" <"$ODE_IFIFO" &>"$ODE_OFIFO" &
exec 5> >(tee ode_log >"$ODE_IFIFO")
exec 6<"$ODE_OFIFO"

###########

parse_input

for (( s=$MIN_STEP; $s < $MAX_STEP; s++ )); do
    do_step $s
done

append_smt "(check-sat)"
read <&4

echo
for var in F_IDS DT_IDS; do
    for (( s=$MIN_STEP; $s < $MAX_STEP; s++ )); do
        for i in ${!F_IDS[@]}; do
            declare -n var_l=$var
            id=${var_l[$i]}_${s}
            get_smt_value ${id}
            printf -- "%s = %.3f\n" ${id} ${VALUES[${id}]}
        done
    done
    echo
done

echo
for fid in ${F_IDS[@]}; do
    id=${fid}_${s}
    get_smt_value ${id}
    printf -- "%s = %.3f\n" ${id} ${VALUES[${id}]}
done

append_smt "(exit)"
cat <&4

exit 0
