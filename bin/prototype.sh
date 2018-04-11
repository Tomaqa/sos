#!/bin/bash

SMT_SOLVER=(cvc4 -L smt2 --incremental)
# SMT_SOLVER=(z3 -smt2 -in)

ODE_SOLVER=(bin/euler_app)

EVAL_CMD=(bin/eval_app)

PARSER_CMD=(bin/parser_app)

INPUT_F="$1"

MIN_STEP=0
MAX_STEP=

T_ID=t
F_IDS=()

declare -A VALUES
ODE_VALUES=()

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

# 1 - ODE function identifier
function set_links {
    declare -gn lODE_SPEC=ODE_SPEC_${1}
    declare -gn lODE_KEYS=ODE_KEYS_${1}
    declare -gn lDT_IDS=DT_IDS_${1}
    declare -gn lINIT_IDS=INIT_IDS_${1}
    declare -gn lT_INIT_IDS=T_INIT_IDS_${1}
    declare -gn lT_END_IDS=T_END_IDS_${1}
    declare -gn lPARAM_IDS=PARAM_IDS_${1}
}

function parse_input {
    local tmp_f=`mktemp`
    (if [[ -z $INPUT_F ]]; then
        "${PARSER_CMD[@]}"
    else
        "${PARSER_CMD[@]}" "$INPUT_F"
    fi) 2>"$tmp_f" | append_smt

    while read fid; do
        [[ -z $fid ]] && continue;

        F_IDS+=($fid)
        set_links $fid

        read
        read ospec
        lODE_SPEC="($ospec)"
        read keys
        lODE_KEYS+=($keys)
        read MAX_STEP
        local s
        for (( s=$MIN_STEP; $s < $MAX_STEP; s++ )); do
            read const_ids
            const_ids=($const_ids)
            lDT_IDS+=(${const_ids[0]})
            lINIT_IDS+=(${const_ids[1]})
            lT_INIT_IDS+=(${const_ids[2]})
            lT_END_IDS+=(${const_ids[3]})
            lPARAM_IDS+=("${const_ids[*]:4}")
        done
    done <"$tmp_f"
    rm -f "$tmp_f"

    init_ode
}

function init_ode {
    local str="( "
    for fid in ${F_IDS[@]}; do
        set_links $fid
        str+="$lODE_SPEC"
    done
    str+=" )( "
    for fid in ${F_IDS[@]}; do
        set_links $fid
        str+="("
        for key in ${lODE_KEYS[@]}; do
            str+=" $key"
        done
        str+=")"
    done
    str+=" )"
    append_ode "$str"
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
    [[ -z $1 ]] && {
        cat >&5
        return
    }
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

    for fid in ${F_IDS[@]}; do
        set_links $fid
        local args=(${lDT_IDS[$1]} ${lINIT_IDS[$1]} \
                    ${lT_INIT_IDS[$1]} ${lT_END_IDS[$1]})
        args+=(${lPARAM_IDS[$1]})
        for var in ${args[@]}; do
            get_smt_value $var
        done
    done
}

# 1 - step
function compute_odes {
    local str_out="("
    for fid in ${F_IDS[@]}; do
        set_links $fid
        str_out+="${VALUES[${lDT_IDS[$1]}]} "
    done
    str_out+=")  ("
    for fid in ${F_IDS[@]}; do
        set_links $fid
        str_out+=" ( "
        str_out+="(${VALUES[${lT_INIT_IDS[$1]}]}"
        str_out+=" ${VALUES[${lT_END_IDS[$1]}]})"
        str_out+="(${VALUES[${lINIT_IDS[$1]}]}"
        local params=(${lPARAM_IDS[$1]})
        for p in ${params[@]}; do
            str_out+=" ${VALUES[$p]}"
        done
        str_out+=") ) "
    done
    str_out+=")"
    append_ode "${str_out}"
    read values <&6
    ODE_VALUES=($values)
}

# 1 - step
function add_asserts {
    for i in ${!F_IDS[@]}; do
        fid=${F_IDS[$i]}
        set_links $fid
        append_smt <<KONEC
(assert (=> (and (= ${lDT_IDS[$1]} ${VALUES[${lDT_IDS[$1]}]})
                 (= ${lINIT_IDS[$1]} ${VALUES[${lINIT_IDS[$1]}]})
                 (= ${lT_INIT_IDS[$1]} ${VALUES[${lT_INIT_IDS[$1]}]})
                 (= ${lT_END_IDS[$1]} ${VALUES[${lT_END_IDS[$1]}]})
            ) (= (int-ode_${fid} ${1}) ${ODE_VALUES[$i]})
))
KONEC
                ## !!?
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
for fid in ${F_IDS[@]}; do
    set_links $fid
    for var in lINIT_IDS lDT_IDS; do
        declare -n lvar=$var
        for (( s=$MIN_STEP; $s < $MAX_STEP; s++ )); do
            id=${lvar[$s]}
            get_smt_value $id
            printf -- "%s = %.3f\n" ${id} ${VALUES[${id}]}
        done
        echo
    done
done

echo
for i in ${!F_IDS[@]}; do
    fid=${F_IDS[$i]}
    printf -- "%s = %.3f\n" $fid ${ODE_VALUES[$i]}
done

append_smt "(exit)"
cat <&4

exit 0
