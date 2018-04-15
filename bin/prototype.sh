#!/bin/bash

INPUT_F="$1"

UNIF=1

##############################

# SMT_SOLVER=(cvc4 -L smt2 -i)
SMT_SOLVER=(z3 -smt2 -in)
# SMT_SOLVER=(~"/Data/Software/opensmt2/opensmt")

ODE_SOLVER=(bin/euler_app)

EVAL_CMD=(bin/eval_app)

PARSER_CMD=(bin/parser_app)

##############################

MIN_STEP=0
MAX_STEP=

F_KEYS=()

declare -A VALUES
ODE_VALUES=()

SMT_IFIFO=`mktemp -u`
SMT_OFIFO=`mktemp -u`

ODE_IFIFO=`mktemp -u`
ODE_OFIFO=`mktemp -u`

############################################################

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

# 1 - ODE function key
function set_links {
    declare -gn lODE_SPEC=ODE_SPEC_${1}
    declare -gn lODE_KEYS=ODE_KEYS_${1}
    declare -gn lDT_IDS=DT_IDS_${1}
    declare -gn lINIT_IDS=INIT_IDS_${1}
    declare -gn lT_INIT_IDS=T_INIT_IDS_${1}
    declare -gn lT_END_IDS=T_END_IDS_${1}
    declare -gn lPARAM_IDS=PARAM_IDS_${1}

    declare -gn lODE_KEY_IDXS=ODE_KEY_IDXS_${1}
}

function parse_input {
    local tmp_1_f=`mktemp`
    local tmp_2_f=`mktemp`
    if [[ -z $INPUT_F ]]; then
        "${PARSER_CMD[@]}" >"$tmp_1_f" 2>"$tmp_2_f"
    else
        "${PARSER_CMD[@]}" "$INPUT_F" >"$tmp_1_f" 2>"$tmp_2_f"
    fi
    (( $? )) && {
        cat "$tmp_1_f"
        cat "$tmp_2_f"
        rm -f "$tmp_1_f" "$tmp_2_f"
        exit 1
    }
    append_smt <"$tmp_1_f"

    while read fkey; do
        [[ -z $fkey ]] && continue;

        F_KEYS+=($fkey)
        set_links $fkey

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
    done <"$tmp_2_f"

    rm -f "$tmp_1_f" "$tmp_2_f"

    init_ode
}

# 1 - array variable
# 2 - element value
# 3 - result variable
function find_elem {
    local -n ary=$1
    local elem="$2"
    local -n res=$3
    local size=${#ary[@]}
    local i
    for (( i=0; $i < $size; i++ )); do
        [[ ${ary[$i]} == $elem ]] && {
            res=$i
            return 0
        }
    done
    return 1
}

function init_ode {
    local str="( "
    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
        str+="$lODE_SPEC"
    done
    str+=" ) "
    (( $UNIF )) && str+="*"
    str+=" ( "
    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
        str+="("
        for key in ${lODE_KEYS[@]}; do
            str+=" $key"
        done
        str+=")"
    done
    str+=" )"

    append_ode "$str"
    local ukeys
    read ukeys <&6

    if (( $UNIF )); then
        set_unif_keys "$ukeys"
    else
        return 0
    fi
}

# 1 - unif. keys expression string
function set_unif_keys {
    local ukeys="$1"
    ukeys="${ukeys#*(}"
    ukeys="${ukeys%*)}"
    UNIF_ODE_KEYS=($ukeys)

    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
        local idx
        for i in ${!lODE_KEYS[@]}; do
            local key=${lODE_KEYS[$i]}
            find_elem UNIF_ODE_KEYS $key idx || {
                printf -- "Unexpected error: '%s' key not found "\
                          "in unified keys: '%s'" $key "${UNIF_ODE_KEYS[*]}"
                exit 7
            }
            lODE_KEY_IDXS[$i]=$idx
        done
    done

    UNIF_ODE_KEY_ODE_IDXS=()
    UNIF_ODE_KEY_KEY_IDXS=()
    for i in ${!UNIF_ODE_KEYS[@]}; do
        local ukey=${UNIF_ODE_KEYS[$i]}
        local idx
        for j in ${!F_KEYS[@]}; do
            fkey=${F_KEYS[$j]}
            set_links $fkey
            find_elem lODE_KEYS $ukey idx && {
                UNIF_ODE_KEY_ODE_IDXS[$i]=$j
                UNIF_ODE_KEY_KEY_IDXS[$i]=$idx
                break
            }
        done
    done

    return 0
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
function add_smt_conflict {
    local str=
    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
        str+="
(= ${lDT_IDS[$1]} ${VALUES[${lDT_IDS[$1]}]})
(= ${lINIT_IDS[$1]} ${VALUES[${lINIT_IDS[$1]}]})
(= ${lT_INIT_IDS[$1]} ${VALUES[${lT_INIT_IDS[$1]}]})
(= ${lT_END_IDS[$1]} ${VALUES[${lT_END_IDS[$1]}]})"
    done
    append_smt "(assert (not (and ${str}
)))"
}

# 1 - step
function smt_check_sat {
    local sat
    append_smt "(check-sat)"
    read sat <&4
    printf -- "%s\n" "$sat"
    if [[ $sat == sat ]]; then
        :
    elif [[ $sat == unsat ]]; then
        return 100
    else
        return 1
    fi
}

# 1 - step
function get_smt_values {
    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
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
    for fkey in ${F_KEYS[@]}; do
        set_links $fkey
        str_out+="${VALUES[${lDT_IDS[$1]}]} "
    done
    str_out+=")  ("
    if (( $UNIF )); then
        str_out+="( "
        set_links ${F_KEYS[0]}
        str_out+="(${VALUES[${lT_INIT_IDS[$1]}]}"
        str_out+=" ${VALUES[${lT_END_IDS[$1]}]})"
        str_out+=" ("
        for fkey in ${F_KEYS[@]}; do
            set_links $fkey
            str_out+=" ${VALUES[${lINIT_IDS[$1]}]}"
        done
        for (( i=${#F_KEYS[@]}; $i < ${#UNIF_ODE_KEYS[@]}-1; i++ )); do
            local fidx=${UNIF_ODE_KEY_ODE_IDXS[$i]}
            local fkey=${F_KEYS[$fidx]}
            set_links $fkey
            local params=(${lPARAM_IDS[$1]})
            local kidx=${UNIF_ODE_KEY_KEY_IDXS[$i]}
            (( kidx-- ))
            p=${params[$kidx]}
            str_out+=" ${VALUES[$p]}"
        done
        str_out+=") )"
    else
        for fkey in ${F_KEYS[@]}; do
            set_links $fkey
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
    fi
    str_out+=")"

    append_ode "$str_out"
    local values
    read values <&6
    ODE_VALUES=($values)
    return 0
}

# 1 - step
function add_asserts {
    for i in ${!F_KEYS[@]}; do
        fkey=${F_KEYS[$i]}
        set_links $fkey
        append_smt <<KONEC
(assert (=> (and (= ${lDT_IDS[$1]} ${VALUES[${lDT_IDS[$1]}]})
                 (= ${lINIT_IDS[$1]} ${VALUES[${lINIT_IDS[$1]}]})
                 (= ${lT_INIT_IDS[$1]} ${VALUES[${lT_INIT_IDS[$1]}]})
                 (= ${lT_END_IDS[$1]} ${VALUES[${lT_END_IDS[$1]}]})
            ) (= (int-ode_${fkey} ${1}) ${ODE_VALUES[$i]})
))
KONEC
    done
}

# 1 - step
function do_step {
    local s=$1
    printf -- "\nStep %d ...\n" $s
    smt_check_sat $s
    local ret=$?
    case $ret in
        1) return 1;;
        100)  if (( $s > 0 )); then
                  printf -- "Backtrack ...\n"
                  (( s-- ))
                  add_smt_conflict $s
                  do_step $s
                  return $?
              else
                  printf -- "Not satisfiable!\n"
                  # append_smt "(get-proof)" "(exit)"
                  append_smt "(exit)"
                  cat <&4
                  return 2
              fi;;
    esac
    (( $s == $MAX_STEP )) && return
    get_smt_values $s
    compute_odes $s
    add_asserts $s
}

############################################################

trap cleanup EXIT
trap 'failure 1' ERR SIGHUP
trap 'failure 2' SIGINT SIGTERM

mkfifo -m 600 "$SMT_IFIFO"
mkfifo -m 600 "$SMT_OFIFO"

"${SMT_SOLVER[@]}" <"$SMT_IFIFO" &>"$SMT_OFIFO" &
# "${SMT_SOLVER[@]}" <"$SMT_IFIFO" >"$SMT_OFIFO" 2>/dev/null &
# exec 3>"$SMT_IFIFO"
exec 3> >(tee smt_log >"$SMT_IFIFO")
exec 4<"$SMT_OFIFO"

mkfifo -m 600 "$ODE_IFIFO"
mkfifo -m 600 "$ODE_OFIFO"

"${ODE_SOLVER[@]}" <"$ODE_IFIFO" &>"$ODE_OFIFO" &
exec 5> >(tee ode_log >"$ODE_IFIFO")
exec 6<"$ODE_OFIFO"

##############################

parse_input

for (( s=$MIN_STEP; $s <= $MAX_STEP; s++ )); do
    do_step $s
done

echo
for fkey in ${F_KEYS[@]}; do
    set_links $fkey
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
for i in ${!F_KEYS[@]}; do
    fkey=${F_KEYS[$i]}
    printf -- "%s = %.3f\n" $fkey ${ODE_VALUES[$i]}
done

append_smt "(exit)"
cat <&4

exit 0
