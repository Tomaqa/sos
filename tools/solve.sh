#!/bin/bash

SMT_SOLVER=(cvc4 -L smt2 --incremental)
# SMT_SOLVER=(z3 -smt2 -in)

if [[ -z $1 ]]; then
  INPUT=`cat`
else
  INPUT=`<"$1"`
fi

MIN_STEP=
MAX_STEP=

F_IDS=()
DT_IDS=()
T_ID=

declare -A VALUES
ODE_VALUE=()

SMT_IFIFO=`mktemp -u`
SMT_OFIFO=`mktemp -u`

##############################

function cleanup {
  printf -- "\nCLOSING ...\n"
  exec 3>&-
  exec 4<&-
  rm -f "$SMT_IFIFO" "$SMT_OFIFO"
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

function append_smt {
  for i; do
    printf -- "%s\n" "$i" >&3
  done
}

# 1 - expression
function get_value {
  # clisp -q -x "$(sed 's/\([0-9][0-9]*\)\([^.0-9]\)/\1.0\2/g' <<<"$value")"
  if [[ $1 =~ \( ]]; then
    ol -e "$1" | bc -l | awk '{ printf "%.3f", $0 }'
  else
    printf -- "%.3f" "$1"
  fi
}

# 1 - step
function get_smt_values {
  local sat values
  append_smt "(check-sat)"
  read sat <&4
  if [[ $sat == sat ]]; then
    :
  elif [[ $sat == unsat ]]; then
    printf -- "%s\n" "$sat"
    append_smt "(get-proof)" "(exit)"
    cat <&4
    return 2
  else
    printf -- "%s\n" "$sat"
    return 1
  fi

  local args=(${T_ID}_${1} ${T_ID}_$(($1+1)) ${F_IDS[@]/%/_$1} ${DT_IDS[@]/%/_$1})
  for var in ${args[@]}; do
    append_smt "(get-value ($var))"
    read value <&4
    value="${value#* }"
    value="${value%))}"
    value=`get_value "$value"`
    VALUES[$var]=$value
  done
}

unset ODE_FIRST
# 1 - step
function compute_odes {
  [[ -z $ODE_FIRST ]] && {
    ODE_FIRST=1
    append_smt "`cat <<KONEC
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
      (let ((C (ite (= dx1 _dx_on) 100.0 50.0)))
          (- C (* (- C x1) (e^-t (- t2 t1)) ) )
      ))
KONEC`"
      # (let ((C (ite (= dx1 dx_on) 100.0 50.0)))
  }
  ODE_VALUE=()
  for i in ${!F_IDS[@]}; do
    ODE_VALUE[$i]="(eval-dx ${VALUES[${DT_IDS[$i]}_${1}]} ${VALUES[${T_ID}_${1}]} ${VALUES[${T_ID}_$(($1+1))]} ${VALUES[${F_IDS[$i]}_${1}]})"
  done
}

# 1 - step
function add_asserts {
  for i in ${!F_IDS[@]}; do
    # append_smt "(assert (= (dt-int ${DT_IDS[$i]}_${1} ${T_ID}_${1} ${T_ID}_$(($1+1)) ${F_IDS[$i]}_${1}) ${ODE_VALUE[$i]}))"
    append_smt "(assert (= _dx_${1}_int ${ODE_VALUE[$i]}))"
  done
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
exec 3>"$SMT_IFIFO"
exec 4<"$SMT_OFIFO"

append_smt "$INPUT"

MIN_STEP=0
MAX_STEP=8

F_IDS+=(x)
# DT_IDS+=(dx)
DT_IDS+=(_dx)
T_ID=t

for (( s=$MIN_STEP; $s <= $MAX_STEP; s++ )); do
  get_smt_values $s
  compute_odes $s
  add_asserts $s
done

append_smt "(check-sat)" "(get-model)" "(exit)"
cat <&4

exit 0
