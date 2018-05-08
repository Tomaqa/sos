#!/bin/bash

ROOT=src
[[ -n $1 ]] && ROOT="$1"

DIRS=(`find "$ROOT"/ -type d`)

if [[ -z $2 ]]; then
    printf -- "%s\n" "${DIRS[@]}"
else
    # sed 's|\([^/]*\)/|'"$2"'/|' <<<"$DIRS"
    printf -- "%s\n" "${DIRS[@]/#$ROOT/$2}"
fi
