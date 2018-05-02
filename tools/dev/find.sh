#!/bin/bash

if [[ -z $1 ]]; then
    PATT="[^/\"]// "
else
    PATT="$1"
fi

find src/ include/ -type f -exec grep -H "$PATT" {} \;
