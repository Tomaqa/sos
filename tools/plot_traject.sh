#!/bin/bash

GNUPLOT_CMD=(gnuplot)

command -v "${GNUPLOT_CMD[@]}" &>/dev/null || {
    printf -- "Gnuplot not found.\n" >&2
    exit 1
}

function usage {
    printf -- "USAGE: %s <data_file> [<plot_file>]\n" "$0"
}

[[ -z $1 ]] && {
    usage
    exit 1
}

GP_TRAJ_SCRIPT=tools/traject.gp

DATA_FILE="$1"

if [[ -n $2 ]]; then
    PLOT_FILE="$2"
else
    PLOT_FILE="${DATA_FILE%.*}_plot.svg"
fi

printf -- "Generating plot ..."

"${GNUPLOT_CMD[@]}" -e "ifname='$DATA_FILE'; ofname='$PLOT_FILE'" \
                       "$GP_TRAJ_SCRIPT"

printf -- " done.\n"

exit 0
