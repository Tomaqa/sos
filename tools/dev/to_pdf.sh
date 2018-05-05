#!/bin/sh

[[ -z $1 ]] && {
	printf -- "Provide an image file to be converted.\n" >&2
	exit 1
}

IFILE="$1"
OFILE="${IFILE%.*}.pdf"
[[ $IFILE == $OFILE ]] && {
	printf -- "Input file is already in PDF format.\n"
	exit 0
}

inkscape -z -b -D -f "$IFILE" -A "$OFILE"
