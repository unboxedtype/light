#!/bin/bash

## USAGE:
## getActorState.sh programSrc actorId

## Prints actor state according to its definition
## in programSrc, from the blockchain account with
## address = actorId

CONFIG_PATH=~/src/lighthouse/scripts/tonos-cli.conf.json
SOURCE="$1"
ACTORID="$2"

if [ $# -ne 2 ]; then
    echo "USAGE: getActorState.sh programSrc actorId"
    echo
    echo "Prints Lighthouse actor state according to its definition"
    echo "in programSrc, from the blockchain account with address = actorId"
    echo "================================================================="
    echo "Warning: tonos-cli configuration is put inside the script"
    echo "Warning: Tools 'LHGenDes' and 'fift' has to be in the PATH"
    echo "================================================================="
fi

tonos-cli -c $CONFIG_PATH account $ACTORID | \
    grep data_boc | \
    cut -d":" -f 2 | \
    sed 's/^[[:space:]]*//' > data.c4

LHGenDes $SOURCE $ACTORID > reader.fif
fift ./reader.fif