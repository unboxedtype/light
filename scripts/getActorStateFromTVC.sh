#!/bin/bash

## USAGE:
## getActorState.sh programSrc actorId

## Prints actor state according to its definition
## in programSrc, from the blockchain account with
## address = actorId

CONFIG_PATH=~/src/lighthouse/scripts/tonos-cli.conf.json
SOURCE="$1"
TVC="$2"
TYPENAME="$3"   # for example, ActorState

if [ $# -ne 3 ]; then
    echo "USAGE: getActorStateFromTVC.sh programSrc pathToTVC typeName"
    echo
    echo "Prints Lighthouse actor state according to the definition of typeName"
    echo "in programSrc, from the tvc file"
    echo "================================================================="
    echo "Warning: tonos-cli configuration is put inside the script"
    echo "Warning: Tools 'LHGenDes' and 'fift' has to be in the PATH"
    echo "================================================================="
fi

tonos-cli -c $CONFIG_PATH decode stateinit --tvc $TVC | \
    grep '"data":' | \
    sed 's/^[[:space:]]*//' | \
    cut -d':' -f 2 | \
    sed 's/^[[:space:]]*//' | \
    tr -d ' ",' | \
    base64 -d > data.c4

~/src/lighthouse/src/LHGenDes/bin/Debug/net6.0/LHGenDes $SOURCE $TYPENAME
fift ./reader.fif