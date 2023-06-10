#!/bin/bash

## USAGE:
## getActorState.sh programSrc actorId

## Prints actor state according to its definition
## in programSrc, from the blockchain account with
## address = actorId

CONFIG_PATH=~/src/lighthouse/scripts/tonos-cli.conf.json
SOURCE="$1"    # ./samples/Sample.lh
ACTORID="$2"   # "0:bb1899c6f6240d3e133d63d1665b3ccca1e2fc5bf2a3526d847e5ccbf724705b"

if [ $# -ne 2 ]; then
    echo "USAGE: genActorMessage.sh programSrc destActorId"
    echo
    echo "Generates msg.boc"
    echo "================================================================="
    echo "Warning: tonos-cli configuration is put inside the script"
    echo "Warning: Tools 'LHGenDes' and 'fift' has to be in the PATH"
    echo "================================================================="
    exit 1
fi

dotnet fsi genActorMessage.fsx $SOURCE

## Execute a script  that will produce TVC with the  code that serializes
## LH message payload On the next  step, we run this TVC with tvm_linker,
## because the serialization code must be executed on Everscale VM - FIFT
## doesn't know how to serialize continuations.

fift writer.fif

## Produce the correctly serialized message payload, save into TVC data field.
tvm_linker test writer.tvc

## Extract from TVC data the message payload (BOC)
tonos-cli decode stateinit --tvc writer.tvc | \
    grep '"data":' | \
    sed 's/^[[:space:]]*//' | \
    cut -d':' -f 2 | \
    sed 's/^[[:space:]]*//' | \
    tr -d ' ",' | \
    base64 -d > msgbody.boc

echo -n "$ACTORID" > msg.address

## Generate correct message with message payload taken from
## 'msgbody.boc' and stateinit set to empty (we do not deploy anything).
fift ./msg_constructor_payload.fif

## Cleanup.
## rm ./msg.address msgbody.boc writer.fif writer.tvc