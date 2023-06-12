#!/bin/bash

## This script extracts 'data' boc from the given tvc file
## and puts it inside the file $2

if [ $# -ne 2 ]; then
    echo "================================================================="
    echo "USAGE: extractData.sh tvcFilePath outputFile"
    echo
    echo "Extracts data boc from the .TVC file"
    echo "================================================================="
    exit 1
fi

TVC=$1
WHERE=$2

tonos-cli decode stateinit --tvc "$TVC" | \
    grep '"data":' | \
    sed 's/^[[:space:]]*//' | \
    cut -d':' -f 2 | \
    sed 's/^[[:space:]]*//' | \
    tr -d ' ",' | \
    base64 -d > "$WHERE"