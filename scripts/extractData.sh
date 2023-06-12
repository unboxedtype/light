#!/bin/bash

TVC=$1

tonos-cli decode stateinit --tvc $TVC | \
    grep '"data":' | \
    sed 's/^[[:space:]]*//' | \
    cut -d':' -f 2 | \
    sed 's/^[[:space:]]*//' | \
    tr -d ' ",' | \
    base64 -d > msg.boc