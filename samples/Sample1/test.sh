#!/bin/bash

TESTNAME=Sample1  # actor file without extension

check_command() {
    if command -v "$1" &>/dev/null; then
        echo "$1 found "
    else
        echo "$1 not found! Exiting..."
        exit 1
    fi
}

check_command fift
check_command LHCompiler
check_command tvm_linker
check_command tonos-cli
check_command genActorMessage.fsx
check_command serializeExpression.fsx

## The system actor state is defined as follows:

## type ActorState = {
##  seqNo: uint32;   (* Sending actors must consequently increase this counter *)
##  deployed: bool;  (* Is actor already live inside the blockchain?           *)
##  state: State     (* Application state of the actor                         *)
## }

## The 'state' field inside the ActorState record defines the 'application state',
## the part of state that is visible to actor program. However, during deploy, we
## need to provide the whole ActorState value, so we set the fields seqNo to zero
## and deployed to false. 
echo "Compiling..."

LHCompiler --input ./"$TESTNAME.lh" '{ seqNo = 0; deployed = false; state = { counter = 10; sum = 0 } }'
if [[ $? -ne 0 ]]; then
   echo "Compilation errors.. Exiting"
   exit 1
fi

fift ./"$TESTNAME".fif > "$TESTNAME".address
if [[ $? -ne 0 ]]; then
    echo "Fift script execution failed."
    exit 1
fi

read -p "Please send 1 coin to $(cat $TESTNAME.address) and press Return"
fift ./"$TESTNAME"_deploy.fif
if [[ $? -ne 0 ]]; then
    echo "Deployment script execution failed."
    exit 1
fi

echo "Spawning actor in the blockchain..."
tonos-cli -c ../../scripts/tonos-cli.conf.json sendfile ./"$TESTNAME".boc
if [[ $? -ne 0 ]]; then
    echo "Sending a spawn message failed"
    exit 1
fi

echo "Generating message 1"
genActorMessage.fsx ./"$TESTNAME".lh "$(cat $TESTNAME.address)" '{ seqNo = 1; actorMsg = { func = fun (x:int) -> x * x } }'
if [[ $? -ne 0 ]]; then
    echo "Generating message 1 failed"
    exit 1
fi

echo "Sending message 1"
tonos-cli -c ../../scripts/tonos-cli.conf.json sendfile ./msg.boc
if [[ $? -ne 0 ]]; then
    echo "Sending message 1 failed"
    exit 1
fi

echo "Retriving actor state..."
getActorState.sh ./"$TESTNAME".lh "$(cat $TESTNAME.address)"
if [[ $? -ne 0 ]]; then
    echo "Retriving actor state failed"
    exit 1
fi
