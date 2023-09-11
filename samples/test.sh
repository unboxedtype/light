#!/bin/bash

## This script is actually a template that you can adjust
## for any sample, or for your code.

## This is needed for DOTNET programs to work from the commandline.
export DOTNET_ROOT=/usr/lib64/dotnet/

## We need to adjust path to the Light compiler
LC=../../src/LHCompiler/bin/Debug/net7.0/LHCompiler

## The list of files we will use.
SAMPLE=minimal
SAMPLE_SRC="$SAMPLE.lh"
SAMPLE_ADDR="$SAMPLE.address"
SAMPLE_TVC="$SAMPLE.stateinit.tvc"
SAMPLE_MSG="$SAMPLE.msg.boc"

## Remove temporary files that get generated after compilation
rm -rf $SAMPLE_ADDR $SAMPLE_TVC $SAMPLE_MSG

## Compile the actor. It will produce .address, .stateinit.tvc files
## The value of 'state' record field depends on State type. In the
## 'minimal.lh' sample, state type is Unit, hence we put () there.
$LC --input $SAMPLE_SRC '{ seqNo = 0; deployed = false; salt = 1; state = () }'
tvm_linker test $SAMPLE_TVC --body x09c_

## Generate message to the actor. The command will produce .msg.boc file with
## the given content. The value of 'actorMsg' field depends on ActorMessage type.
## In the 'minimal.lh' sample, message type is Unit, hence we put () there.
$LC --message $SAMPLE_SRC $(cat $SAMPLE_ADDR) '{ seqNo = 1; actorMsg = () }'
tvm_linker test $SAMPLE_TVC --body-from-boc $SAMPLE_MSG

## Generate another message to the actor. You need to adjust seqNo counter
## for proper replay-protection.
$LC --message $SAMPLE_SRC $(cat $SAMPLE_ADDR) '{ seqNo = 2; actorMsg = () }'
tvm_linker test $SAMPLE_TVC --body-from-boc $SAMPLE_MSG
