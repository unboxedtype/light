#!/bin/bash

## Remove trailing whitespaces from files.
## Needs to be done before each git commit.
find -type f -name '*.fs' -o -name '*.fsy' -o -name '*.fsl' -o -name '*.fsproj' | xargs sed --in-place 's/[[:space:]]\+$//'