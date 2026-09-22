#!/bin/bash
cd "$(git rev-parse --show-toplevel)"
B=${S16_BIN:-./_build/default/cli/main.exe}
f="$1"
line=$(MORDOR_S16=1 timeout 600 $B futures --single "$f" --no-progress --warning --allow-unknown-model 2>&1 | grep "^S16 executions")
if [ -n "$line" ]; then echo -e "$f\t$line"; else echo -e "$f\tNONE"; fi
