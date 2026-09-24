#!/usr/bin/env bash
# Build modules with lake (writes .olean files). Only ONE agent at a time may run this.
# usage: wsl -d Ubuntu --cd /home/mdevi/zeta2-lean -- bash scripts/build.sh [Module.Name ...]
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/zeta2-lean" || exit 2
exec 9>/tmp/zeta2-lean-build.lock
flock 9
timeout "${TIMEOUT:-3600}" lake build "$@" 2>&1 | tail -c 150000
echo "---"
echo "exit=${PIPESTATUS[0]}"
