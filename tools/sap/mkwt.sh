#!/bin/bash
# mkwt.sh KEY: plain git worktree ~/sap/wt/KEY of ~/sap/repo2 (HEAD, detached). Agents compile SAP/ modules with
# ~/sap/tools/sap-lean (shared prebuilt Mathlib + AronowAudit via repo2's LEAN_PATH; outputs under the worktree's
# .lake/build). No Lake in worktrees: Lake there re-clones the packages and rebuilds Mathlib.
set -eu
KEY=$1; R=$HOME/sap/repo2; W=$HOME/sap/wt/$KEY
test -e "$W" && { echo "exists: $W"; exit 1; }
git -C "$R" worktree add -q --detach "$W" HEAD
mkdir -p "$W/.lake/build/lib/lean" "$W/scratch"
echo "$W"
