#!/bin/sh
# Build the ACN library (requires lake, from elan, on PATH) and show only errors and warnings.
cd "$(dirname "$0")"
lake build "$@" 2>&1 | grep -v "^✔\|^⣿\|Replayed\|^trace:\|^info: \[" | grep -v "^\s*$"
