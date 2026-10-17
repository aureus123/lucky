#!/bin/bash
# Build the ACN session; print theory progress, errors and long-running commands.
#   ISABELLE  the isabelle executable (default: isabelle, from PATH)
#   AFP       directory with the AFP entries Girth_Chromatic, Undirected_Graph_Theory and their
#             dependencies, e.g. the thys directory of an AFP release (default: ./afp)
cd "$(dirname "$0")"
ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-afp}"
"$ISABELLE" build -v -d "$AFP" -D ACN 2>&1 \
  | grep -E --line-buffered "theory ACN|\*\*\*|Finished|FAILED|Timeout|running for [0-9]{2}" \
  | grep -v --line-buffered "cumulated" | awk '!seen[$0]++ {print; fflush()}'
