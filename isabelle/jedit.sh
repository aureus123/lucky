#!/bin/bash
# Open the ACN theories in Isabelle/jEdit, with HOL-Library as logic.
# Usage: ./jedit.sh [theory files...]   (default: ACN/ACN_Sec2.thy)
#   ISABELLE  the isabelle executable (default: isabelle, from PATH)
#   AFP       directory with the AFP entries (default: ./afp)
cd "$(dirname "$0")"
ISABELLE="${ISABELLE:-isabelle}"
AFP="${AFP:-afp}"
[ $# -eq 0 ] && set -- ACN/ACN_Sec2.thy
exec "$ISABELLE" jedit -d "$AFP" -d ACN -l HOL-Library "$@"
