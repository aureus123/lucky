#!/bin/sh
# Usage: ./mmlthm.sh ARTICLE REGEX  -- show theorems of an MML abstract (with labels) matching REGEX
f="$MIZFILES/abstr/$(echo "$1" | tr A-Z a-z).abs"
awk -v re="$2" '/^(theorem|scheme|definition|registration)/{if(blk ~ re) print blk "\n"; blk=$0; next} {blk=blk "\n" $0} END{if(blk ~ re) print blk}' "$f"
