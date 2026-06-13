#!/bin/sh

sudo dtrace -n 'profile-997 /pid == $target && arg1/ { @[ufunc(arg1)] = count(); }' \
  -c './_build/default/bin/main.exe' 2>/dev/null \
  | tail -r \
  | awk 'NR>1 && $NF ~ /^[0-9]+$/ {total += $NF; lines[NR] = $0; counts[NR] = $NF}
         END {for (i in lines) print counts[i]/total*100"%", lines[i]}' \
  | sort -rn \
  | head -30
