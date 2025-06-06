#!/usr/bin/env bash
set -euo pipefail # ; set -x # for debugging

DEFINITIONS_DIR="lean/Shars/Definitions"

charon(){
    nix run github:aeneasverif/aeneas#charon -L \
        -- \
        rustc \
        --dest-file="$1.llbc" \
        --hide-marker-traits \
        --remove-associated-types="*" \
        -- \
        --crate-type=lib \
        "src/$1.rs"
}

aeneas(){
    nix run github:aeneasverif/aeneas -L -- -backend lean "$1.llbc"
    rm "$1.llbc"
}

extract(){
    charon $1
    aeneas $1
}

prog="$0"
cmd="$1"; shift
case $cmd in

  "algos")
      extract "algos"
      mv Algos.lean "$DEFINITIONS_DIR/"
    ;;

  "custom")
      extract $1
    ;;

  *)
      echo "Unknown option, look at $prog to see options available"
      read && [ -n "$REPLY" ] && less $prog
      exit 1
    ;;

esac

