#!/usr/bin/env bash
set -euo pipefail # ; set -x # for debugging

DEFINITIONS_DIR="lean/Shars/Definitions"

charon(){
    nix run github:aeneasverif/aeneas#charon -L \
        -- \
        rustc \
        --input "src/$1.rs" \
        --dest-file="$1.llbc" \
        --hide-marker-traits \
        --remove-associated-types="*" \
        -- \
        --crate-type=lib
}

aeneas(){
    nix run github:aeneasverif/aeneas -L -- -backend lean "$1.llbc"
    rm "$1.llbc"
}

prog="$0"
cmd="$1"; shift
case $cmd in

  "simple")
      charon "simple"
      aeneas "simple"
      mv Simple.lean "$DEFINITIONS_DIR/"
    ;;

  "custom")
      charon $1
      aeneas $1
    ;;

  *)
      echo "Unknown option, look at $prog to see options available"
      read && [ -n "$REPLY" ] && less $prog
      exit 1
    ;;
esac

