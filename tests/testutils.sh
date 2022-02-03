#!/bin/sh

basicTest() {
  idris2 --quiet --no-color -p table "$@" | sed 's/Main> //' | sed 's/\(Main> \)\+/\n/'

  rm -rf build
}

b2t2Test() {
  printf "%s\n%s\n" ":module B2T2" "$(cat -)" | basicTest -p contrib -p b2t2 "$@" | sed '/^Imported module B2T2$/d'
}
