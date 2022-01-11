#!/bin/sh

basicTest() {
  fileName=$1

  idris2 --quiet --no-color -p table "$fileName" | sed 's/Main> //' | sed 's/\(Main> \)\+/\n/'

  rm -rf build
}
