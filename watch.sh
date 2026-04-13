#!/bin/sh

find . -name '*.ml' -o -name '*.mli' | entr -c dune exec theory_dev
