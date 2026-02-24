#!/bin/bash

sudo perf record --call-graph dwarf -F 999 ./_build/default/bin/main.exe

sudo perf script -F +pid > trace.txt
