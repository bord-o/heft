#!/bin/bash

sudo perf record --call-graph dwarf -F 999 ../_build/default/theory_dev/theory_dev.exe

sudo perf script -F +pid > trace.txt
