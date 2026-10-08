#!/bin/sh
# CEP:FILE: tools/cep_lint/build.sh
# CEP:WHAT: Build script for cep_lint: compiles the C++26 sources with the CEP&CC 6.3 minimum warning set and -Werror.
# CEP:WHY: CEP&CC 50.6 gate 1 requires this exact build discipline before every change to the tool.
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: exits nonzero when compilation or linking fails.
# CEP:ASSUMES: run from the repository root; g++ with C++26 support is available.
# CEP:COST: offline build; a few seconds.
# CEP:EVIDENCE: CI job lint runs this script.
# CEP:SECURITY: no network; repository sources only.

set -eu
mkdir -p tools/cep_lint/build
g++ -std=c++26 -O2 \
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion -Wshadow \
    -Wnon-virtual-dtor -Wold-style-cast -Woverloaded-virtual -Wformat=2 -Werror \
    -Itools/cep_lint/src \
    tools/cep_lint/src/main.cpp \
    tools/cep_lint/src/engine.cpp \
    tools/cep_lint/src/checks.cpp \
    tools/cep_lint/src/source.cpp \
    tools/cep_lint/src/json.cpp \
    tools/cep_lint/src/selftest.cpp \
    -o tools/cep_lint/build/cep_lint
echo "built tools/cep_lint/build/cep_lint"
