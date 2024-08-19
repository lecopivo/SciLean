#!/usr/bin/env bash

git ls-files 'SciLean/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > SciLean.lean
