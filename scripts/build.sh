#!/bin/bash

VERBOSE=1 \
cmake \
  --build build \
  --config Debug \
  --target all
