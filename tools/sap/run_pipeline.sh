#!/bin/bash
cd ~/sap && exec python3 tools/sap_pipeline.py "$@" >> pipeline/pipeline.out 2>&1
