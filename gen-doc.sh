#!/bin/bash

cargo makedocs -e log -e derive_more
cargo doc -p thread-local-drop --no-deps
