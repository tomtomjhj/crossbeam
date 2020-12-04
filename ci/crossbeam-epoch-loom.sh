#!/bin/bash

cd "$(dirname "$0")"/../crossbeam-epoch
set -ex

env LOOM_MAX_PREEMPTIONS=2 cargo test --test loom --features sanitize --features check-loom --release -- --nocapture
