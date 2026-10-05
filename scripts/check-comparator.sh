#!/bin/sh
set -eu
PROJECT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
if [ "${1:-}" = '--development' ]; then
  export COMPARATOR_LANDRUN="$PROJECT_DIR/vendor/comparator/scripts/fake-landrun.sh"
  echo 'Development mode: statement matching, axioms and kernels; no Linux isolation.' >&2
  shift
elif [ "$(uname -s)" != Linux ]; then
  echo 'Use --development on macOS, or genuine landrun on Linux.' >&2
  exit 2
fi
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$PROJECT_DIR/vendor/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export}"
cd "$PROJECT_DIR"
exec ./scripts/lake env "$PROJECT_DIR/vendor/comparator/.lake/build/bin/comparator" "${1:-comparator-paper2.json}"
