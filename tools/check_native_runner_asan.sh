#!/bin/sh
# SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

set -eu

moon_toolchain_root=${MOON_HOME:-}
if [ -z "$moon_toolchain_root" ]; then
  moon_executable=$(command -v moon) || {
    echo "moon is required to locate moonbit.h" >&2
    exit 1
  }
  moon_executable=$(readlink -f "$moon_executable")
  moon_toolchain_root=$(dirname "$(dirname "$moon_executable")")
fi
if [ ! -f "$moon_toolchain_root/include/moonbit.h" ]; then
  echo "moonbit.h not found under $moon_toolchain_root/include" >&2
  exit 1
fi

asan_directory=$(mktemp -d)
trap 'rm -rf "$asan_directory"' EXIT HUP INT TERM

asan_executable="$asan_directory/process-group-asan"
${CC:-cc} \
  -std=gnu11 \
  -Wall \
  -Wextra \
  -Werror \
  -fsanitize=address,undefined \
  -fno-omit-frame-pointer \
  -I"$moon_toolchain_root/include" \
  prover/native/process_group.c \
  tools/native_runner_asan_harness.c \
  -o "$asan_executable"

ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
UBSAN_OPTIONS=halt_on_error=1 \
  "$asan_executable" kill-boundary

env -i \
  ASAN_OPTIONS=detect_leaks=0:halt_on_error=1 \
  UBSAN_OPTIONS=halt_on_error=1 \
  LC_ALL=C \
  WHY3MBT_ASAN_SENTINEL=retained \
  WHY3MBT_INTERNAL_LAUNCH=1 \
  WHY3MBT_INTERNAL_EXECUTABLE=/bin/sh \
  WHY3MBT_INTERNAL_ARGC=2 \
  WHY3MBT_INTERNAL_ARG_0=-c \
  WHY3MBT_INTERNAL_ARG_1='test "$LC_ALL" = C && test -z "${WHY3MBT_INTERNAL_LAUNCH+x}" && test "$WHY3MBT_ASAN_SENTINEL" = retained' \
  "$asan_executable"

descendant_pid_file="$asan_directory/descendant.pid"
env -i \
  ASAN_OPTIONS=detect_leaks=0:halt_on_error=1 \
  UBSAN_OPTIONS=halt_on_error=1 \
  LC_ALL=C \
  WHY3MBT_INTERNAL_LAUNCH=1 \
  WHY3MBT_INTERNAL_EXECUTABLE=/bin/sh \
  WHY3MBT_INTERNAL_ARGC=2 \
  WHY3MBT_INTERNAL_ARG_0=-c \
  WHY3MBT_INTERNAL_ARG_1="sleep 30 & child=\$!; printf '%s' \"\$child\" > '$descendant_pid_file'; wait" \
  "$asan_executable" &
launcher_pid=$!

attempt=0
while [ ! -s "$descendant_pid_file" ]; do
  attempt=$((attempt + 1))
  if [ "$attempt" -ge 500 ]; then
    kill -KILL "$launcher_pid" 2>/dev/null || true
    wait "$launcher_pid" 2>/dev/null || true
    echo "ASan cancellation launcher did not create its descendant" >&2
    exit 1
  fi
  sleep 0.01
done

kill -TERM "$launcher_pid"
set +e
wait "$launcher_pid"
launcher_status=$?
set -e
if [ "$launcher_status" -ne 130 ]; then
  echo "ASan cancellation launcher exited with $launcher_status, expected 130" >&2
  exit 1
fi
descendant_pid=
IFS= read -r descendant_pid < "$descendant_pid_file" || true
if [ -z "$descendant_pid" ]; then
  echo "ASan cancellation recorded an empty descendant pid" >&2
  exit 1
fi
if [ -e "/proc/$descendant_pid" ]; then
  echo "ASan cancellation left descendant $descendant_pid behind" >&2
  exit 1
fi
