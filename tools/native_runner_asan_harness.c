// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

#include <stdint.h>
#include <string.h>

void why3mbt_launch_process_group_from_environment(void);
void why3mbt_kill_process_group(int32_t pid);

int main(int argc, char **argv) {
  if (argc == 2 && strcmp(argv[1], "kill-boundary") == 0) {
    why3mbt_kill_process_group(0);
    why3mbt_kill_process_group(1);
    return 0;
  }
  why3mbt_launch_process_group_from_environment();
  return 125;
}
