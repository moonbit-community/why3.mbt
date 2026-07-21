// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
extern "C" fn launch_process_group_from_environment() -> Unit = "why3mbt_launch_process_group_from_environment"

///|
extern "C" fn kill_process_group(pid : Int) -> Unit = "why3mbt_kill_process_group"

///|
fn init {
  if @env.get_env_var("WHY3MBT_INTERNAL_LAUNCH") == Some("1") {
    launch_process_group_from_environment()
  }
}

///|
fn process_group_hard_cancel() -> @process.CancellationHandler {
  @process.CancellationHandler(pid => kill_process_group(pid))
}
