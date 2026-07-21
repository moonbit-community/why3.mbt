// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub fn prepare_proof(
  checked : CheckedFile,
  solver_seconds? : Int = @prover.default_solver_seconds(),
  executable_request? : BytesView? = None,
) -> Array[@z3.PreparedCall] raise {
  let checked = tasks(checked)
  let profile = bind_z3_profile(checked.environment, checked.context)
  let command = profile.command_spec(solver_seconds~, executable_request~)
  let calls : Array[@z3.PreparedCall] = []
  for entry in checked.raw_goal_entries {
    let prepared = prepare_z3_task(profile, checked.context, entry.task)
    let query = print_prepared_z3_task(profile, prepared)
    calls.push(
      @z3.PreparedCall::new(entry.task, prepared, query, command, entry.info),
    )
  }
  calls
}
