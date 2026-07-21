// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum NativeRunOutcome {
  Completed(@prover.RawProcessOutcome)
  ParentDeadlineExceeded
}

///|
struct NativeRunner {
  command : @prover.CommandSpec
  executable : ResolvedExecutable
  launcher : ResolvedLauncher
}

///|
pub async fn NativeRunner::new(command : @prover.CommandSpec) -> NativeRunner {
  let executable = resolve_executable(command.view().executable_request)
  let launcher = resolve_current_launcher()
  { command, executable, launcher }
}

///|
pub fn NativeRunner::resolved_executable(self : NativeRunner) -> StringView {
  self.executable.path()
}

///|
fn signal_name(number : Int) -> Bytes {
  match number {
    9 => b"SIGKILL"
    15 => b"SIGTERM"
    2 => b"SIGINT"
    6 => b"SIGABRT"
    11 => b"SIGSEGV"
    _ => {
      let buffer = @buffer.Buffer(size_hint=16)
      buffer.write_bytes(b"SIGNAL:")
      buffer.write_bytes(@utf8.encode(number.to_string()))
      buffer.to_bytes()
    }
  }
}

///|
fn command_arguments(command : @prover.CommandSpecView) -> Array[String] raise {
  let result : Array[String] = []
  for argument in command.arguments {
    result.push(
      @utf8.decode(argument) catch {
        _ =>
          raise @prover.ConfigError({
            kind: @prover.InvalidCommand,
            message: "native prover argument is not UTF-8",
          })
      },
    )
  }
  result
}

///|
fn launcher_environment(
  executable : StringView,
  arguments : ArrayView[String],
) -> Map[String, String] {
  let environment = @env.get_env_vars()
  environment["LC_ALL"] = "C"
  environment["WHY3MBT_INTERNAL_LAUNCH"] = "1"
  environment["WHY3MBT_INTERNAL_EXECUTABLE"] = executable.to_owned()
  environment["WHY3MBT_INTERNAL_ARGC"] = arguments.length().to_string()
  for index, argument in arguments {
    environment["WHY3MBT_INTERNAL_ARG_" + index.to_string()] = argument
  }
  environment
}

///|
async fn write_query(writer : @process.WriteToProcess, query : Bytes) -> Unit {
  writer.write(query) catch {
    err if @async.is_being_cancelled() => raise err
    err =>
      raise @prover.ProcessError({
        kind: @prover.BrokenPipe,
        exit_code: None,
        signal: None,
        message: "failed to write prover stdin: \{err}",
      })
  }
  writer.close()
}

///|
async fn NativeRunner::run_without_deadline(
  self : NativeRunner,
  query : Bytes,
) -> @prover.RawProcessOutcome {
  let command = self.command.view()
  let arguments = command_arguments(command)
  let environment = launcher_environment(self.executable.path(), arguments)
  let (process_stdin, stdin_writer) = @process.write_to_process()
  let (stdout_reader, process_stdout) = @process.read_from_process()
  let (stderr_reader, process_stderr) = @process.read_from_process()
  defer stdin_writer.close()
  defer stdout_reader.close()
  defer stderr_reader.close()
  @async.with_task_group() <| group => {
    let process = @process.spawn(
      group,
      self.launcher.executable.path(),
      self.launcher.arguments,
      extra_env=environment,
      inherit_env=false,
      stdin=process_stdin,
      stdout=process_stdout,
      stderr=process_stderr,
      cancel_handler=process_group_hard_cancel(),
    ) catch {
      err =>
        raise @prover.ProcessError({
          kind: @prover.SpawnFailed,
          exit_code: None,
          signal: None,
          message: "failed to spawn prover launcher: \{err}",
        })
    }
    let writer_task = group.spawn(() => write_query(stdin_writer, query))
    let stdout_task = group.spawn(() => {
      bounded_capture(
        stdout_reader,
        @prover.StandardOutput,
        command.stdout_limit_bytes,
      )
    })
    let stderr_task = group.spawn(() => {
      bounded_capture(
        stderr_reader,
        @prover.StandardError,
        command.stderr_limit_bytes,
      )
    })
    let exit_code = process.wait()
    writer_task.wait()
    let stdout = stdout_task.wait()
    let stderr = stderr_task.wait()
    let status = if exit_code >= 128 && exit_code <= 255 {
      @prover.Signaled(signal_name(exit_code - 128))
    } else {
      @prover.Exited(exit_code)
    }
    @prover.RawProcessOutcome::new(stdout, stderr, status)
  }
}

///|
pub async fn NativeRunner::run(
  self : NativeRunner,
  query : BytesView,
) -> NativeRunOutcome {
  try {
    let query = query.to_owned()
    let policy = self.command.view().parent_deadline_policy
    match policy {
      @prover.NoAutomaticDeadline => Completed(self.run_without_deadline(query))
      @prover.DeadlineAfterSeconds(seconds) =>
        Completed(
          @async.with_timeout(seconds * 1000, () => {
            self.run_without_deadline(query)
          }),
        ) catch {
          @async.TimeoutError => ParentDeadlineExceeded
          err => raise err
        }
    }
  } catch {
    err if @async.is_cancellation_error(err) =>
      raise @prover.ProcessError({
        kind: @prover.Cancelled,
        exit_code: None,
        signal: None,
        message: "prover invocation was cancelled",
      })
    err => raise err
  }
}
