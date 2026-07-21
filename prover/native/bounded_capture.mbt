// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
async fn bounded_capture(
  reader : @process.ReadFromProcess,
  stream : @prover.ProverStream,
  limit_bytes : Int,
) -> Bytes {
  let buffer = @buffer.Buffer(size_hint=limit_bytes)
  let mut captured = 0
  for ;; {
    let remaining = limit_bytes - captured
    let requested = if remaining <= 0 {
      1
    } else if remaining < 65536 {
      remaining + 1
    } else {
      65536
    }
    let chunk = reader.read_some(max_len=requested) catch {
      err if @async.is_being_cancelled() => raise err
      err =>
        raise @prover.ProcessError({
          kind: @prover.ReadFailed,
          exit_code: None,
          signal: None,
          message: "failed to read prover output: \{err}",
        })
    }
    match chunk {
      None => return buffer.to_bytes()
      Some(bytes) => {
        if bytes.length() > remaining {
          raise @prover.OutputLimitExceeded({ stream, limit_bytes })
        }
        buffer.write_bytes(bytes)
        captured = captured + bytes.length()
      }
    }
  }
}
