// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
async fn test_cli_configuration_defaults() -> Unit {
  let options = resolve_cli_configuration(
    parse_arguments([
      "why3mbt", "prove", "-C", "fixtures/why3mbt-z3.conf", "tools/why3_reference/fixtures/mvp.mlw",
    ]),
  )
  assert_eq(options.loadpaths.length(), 1)
  assert_true(options.loadpaths[0].has_suffix("/fixtures/why3-1.7.2/stdlib"))
  assert_true(!options.use_stdlib)
  assert_true(!options.load_default_plugins)
  assert_eq(options.requested_solver_seconds, 0.25)
  assert_eq(options.solver_seconds, 1)
  assert_eq(options.memory_limit_mib, 64)
  assert_eq(options.z3, Some(b"/opt/pinned-z3"))
}

///|
test "CLI configuration rejects requested plugin loading unless overridden" {
  let parsed = parsed_configuration(
    "[main]\nload_default_plugins = true\n", "plugin.conf",
  )
  try validate_configuration_plugins(parsed, true) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, UnsupportedCliFeature)
  } noraise {
    _ => fail("configuration-requested plugins must be rejected")
  }
  validate_configuration_plugins(parsed, false)
  let explicit = parsed_configuration(
    "[main]\nplugin = \"custom\"\n", "plugin.conf",
  )
  try validate_configuration_plugins(explicit, false) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, UnsupportedCliFeature)
  } noraise {
    _ => fail("explicit configuration plugins must always be rejected")
  }
}

///|
test "CLI discovers the Why3 main configuration in official priority order" {
  let explicit = select_main_configuration(
    Some("explicit.conf"),
    Some("environment.conf"),
    Some("/home/example"),
  )
  assert_eq(explicit.path, Some("explicit.conf"))
  assert_true(explicit.required)
  let environment = select_main_configuration(
    None,
    Some("environment.conf"),
    Some("/home/example"),
  )
  assert_eq(environment.path, Some("environment.conf"))
  assert_true(environment.required)
  let home = select_main_configuration(None, None, Some("/home/example"))
  assert_eq(home.path, Some("/home/example/.why3.conf"))
  assert_true(!home.required)
  let disabled = select_main_configuration(Some(""), Some("ignored.conf"), None)
  assert_eq(disabled.path, None)
  assert_true(!disabled.required)
}

///|
test "extra configuration prepends paths without replacing main limits" {
  let main = parsed_configuration(
    "[main]\nloadpath = \"main-lib\"\ntimelimit = 2.5\nmemlimit = 64\n", "/config/main.conf",
  )
  let extra = parsed_configuration(
    "[main]\nloadpath = \"extra-lib\"\ntimelimit = 9\nmemlimit = 512\n", "/extra/extra.conf",
  )
  let merged = merge_extra_configuration(main, extra)
  assert_eq(merged.loadpaths, ["/extra/extra-lib", "/config/main-lib"])
  assert_eq(merged.solver_seconds, Some(2.5))
  assert_eq(merged.memory_limit_mib, Some(64))
}
