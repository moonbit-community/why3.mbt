// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct SnapshotManifest {
  schema_version : Int
  snapshot_schema_version : Int
  why3_version : Bytes
  why3_commit : Bytes
  why3_tree : Bytes
  driver_profile : Bytes
  payload_length : Int
  payload_sha256 : Bytes
  theory_count : Int
  module_count : Int
  symbol_count : Int
  type_variable_count : Int
}

///|
pub(all) struct SnapshotManifestView {
  schema_version : Int
  snapshot_schema_version : Int
  why3_version : Bytes
  why3_commit : Bytes
  why3_tree : Bytes
  driver_profile : Bytes
  payload_length : Int
  payload_sha256 : Bytes
  theory_count : Int
  module_count : Int
  symbol_count : Int
  type_variable_count : Int
}

///|
fn frozen_snapshot_manifest() -> SnapshotManifest {
  {
    schema_version: 1,
    snapshot_schema_version: 1,
    why3_version: b"1.7.2",
    why3_commit: b"1343338d3bb1941c0d4f134283bb0790816113c4",
    why3_tree: b"f5e82693620413d7d8e3ebcba69addcb6a65f877",
    driver_profile: b"z3_487",
    payload_length: 10512401,
    payload_sha256: b"\x15\x87\x8b\x10\x32\x8d\x2b\xbb\xc7\x12\x07\xdd\x59\xb8\x69\xa9\x56\x6a\x21\x37\xcb\xe3\xf1\x00\x1b\x4f\xc2\x62\x75\x3a\xd3\x1d",
    theory_count: 73,
    module_count: 25,
    symbol_count: 2317,
    type_variable_count: 10,
  }
}

///|
pub fn SnapshotManifest::view(self : SnapshotManifest) -> SnapshotManifestView {
  {
    schema_version: self.schema_version,
    snapshot_schema_version: self.snapshot_schema_version,
    why3_version: self.why3_version,
    why3_commit: self.why3_commit,
    why3_tree: self.why3_tree,
    driver_profile: self.driver_profile,
    payload_length: self.payload_length,
    payload_sha256: self.payload_sha256,
    theory_count: self.theory_count,
    module_count: self.module_count,
    symbol_count: self.symbol_count,
    type_variable_count: self.type_variable_count,
  }
}
