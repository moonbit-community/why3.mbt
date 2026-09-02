// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct DLocal {
  id : Int
  name : Bytes
  origin : @identity.Origin
  ty : Dty
  reference : Bool
}

///|
priv struct PureTyping {
  semantic_context : @identity.CompilationContext
  environment : @environment.Environment
  library_path : Array[Bytes]
  file_theories : Array[(Bytes, @theory.Theory)]
  delayed : DtyContext
  mut known : @logic.KnownMap
  mut coercions : @theory.CoercionMap
  mut next_local_id : Int
}

///|
fn PureTyping::new(
  semantic_context : @identity.CompilationContext,
  environment : @environment.Environment,
  library_path? : ArrayView[Bytes] = [],
  file_theories? : ArrayView[(Bytes, @theory.Theory)] = [],
) -> PureTyping {
  {
    semantic_context,
    environment,
    library_path: library_path.to_owned(),
    file_theories: file_theories.to_owned(),
    delayed: DtyContext::new(semantic_context),
    known: @logic.KnownMap::new(semantic_context),
    coercions: @theory.CoercionMap::empty(),
    next_local_id: 0,
  }
}

///|
fn PureTyping::sync_known(self : PureTyping, known : @logic.KnownMap) -> Unit {
  self.known = known
}

///|
fn PureTyping::sync_coercions(
  self : PureTyping,
  coercions : @theory.CoercionMap,
) -> Unit {
  self.coercions = coercions
}

///|
fn ident_has_reference_marker(ident : @parser.Ident) -> Bool {
  ident.attributes.any(attribute => {
    attribute is Text(name) && name == b"mlw:reference_var"
  })
}

///|
fn PureTyping::make_local(
  self : PureTyping,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  ty : Dty,
) -> DLocal {
  let id = self.next_local_id
  self.next_local_id = id + 1
  match ident {
    Some(ident) => {
      let origin = user_origin(ident)
      {
        id,
        name: ident.name,
        origin,
        ty,
        reference: ident_has_reference_marker(ident),
      }
    }
    None => {
      let span = source_span(fallback_span)
      {
        id,
        name: b"_",
        origin: @identity.Origin::user(b"_", Some(span), []),
        ty,
        reference: false,
      }
    }
  }
}

///|
fn find_local(locals : ArrayView[(Bytes, DLocal)], name : BytesView) -> DLocal? {
  for index = locals.length() - 1; index >= 0; index = index - 1 {
    if locals[index].0[:] == name {
      return Some(locals[index].1)
    }
  }
  None
}
