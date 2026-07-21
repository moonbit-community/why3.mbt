// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct DLocal {
  id : Int
  name : Bytes
  origin : @identity.Origin
  ty : Dty
}

///|
priv struct PureTyping {
  semantic_context : @identity.CompilationContext
  environment : @environment.Environment
  delayed : DtyContext
  mut next_local_id : Int
}

///|
fn PureTyping::new(
  semantic_context : @identity.CompilationContext,
  environment : @environment.Environment,
) -> PureTyping {
  {
    semantic_context,
    environment,
    delayed: DtyContext::new(semantic_context),
    next_local_id: 0,
  }
}

///|
fn PureTyping::make_local(
  self : PureTyping,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  ty : Dty,
) -> DLocal raise ElabError {
  let id = self.next_local_id
  self.next_local_id = id + 1
  match ident {
    Some(ident) => {
      let origin = user_origin(ident)
      { id, name: ident.name, origin, ty }
    }
    None => {
      let span = source_span(fallback_span)
      {
        id,
        name: b"_",
        origin: @identity.Origin::user(b"_", Some(span), []),
        ty,
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
