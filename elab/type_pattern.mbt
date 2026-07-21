// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn pty_has_arrow(pty : @parser.Pty) -> Bool {
  match pty {
    PTarrow(_, _) => true
    PTtyapp(_, arguments) | PTtuple(arguments) | PTref(arguments) =>
      arguments.any(pty_has_arrow)
    PTscope(_, nested) | PTparen(nested) | PTpure(nested) =>
      pty_has_arrow(nested)
    PTtyvar(_) => false
  }
}

///|
fn PureTyping::dty_of_pty(
  self : PureTyping,
  space : @theory.Namespace,
  pty : @parser.Pty,
) -> Dty raise {
  match pty {
    PTtyvar(ident) => {
      let span = source_span(ident.span)
      let variable = self.environment.intern_type_variable(
        self.semantic_context,
        ident.name,
        user_origin(ident),
        Some(span),
      )
      self.delayed.known(@logic.Ty::variable(variable), Some(span))
    }
    PTtyapp(qualid, arguments) => {
      let span = qualid_span(qualid)
      let symbol = space.find_type(qualid_segments(qualid), Some(span))
      let delayed_arguments = [
        for argument in arguments => self.dty_of_pty(space, argument)
      ]
      self.delayed.app(symbol, delayed_arguments, Some(span))
    }
    PTarrow(parameter, result) => {
      let parameter = self.dty_of_pty(space, parameter)
      let result = self.dty_of_pty(space, result)
      self.delayed.arrow(parameter, result, None)
    }
    PTscope(qualid, nested) => {
      let span = qualid_span(qualid)
      let imported = space.import_scope(qualid_segments(qualid), Some(span))
      self.dty_of_pty(imported, nested)
    }
    PTparen(nested) => self.dty_of_pty(space, nested)
    PTtuple(_) =>
      fail_unsupported(
        TupleType,
        FeatureClassification,
        None,
        "tuple types are outside the MVP",
      )
    PTref(_) =>
      fail_unsupported(
        Reference,
        FeatureClassification,
        None,
        "reference types are outside the MVP",
      )
    PTpure(_) =>
      fail_unsupported(
        TypePurification,
        FeatureClassification,
        None,
        "type purification is outside the MVP",
      )
  }
}

///|
fn PureTyping::ty_of_pty(
  self : PureTyping,
  space : @theory.Namespace,
  pty : @parser.Pty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  if pty_has_arrow(pty) {
    fail_unsupported(
      HigherOrder,
      FeatureClassification,
      span,
      "higher-order pure types are outside the MVP",
    )
  }
  self.delayed.finalize_pure(self.dty_of_pty(space, pty), span)
}
