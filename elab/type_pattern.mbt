// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

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
      let imported = space.open_scope(qualid_segments(qualid), Some(span))
      self.dty_of_pty(imported, nested)
    }
    PTparen(nested) => self.dty_of_pty(space, nested)
    PTtuple(arguments) =>
      self.delayed.app(
        space.find_type([tuple_type_name(arguments.length())], None),
        arguments.map(argument => self.dty_of_pty(space, argument)),
        None,
      )
    PTref(arguments) =>
      self.delayed.app(
        space.find_type([b"ref"], None),
        arguments.map(argument => self.dty_of_pty(space, argument)),
        None,
      )
    PTpure(nested) => self.dty_of_pty(space, nested)
  }
}

///|
fn PureTyping::ty_of_pty(
  self : PureTyping,
  space : @theory.Namespace,
  pty : @parser.Pty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  self.finalize_dty(space, self.dty_of_pty(space, pty), span)
}
