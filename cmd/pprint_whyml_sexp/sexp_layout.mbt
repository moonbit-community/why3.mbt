// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

// Why3 1.7.2 prints S-expressions with an OCaml Format hv box at offset 2.
// Format.std_formatter uses a margin of 78 and a maximum indentation of 68.

///|
let why3_margin : Int = 78

///|
let why3_max_indent : Int = 68

///|
let why3_box_indent : Int = 2

///|
priv struct Why3SexpLayout {
  document : @prettyprinter.Document
  flat_length : Int
}

///|
fn Sexp::to_why3_layout(self : Sexp) -> Why3SexpLayout {
  match self {
    Atom(value) => {
      let builder = StringBuilder::new()
      write_atom(builder, value)
      let text = builder.to_string()
      { document: @prettyprinter.text(text), flat_length: text.length() }
    }
    List(items) => {
      let documents = []
      let mut flat_length = 2
      for index, item in items {
        let layout = item.to_why3_layout()
        documents.push(layout.document)
        if index > 0 {
          flat_length += 1
        }
        flat_length += layout.flat_length
      }
      let document = @prettyprinter.dynamic(context => {
        // OCaml Format keeps an hv box horizontal only while it ends strictly
        // before the margin; otherwise every separator in this box breaks.
        let separator = if context.indent + flat_length < context.width {
          @prettyprinter.space
        } else {
          @prettyprinter.hardline
        }
        let requested_indent = context.indent + why3_box_indent
        let next_indent = if requested_indent > why3_max_indent {
          why3_max_indent
        } else {
          requested_indent
        }
        let indent = next_indent - context.next_indent
        @prettyprinter.char('(') +
        @prettyprinter.nest(
          indent~,
          @prettyprinter.separate(separator, documents),
        ) +
        @prettyprinter.char(')')
      })
      { document, flat_length }
    }
  }
}

///|
fn Sexp::render(self : Sexp) -> String {
  @prettyprinter.render(self.to_why3_layout().document, width=why3_margin)
}
