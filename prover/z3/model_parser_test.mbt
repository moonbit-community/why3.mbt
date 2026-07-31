// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "SMTv2 model parser retains constants arrays functions and solver terms" {
  let source =
    #|sat
    #|(
    #|  (define-fun neg () Int (- 12))
    #|  (define-fun ratio () Real (/ 1.0 3.0))
    #|  (define-fun memory () (Array Int Int)
    #|    (store ((as const (Array Int Int)) 0) 2 7))
    #|  (define-fun bits () (_ BitVec 8) #x2a)
    #|  (define-fun zero () (_ FloatingPoint 8 24) (_ +zero 8 24))
    #|  (define-fun text () String "a""b")
    #|  (define-fun choose ((x Int)) Int (ite (= x 0) 1 x))
    #|)
    #|(:rlimit-count 10)
  let model = parse_smtv2_model(@utf8.encode(source))
  assert_eq(model.definitions().length(), 7)
  guard model.definitions()[0]
    is {
      name: b"neg",
      body: ConstantTerm(IntegerConstant({ value, verbatim: b"-12" })),
      ..,
    } else {
    fail("negative integer model value was not retained")
  }
  assert_eq(value, BigInt::from_int(-12))
  guard model.definitions()[1].body
    is ConstantTerm(
      FractionConstant(
        {
          numerator: { significand: numerator, decimal_scale: 1, .. },
          denominator: { significand: denominator, decimal_scale: 1, .. },
          ..,
        }
      )
    ) else {
    fail("fraction model value was not retained")
  }
  assert_eq(numerator, BigInt::from_int(10))
  assert_eq(denominator, BigInt::from_int(30))
  guard model.definitions()[2].body
    is ArrayTerm(
      IntegerSort,
      IntegerSort,
      { indices: [(index, element)], others }
    ) else {
    fail("array store model value was not normalized")
  }
  assert_true(
    index is ConstantTerm(IntegerConstant({ value, .. })) &&
    value == BigInt::from_int(2),
  )
  assert_true(
    element is ConstantTerm(IntegerConstant({ value, .. })) &&
    value == BigInt::from_int(7),
  )
  assert_true(
    others is ConstantTerm(IntegerConstant({ value, .. })) &&
    value == BigInt::from_int(0),
  )
  assert_true(
    model.definitions()[3].body
    is ConstantTerm(
      BitVectorConstant({ value, bit_length: 8, verbatim: b"#x2a" })
    ) &&
    value == BigInt::from_int(42),
  )
  assert_true(
    model.definitions()[4].body
    is ConstantTerm(
      FloatConstant({ exponent_size: 8, significand_size: 24, value: PlusZero })
    ),
  )
  assert_true(
    model.definitions()[5].body is ConstantTerm(StringConstant(b"a\"\"b")),
  )
  assert_true(
    model.definitions()[6].body
    is ConditionalTerm(ApplicationTerm(_, [_, _]), _, _),
  )
}

///|
test "SMTv2 model parser accepts model wrappers quoted names and as-array" {
  let source =
    #|(model
    #|  (define-fun |quoted name| () Bool true)
    #|  (define-fun a () (Array Int Int) (_ as-array @uc_Int_0))
    #|  (define-fun opaque () Int (lambda ((x Int)) x)))
  let model = parse_smtv2_model(@utf8.encode(source))
  guard model.definitions()
    is [
      { name: b"quoted name", body: ConstantTerm(BooleanConstant(true)), .. },
      { name: b"a", body: AsArrayTerm(VariableTerm(_)), .. },
      {
        name: b"opaque",
        body: ApplicationTerm(
          UnannotatedIdentifier(SimpleIdentifier(UserSymbol(b"lambda"))),
          [UnparsedTerm(b"((x Int))"), VariableTerm(_)]
        ),
        ..,
      },
    ] else {
    fail("wrapped SMT model was not parsed as expected")
  }
}

///|
test "SMTv2 model parser reports structural S-expression failures" {
  try parse_smtv2_model(b"((define-fun x () Int 0)") catch {
    ModelParseError(diagnostic) => {
      assert_eq(diagnostic.kind, UnclosedModelList)
      assert_eq(diagnostic.byte_offset, 0)
    }
  } noraise {
    _ => fail("expected an unclosed SMT model error")
  }
  try parse_smtv2_model(b"(model (define-fun x () String \"no))") catch {
    ModelParseError(diagnostic) =>
      assert_eq(diagnostic.kind, UnclosedModelString)
  } noraise {
    _ => fail("expected an unterminated SMT string error")
  }
}
