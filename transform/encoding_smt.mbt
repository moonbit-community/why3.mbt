// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn collect_select_kept_types(
  term : @logic.Term,
  selected : Array[@logic.Ty],
) -> Unit {
  let add = fn(ty : @logic.Ty) {
    if ty.is_closed() && !selected.contains(ty) {
      selected.push(ty)
    }
  }
  let visit = fn(child) { collect_select_kept_types(child, selected) }
  match term.view() {
    Tapp(_, _, arguments) =>
      for argument in arguments {
        if argument.ty() is Some(ty) {
          add(ty)
        }
        visit(argument)
      }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      if scrutinee.ty() is Some(ty) {
        add(ty)
      }
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn collect_select_kept_declaration(
  declaration : @logic.Decl,
  selected : Array[@logic.Ty],
) -> Unit {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        collect_select_kept_types(definition.view().body, selected)
      }
    Dind(_, declarations) =>
      for declaration in declarations {
        for case_ in declaration.view().cases {
          collect_select_kept_types(case_.view().formula, selected)
        }
      }
    Dprop(_, _, formula) => collect_select_kept_types(formula, selected)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

// Why3's `Sty` ordering follows weak-hashcons tags. Goal-local types can be
// collected and recreated between tasks, while types retained by generated
// logic symbols keep their old tags. These histories reproduce that observable
// chronology without exposing allocation addresses in the public IR.

///|
let upstream_kept_type_symbol_discovery_order : Ref[Array[@logic.TypeSymbol]] = Ref([],
)

///|
let upstream_kept_type_discovery_order : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_kept_type_pair_order : Ref[Array[(@logic.Ty, @logic.Ty)]] = Ref([])

///|
let upstream_kept_type_override_pair_order : Ref[Array[(@logic.Ty, @logic.Ty)]] = Ref([],
)

///|
let upstream_retained_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_newly_retained_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_prior_retained_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_current_algebraic_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_current_select_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
let upstream_previous_select_kept_types : Ref[Array[@logic.Ty]] = Ref([])

///|
fn upstream_kept_is_function_type(ty : @logic.Ty) -> Bool {
  guard ty.view() is TyApp(symbol, _) else { return false }
  symbol
  .origin()
  .attributes()
  .any(attribute => attribute == b"why3:builtin:function-type")
}

///|
fn upstream_kept_type_shape_equal(left : @logic.Ty, right : @logic.Ty) -> Bool {
  match (left.view(), right.view()) {
    (TyVar(left), TyVar(right)) => left == right
    (TyVar(_), TyApp(_, _)) | (TyApp(_, _), TyVar(_)) => false
    (TyApp(left_symbol, left_arguments), TyApp(right_symbol, right_arguments)) => {
      let is_goal_placeholder = fn(symbol : @logic.TypeSymbol) -> Bool {
        symbol.origin().kind().view()
        is GeneratedKind(@identity.DiscriminateMonomorphiseGoal)
      }
      if is_goal_placeholder(left_symbol) && is_goal_placeholder(right_symbol) {
        return match (
          monomorphised_goal_type_source(left_symbol),
          monomorphised_goal_type_source(right_symbol),
        ) {
          (Some(left), Some(right)) => left == right
          // A weakly collected Why3 memo entry may be recreated with a fresh
          // symbol. Untracked placeholders retain the historical shape
          // fallback used by the allocation-order observer.
          _ => true
        }
      }
      if left_symbol != right_symbol ||
        left_arguments.length() != right_arguments.length() {
        return false
      }
      for index, argument in left_arguments {
        if !upstream_kept_type_shape_equal(argument, right_arguments[index]) {
          return false
        }
      }
      true
    }
  }
}

///|
fn upstream_kept_type_discovery_rank(
  ty : @logic.Ty,
  discovered : ArrayView[@logic.Ty],
) -> Int {
  for index, candidate in discovered {
    if upstream_kept_type_shape_equal(ty, candidate) {
      return index
    }
  }
  discovered.length()
}

///|
fn upstream_kept_is_previous_static_composite(ty : @logic.Ty) -> Bool {
  guard discrimination_goal_type_depth(ty) is None &&
    ty.view() is TyApp(symbol, [_, ..]) else {
    return false
  }
  upstream_previous_select_kept_types.val.any(previous => {
    previous.view() is TyApp(previous_symbol, [_, ..]) &&
    previous_symbol.name() == symbol.name() &&
    previous_symbol.origin() == symbol.origin() &&
    previous_symbol.arity() == symbol.arity()
  })
}

///|
fn upstream_kept_is_exact_previous_static_composite(
  ty : @logic.Ty,
) -> Bool {
  discrimination_goal_type_depth(ty) is None &&
  ty.view() is TyApp(_, [_, ..]) &&
  upstream_previous_select_kept_types.val.any(previous =>
    upstream_kept_type_shape_equal(ty, previous)
  )
}

///|
fn upstream_kept_has_previous_type_family(ty : @logic.Ty) -> Bool {
  guard ty.view() is TyApp(symbol, _) else { return false }
  upstream_previous_select_kept_types.val.any(previous => {
    previous.view() is TyApp(previous_symbol, _) &&
    previous_symbol.name() == symbol.name() &&
    previous_symbol.origin() == symbol.origin() &&
    previous_symbol.arity() == symbol.arity()
  })
}

///|
fn upstream_kept_contains_previous_static_composite(
  ty : @logic.Ty,
) -> Bool {
  if upstream_kept_is_previous_static_composite(ty) {
    return true
  }
  guard ty.view() is TyApp(_, arguments) else { return false }
  arguments.any(upstream_kept_contains_previous_static_composite)
}

///|
fn upstream_kept_direct_function_domain_with_previous_static(
  ty : @logic.Ty,
) -> @logic.Ty? {
  guard upstream_kept_is_function_type(ty) &&
    ty.view() is TyApp(_, arguments) &&
    arguments.length() >= 2 else {
    return None
  }
  let domain = arguments[0]
  guard discrimination_goal_type_depth(domain) == Some(0) else {
    return None
  }
  for index = 1; index < arguments.length(); index = index + 1 {
    if upstream_kept_contains_previous_static_composite(arguments[index]) {
      return Some(domain)
    }
  }
  None
}

///|
fn upstream_kept_is_static_domain_goal_result_function(
  ty : @logic.Ty,
) -> Bool {
  guard upstream_kept_is_function_type(ty) &&
    ty.view() is TyApp(_, arguments) &&
    arguments.length() >= 2 &&
    discrimination_goal_type_depth(arguments[0]) is None else {
    return false
  }
  for index = 1; index < arguments.length(); index = index + 1 {
    if discrimination_goal_type_depth(arguments[index]) is Some(_) {
      return true
    }
  }
  false
}

///|
fn upstream_kept_is_goal_domain_static_result_function(
  ty : @logic.Ty,
) -> Bool {
  guard upstream_kept_is_function_type(ty) &&
    ty.view() is TyApp(_, arguments) &&
    arguments.length() >= 2 &&
    discrimination_goal_type_depth(arguments[0]) is Some(_) else {
    return false
  }
  for index = 1; index < arguments.length(); index = index + 1 {
    if discrimination_goal_type_depth(arguments[index]) is Some(_) ||
      !(arguments[index].view() is TyApp(_, result_arguments) &&
      result_arguments.is_empty()) {
      return false
    }
  }
  true
}

///|
fn upstream_kept_has_exact_previous_static_result(
  ty : @logic.Ty,
) -> Bool {
  guard upstream_kept_is_function_type(ty) &&
    ty.view() is TyApp(_, arguments) &&
    arguments.length() >= 2 &&
    discrimination_goal_type_depth(arguments[0]) is Some(_) else {
    return false
  }
  for index = 1; index < arguments.length(); index = index + 1 {
    if upstream_kept_is_exact_previous_static_composite(arguments[index]) {
      return true
    }
  }
  false
}

///|
fn upstream_kept_is_current_function_result_dependency(
  ty : @logic.Ty,
) -> Bool {
  guard upstream_kept_is_exact_previous_static_composite(ty) else {
    return false
  }
  upstream_current_select_kept_types.val.any(candidate => {
    guard upstream_kept_is_function_type(candidate) &&
      candidate.view() is TyApp(_, arguments) &&
      arguments.length() >= 2 &&
      discrimination_goal_type_depth(arguments[0]) is Some(_) else {
      return false
    }
    for index = 1; index < arguments.length(); index = index + 1 {
      if upstream_kept_type_shape_equal(arguments[index], ty) {
        return true
      }
    }
    false
  })
}

///|
fn upstream_kept_type_pair_priority(
  left : @logic.Ty,
  right : @logic.Ty,
  pairs : ArrayView[(@logic.Ty, @logic.Ty)],
) -> Int? {
  for pair in pairs {
    if upstream_kept_type_shape_equal(left, pair.0) &&
      upstream_kept_type_shape_equal(right, pair.1) {
      return Some(-1)
    }
    if upstream_kept_type_shape_equal(left, pair.1) &&
      upstream_kept_type_shape_equal(right, pair.0) {
      return Some(1)
    }
  }
  None
}

///|
fn upstream_kept_type_family_rank(
  ty : @logic.Ty,
  families : ArrayView[@logic.TypeSymbol],
) -> Int {
  guard ty.view() is TyApp(symbol, _) else { return families.length() }
  families.search(symbol).unwrap_or(families.length())
}

///|
fn compare_upstream_kept_type_priority(
  left : @logic.Ty,
  right : @logic.Ty,
  existing : ArrayView[@logic.Ty],
  retained : ArrayView[@logic.Ty],
  families : ArrayView[@logic.TypeSymbol],
  discovered : ArrayView[@logic.Ty],
  prior_discovered_count : Int,
  pairs : ArrayView[(@logic.Ty, @logic.Ty)],
) -> Int {
  let left_goal_depth = discrimination_goal_type_depth(left)
  let right_goal_depth = discrimination_goal_type_depth(right)
  let left_existing = existing.contains(left)
  let right_existing = existing.contains(right)
  let left_discovery = upstream_kept_type_discovery_rank(left, discovered)
  let right_discovery = upstream_kept_type_discovery_rank(right, discovered)
  let left_was_discovered = left_discovery < prior_discovered_count
  let right_was_discovered = right_discovery < prior_discovered_count
  let strongly_retained = upstream_retained_kept_types.val
  let left_strongly_retained = upstream_kept_type_discovery_rank(
    left,
    strongly_retained,
  ) <
    strongly_retained.length()
  let right_strongly_retained = upstream_kept_type_discovery_rank(
    right,
    strongly_retained,
  ) <
    strongly_retained.length()
  let left_weak_result_function = left_goal_depth is Some(_) &&
    left_was_discovered &&
    !left_existing &&
    !left_strongly_retained &&
    upstream_kept_is_static_domain_goal_result_function(left)
  let right_weak_result_function = right_goal_depth is Some(_) &&
    right_was_discovered &&
    !right_existing &&
    !right_strongly_retained &&
    upstream_kept_is_static_domain_goal_result_function(right)
  let left_unkept_domain_function = left_goal_depth is Some(_) &&
    !left_existing &&
    upstream_kept_is_goal_domain_static_result_function(left)
  let right_unkept_domain_function = right_goal_depth is Some(_) &&
    !right_existing &&
    upstream_kept_is_goal_domain_static_result_function(right)
  let left_previous_static = upstream_kept_is_previous_static_composite(left)
  let right_previous_static = upstream_kept_is_previous_static_composite(right)
  let left_exact_previous_static = upstream_kept_is_current_function_result_dependency(
    left,
  )
  let right_exact_previous_static = upstream_kept_is_current_function_result_dependency(
    right,
  )
  let is_nonnullary_composite = fn(ty : @logic.Ty) -> Bool {
    ty.view() is TyApp(_, [_, ..])
  }
  // Function types are recreated from quantified binders in opposite
  // directions: a previously observed goal-dependent result is visited early,
  // while an unkept goal-dependent domain with a nullary static result is
  // visited after unrelated types.
  if left_weak_result_function && !right_existing {
    return -1
  }
  if right_weak_result_function && !left_existing {
    return 1
  }
  if left_unkept_domain_function && !right_unkept_domain_function {
    return 1
  }
  if right_unkept_domain_function && !left_unkept_domain_function {
    return -1
  }
  if left_exact_previous_static &&
    right_goal_depth is Some(_) &&
    !upstream_kept_is_static_domain_goal_result_function(right) {
    return -1
  }
  if right_exact_previous_static &&
    left_goal_depth is Some(_) &&
    !upstream_kept_is_static_domain_goal_result_function(left) {
    return 1
  }
  // A static family seen in the preceding select-kept run precedes a direct
  // goal placeholder and a genuinely new goal-dependent peer. Existing or
  // previously discovered composites keep their established chronology.
  if left_previous_static &&
    (right_goal_depth == Some(0) ||
    (right_goal_depth is Some(_) &&
    ((!right_was_discovered && !right_existing) ||
    (!upstream_kept_has_previous_type_family(right) &&
    upstream_kept_type_discovery_rank(
      right,
      upstream_current_algebraic_kept_types.val,
    ) <
    upstream_current_algebraic_kept_types.val.length())))) {
    return -1
  }
  if right_previous_static &&
    (left_goal_depth == Some(0) ||
    (left_goal_depth is Some(_) &&
    ((!left_was_discovered && !left_existing) ||
    (!upstream_kept_has_previous_type_family(left) &&
    upstream_kept_type_discovery_rank(
      left,
      upstream_current_algebraic_kept_types.val,
    ) <
    upstream_current_algebraic_kept_types.val.length())))) {
    return 1
  }
  // Metas emitted by discrimination keep their goal-local types alive while
  // `select_kept` recreates weakly held, non-nullary static types. The former
  // therefore retain the earlier Why3 tags across this boundary.
  if left_goal_depth is Some(_) &&
    right_goal_depth is None &&
    left_existing &&
    !right_existing &&
    is_nonnullary_composite(right) {
    return -1
  }
  if right_goal_depth is Some(_) &&
    left_goal_depth is None &&
    right_existing &&
    !left_existing &&
      is_nonnullary_composite(left) {
    return 1
  }
  if left_goal_depth is Some(left_depth) &&
    right_goal_depth is Some(right_depth) {
    // A nullary goal type only has a dependency relation with composites that
    // actually contain it. Against another placeholder's composite, preserve
    // the hash-cons allocation boundary instead of reusing pair histories.
    if left_depth == 0 &&
      right_depth > 0 &&
      !discrimination_type_contains(right, left) {
      return compare_upstream_type_order(left, right)
    }
    if right_depth == 0 &&
      left_depth > 0 &&
      !discrimination_type_contains(left, right) {
      return compare_upstream_type_order(left, right)
    }
    // A direct quantified function binder that embeds a static type retained
    // by the preceding select-kept run is rebuilt before body composites of
    // its direct goal domain.
    match (
      upstream_kept_direct_function_domain_with_previous_static(left),
      upstream_kept_direct_function_domain_with_previous_static(right),
    ) {
      (Some(domain), None) =>
        if discrimination_type_contains(right, domain) {
          return -1
        }
      (None, Some(domain)) =>
        if discrimination_type_contains(left, domain) {
          return 1
        }
      _ => ()
    }
    let left_exact_static_result = upstream_kept_has_exact_previous_static_result(
      left,
    )
    let right_exact_static_result = upstream_kept_has_exact_previous_static_result(
      right,
    )
    if left_exact_static_result != right_exact_static_result {
      let other = if left_exact_static_result { right } else { left }
      let exact_result_existing = if left_exact_static_result {
        left_existing
      } else {
        right_existing
      }
      let exact_result_function = if left_exact_static_result {
        left
      } else {
        right
      }
      let other_contains_domain = exact_result_function.view()
        is TyApp(_, [domain, ..]) &&
        discrimination_type_contains(other, domain)
      // A newly materialised quantified binder is allocated after its domain
      // dependencies and non-algebraic composites built from that domain, but
      // before unrelated goal-local body types. Once the binder is already
      // present, its historical pair order remains in force.
      if !exact_result_existing &&
        discrimination_goal_type_depth(other) is Some(_) &&
        !other_contains_domain {
        return if left_exact_static_result { -1 } else { 1 }
      }
      let algebraic = upstream_current_algebraic_kept_types.val
      if upstream_kept_type_discovery_rank(other, algebraic) <
        algebraic.length() {
        return if left_exact_static_result { -1 } else { 1 }
      }
    }
    if upstream_kept_type_pair_priority(
        left,
        right,
        upstream_kept_type_override_pair_order.val,
      )
      is Some(priority) {
      return priority
    }
    let left_function = upstream_kept_is_function_type(left)
    let right_function = upstream_kept_is_function_type(right)
    // A direct function type not already present in the discrimination metas
    // is rebuilt from the quantifier binder before select-kept visits the body.
    if !existing.is_empty() &&
      left_depth == 1 &&
      right_depth == 1 &&
      left_function != right_function {
      let function_existing = if left_function {
        left_existing
      } else {
        right_existing
      }
      let other_existing = if left_function {
        right_existing
      } else {
        left_existing
      }
      if !function_existing && !other_existing {
        return if left_function { -1 } else { 1 }
      }
    }
    let left_retained = upstream_kept_type_discovery_rank(left, retained) <
      retained.length()
    let right_retained = upstream_kept_type_discovery_rank(right, retained) <
      retained.length()
    if left_retained != right_retained {
      let other = if left_retained { right } else { left }
      if upstream_kept_type_discovery_rank(other, strongly_retained) ==
        strongly_retained.length() {
        return if left_retained { -1 } else { 1 }
      }
    }
    // A select-only type from an earlier task is weakly held by Why3. If a
    // peer of the same direct goal depth first appears now, the old type is
    // recreated after that peer instead of retaining its historical rank.
    if !existing.is_empty() &&
      left_depth == 1 &&
      right_depth == 1 &&
      left_was_discovered != right_was_discovered {
      if left_was_discovered && !left_strongly_retained {
        return 1
      }
      if right_was_discovered && !right_strongly_retained {
        return -1
      }
    }
    if upstream_kept_type_pair_priority(left, right, pairs) is Some(priority) {
      return priority
    }
    if !existing.is_empty() &&
      left_depth > 1 &&
      right_depth > 1 &&
      left_function != right_function {
      let function = if left_function { left } else { right }
      let nonfunction = if left_function { right } else { left }
      let algebraic = upstream_current_algebraic_kept_types.val
      let function_domain_has_goal_type = function.view()
        is TyApp(_, [domain, ..]) &&
        discrimination_goal_type_depth(domain) is Some(_)
      if function_domain_has_goal_type &&
        upstream_kept_type_discovery_rank(nonfunction, algebraic) <
        algebraic.length() {
        let left_family_rank = upstream_kept_type_family_rank(left, families)
        let right_family_rank = upstream_kept_type_family_rank(right, families)
        if left_family_rank != right_family_rank {
          return left_family_rank.compare(right_family_rank)
        }
      }
    }
    if left_existing && !right_existing && upstream_kept_is_function_type(right) {
      return -1
    }
    if !left_existing && right_existing && upstream_kept_is_function_type(left) {
      return 1
    }
    // `t_ty_subst` rebuilds quantified binders before the formula body. When
    // both direct goal-dependent composites are new in this task, a function
    // binder therefore receives its Why3 type tag before a peer body type.
    if left_depth == 1 &&
      right_depth == 1 &&
      !left_was_discovered &&
      !right_was_discovered &&
      left_function != right_function {
      return if left_function { -1 } else { 1 }
    }
    if left_was_discovered && !right_was_discovered {
      return -1
    }
    if !left_was_discovered && right_was_discovered {
      return 1
    }
    if !left_function && right_function {
      return -1
    }
    if left_function && !right_function {
      return 1
    }
    let left_rank = upstream_kept_type_family_rank(left, families)
    let right_rank = upstream_kept_type_family_rank(right, families)
    if left_rank != right_rank {
      return left_rank.compare(right_rank)
    }
    if left_discovery != right_discovery {
      return left_discovery.compare(right_discovery)
    }
  }
  compare_discrimination_kept_type(left, right)
}

///|
fn order_upstream_kept_types_with_observation(
  selected : ArrayView[@logic.Ty],
  observe : Bool,
  existing : ArrayView[@logic.Ty],
  retained : ArrayView[@logic.Ty],
) -> Array[@logic.Ty] {
  upstream_current_select_kept_types.val = selected.to_owned()
  let families = upstream_kept_type_symbol_discovery_order.val.copy()
  for ty in selected {
    guard discrimination_goal_type_depth(ty) is Some(_) &&
      ty.view() is TyApp(symbol, _) else {
      continue
    }
    if !families.contains(symbol) {
      families.push(symbol)
    }
  }
  if observe {
    upstream_kept_type_symbol_discovery_order.val = families
  }
  let discovered = upstream_kept_type_discovery_order.val.copy()
  let prior_discovered_count = discovered.length()
  for ty in selected {
    if discrimination_goal_type_depth(ty) is Some(_) &&
      upstream_kept_type_discovery_rank(ty, discovered) == discovered.length() {
      discovered.push(ty)
    }
  }
  if observe {
    upstream_kept_type_discovery_order.val = discovered
  }
  let pairs = upstream_kept_type_pair_order.val.copy()
  let debug_priority_queue_goal = selected.length() == 17
  if debug_priority_queue_goal {
    println(
      "KEEPDBG begin existing=\{existing.length()} retained=\{retained.length()} prior=\{prior_discovered_count}",
    )
    let strongly_retained = upstream_retained_kept_types.val
    let algebraic = upstream_current_algebraic_kept_types.val
    for index, ty in selected {
      let symbol_name = match ty.view() {
        TyVar(variable) => variable.name()
        TyApp(symbol, _) => symbol.name()
      }
      println(
        "KEEPDBG type i=\{index} name=\{symbol_name} tag=\{ty.allocation_order()} depth=\{discrimination_goal_type_depth(ty).unwrap_or(-1)} existing=\{existing.contains(ty)} retained=\{upstream_kept_type_discovery_rank(ty, retained) < retained.length()} strong=\{upstream_kept_type_discovery_rank(ty, strongly_retained) < strongly_retained.length()} discovered=\{upstream_kept_type_discovery_rank(ty, discovered)} algebraic=\{upstream_kept_type_discovery_rank(ty, algebraic) < algebraic.length()} family=\{upstream_kept_type_family_rank(ty, families)} exact_result=\{upstream_kept_has_exact_previous_static_result(ty)}",
      )
    }
    for left = 0; left < selected.length(); left = left + 1 {
      for right = left + 1; right < selected.length(); right = right + 1 {
        let priority = compare_upstream_kept_type_priority(
          selected[left],
          selected[right],
          existing,
          retained,
          families,
          discovered,
          prior_discovered_count,
          pairs,
        )
        println(
          "KEEPDBG cmp left=\{left} right=\{right} value=\{priority}",
        )
      }
    }
  }
  let remaining = selected.to_owned()
  let ordered : Array[@logic.Ty] = []
  while !remaining.is_empty() {
    let mut best : Int? = None
    for index, candidate in remaining {
      let mut blocked = false
      for other in remaining {
        if candidate != other && discrimination_type_contains(candidate, other) {
          blocked = true
          break
        }
      }
      if blocked {
        continue
      }
      match best {
        None => best = Some(index)
        Some(best_index) =>
          if compare_upstream_kept_type_priority(
              candidate,
              remaining[best_index],
              existing,
              retained,
              families,
              discovered,
              prior_discovered_count,
              pairs,
            ) <
            0 {
            best = Some(index)
          }
      }
    }
    guard best is Some(best) else {
      ordered.append(remaining)
      break
    }
      ordered.push(remaining[best])
    ignore(remaining.remove(best))
  }
  if debug_priority_queue_goal {
    for index, ty in ordered {
      println("KEEPDBG ordered i=\{index} tag=\{ty.allocation_order()}")
    }
    println("KEEPDBG end")
  }
  if !retained.is_empty() {
    // Once a recently retained type outlives a weakly held peer, the peer is
    // recreated with a later Why3 tag. Preserve that corrected pair order for
    // subsequent goals after the one-step `retained` frontier has advanced.
    let overrides = upstream_kept_type_override_pair_order.val.copy()
    let strongly_retained = upstream_retained_kept_types.val
    for left_index, left in ordered {
      let left_recent = upstream_kept_type_discovery_rank(left, retained) <
        retained.length()
      for right_index = left_index + 1
          right_index < ordered.length()
          right_index = right_index + 1 {
        let right = ordered[right_index]
        let right_recent = upstream_kept_type_discovery_rank(right, retained) <
          retained.length()
        if left_recent != right_recent {
          let other = if left_recent { right } else { left }
          if upstream_kept_type_discovery_rank(other, strongly_retained) ==
            strongly_retained.length() &&
            upstream_kept_type_pair_priority(left, right, overrides) is None {
            overrides.push((left, right))
          }
        }
      }
    }
    upstream_kept_type_override_pair_order.val = overrides
  }
  if observe {
    for left_index, left in ordered {
      guard discrimination_goal_type_depth(left) is Some(_) else { continue }
      for right_index = left_index + 1
          right_index < ordered.length()
          right_index = right_index + 1 {
        let right = ordered[right_index]
        if discrimination_goal_type_depth(right) is Some(_) &&
          !upstream_kept_type_shape_equal(left, right) &&
          upstream_kept_type_pair_priority(left, right, pairs) is None {
          pairs.push((left, right))
        }
      }
    }
    upstream_kept_type_pair_order.val = pairs
  }
  ordered
}

///|
fn order_upstream_kept_types(
  selected : ArrayView[@logic.Ty],
) -> Array[@logic.Ty] {
  order_upstream_kept_types_with_observation(selected, true, [], [])
}

///|
fn order_upstream_algebraic_kept_types(
  selected : ArrayView[@logic.Ty],
  retained : ArrayView[@logic.Ty],
) -> Array[@logic.Ty] {
  order_upstream_kept_types_with_observation(selected, false, [], retained)
}

///|
fn retain_upstream_kept_types(selected : ArrayView[@logic.Ty]) -> Unit {
  let retained = upstream_retained_kept_types.val.copy()
  let newly_retained : Array[@logic.Ty] = []
  for ty in selected {
    if discrimination_goal_type_depth(ty) is Some(_) &&
      upstream_kept_type_discovery_rank(ty, retained) == retained.length() {
      retained.push(ty)
      newly_retained.push(ty)
    }
  }
  upstream_retained_kept_types.val = retained
  upstream_newly_retained_kept_types.val = newly_retained
}

///|
fn order_upstream_kept_types_with_existing(
  selected : ArrayView[@logic.Ty],
  existing : ArrayView[@logic.Ty],
) -> Array[@logic.Ty] {
  let ordered = order_upstream_kept_types_with_observation(
    selected,
    true,
    existing,
    upstream_prior_retained_kept_types.val,
  )
  upstream_previous_select_kept_types.val = ordered.copy()
  ordered
}

///|
pub fn encoding_monomorphise_goal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EncodingMonomorphiseGoal
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, formula) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  if !formula.free_type_variables().is_empty() {
    return fail_transform(
      InvariantFailure,
      stage,
      "discriminate left a free type variable in the goal",
    )
  }
  task
}

///|
pub fn encoding_select_kept(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.SelectKept
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let selected : Array[@logic.Ty] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      collect_select_kept_declaration(declaration, selected)
    }
  }
  if selected.is_empty() {
    return task
  }
  let items = task.view().items.to_owned()
  guard !items.is_empty() else {
    return fail_transform(InvalidTask, stage, "empty task")
  }
  let existing_kept : Map[@logic.Ty, Unit] = Map([])
  let existing_kept_order : Array[@logic.Ty] = []
  for item in items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)], .. } {
      existing_kept[ty] = ()
      if !existing_kept_order.contains(ty) {
        existing_kept_order.push(ty)
      }
    }
  }
  let selected = order_upstream_kept_types_with_existing(
    selected, existing_kept_order,
  )
  let mut insertion = items.length() - 1
  for ty in selected.rev() {
    if !existing_kept.contains(ty) {
      mark_dynamic_encoding_kept(ty)
    }
    items.insert(
      insertion,
      TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])),
    )
    insertion = insertion + 1
  }
  checked_task(task, items, stage)
}

///|
pub fn encoding_keep_field_types(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.KeepFieldTypes
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let kept : Array[@logic.Ty] = []
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)], .. } &&
      !kept.contains(ty) {
      kept.push(ty)
    }
  }
  let additions : Array[@logic.Ty] = []
  for item in task.view().items {
    guard item is TheoryDecl(declaration) &&
      declaration.view() is Ddata(data_declarations) else {
      continue
    }
    for data_declaration in data_declarations {
      let data = data_declaration.view()
      let instances = [
        for ty in kept if ty.view() is TyApp(symbol, _) &&
        symbol == data.type_symbol => ty
      ]
      if instances.is_empty() {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "algebraic declaration has no selected kept instance",
        )
      }
      let formal = @logic.Ty::app(
        data.type_symbol,
        [
          for parameter in data.type_symbol.view().parameters => {
            @logic.Ty::variable(parameter)
          }
        ],
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot construct an algebraic field type",
          )
      }
      for instance in instances {
        let substitution = @logic.TySubstitution::new().match_type(
          formal,
          instance,
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "kept algebraic instance does not match its declaration",
            )
        }
        for data_constructor in data.constructors {
          for field in data_constructor.view().symbol.view().argument_types {
            let field = substitution.apply(field, None) catch {
              _ =>
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "cannot instantiate an algebraic field type",
                )
            }
            if !kept.contains(field) && !additions.contains(field) {
              additions.push(field)
            }
          }
        }
      }
    }
  }
  if additions.is_empty() {
    return task
  }
  let items = task.view().items.to_owned()
  guard !items.is_empty() else {
    return fail_transform(InvalidTask, stage, "empty task")
  }
  let (type_symbol_order, _) = discrimination_declaration_order(items)
  additions.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let mut insertion = items.length() - 1
  for ty in additions.rev() {
    mark_dynamic_encoding_kept(ty)
    items.insert(
      insertion,
      TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])),
    )
    insertion = insertion + 1
  }
  checked_task(task, items, stage)
}

///|
fn kept_type_set(task : @theory.Task) -> Map[@logic.Ty, Unit] {
  let kept : Map[@logic.Ty, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)], .. } {
      kept[ty] = ()
    }
  }
  kept
}

///|
priv struct TwinBridge {
  ty : @logic.Ty
  protect : @logic.LSymbol
  unprotect : @logic.LSymbol
  declarations : Array[@theory.TheoryItem]
}

///|
priv struct TwinBridgeCacheEntry {
  equality : @logic.LSymbol
  bridge : TwinBridge
}

///|
let twin_bridge_cache : Ref[Map[@logic.Ty, Array[TwinBridgeCacheEntry]]] = Ref(
  Map([]),
)

///|
/// `make_twin_bridge` mirrors Why3's type-keyed weak memoization. Bridge
/// declarations therefore remain live with the cached type and are the only
/// declarations whose subsequent guards translation survives across goals.
let twin_bridge_declarations : Ref[Map[@identity.DeclarationId, Unit]] = Ref(
  Map([]),
)

///|
fn twin_origin(
  name : BytesView,
  attributes : ArrayView[Bytes],
) -> @identity.Origin {
  @identity.Origin::generated(@identity.Twin, name, None, attributes)
}

///|
fn twin_parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let declaration = @logic.Decl::parameter(
    context,
    symbol.view().origin,
    symbol,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot declare a twin bridge")
  }
  TheoryDecl(declaration)
}

///|
fn twin_equality(
  equality : @logic.LSymbol,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::elaborated_apply(equality, [left, right], None, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Twin,
        "cannot construct a bridge equality",
      )
  }
}

///|
fn twin_bridge_axiom(
  context : @identity.CompilationContext,
  name : BytesView,
  ty : @logic.Ty,
  protect : @logic.LSymbol,
  unprotect : @logic.LSymbol,
  equality : @logic.LSymbol,
  left_bridge : Bool,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let variable_name = if left_bridge { b"i" } else { b"j" }
  let variable_attributes : Array[Bytes] = if left_bridge {
    []
  } else {
    [b"encoding:unprotected"]
  }
  let variable = @logic.VSymbol::new(
    context,
    variable_name,
    twin_origin(variable_name, variable_attributes),
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create a bridge binder",
      )
  }
  let value = @logic.Term::variable(variable)
  let (first, second) = if left_bridge {
    (protect, unprotect)
  } else {
    (unprotect, protect)
  }
  let inner = @logic.Term::elaborated_apply(first, [value], Some(ty), None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply an inner bridge",
      )
  }
  let outer = @logic.Term::elaborated_apply(second, [inner], Some(ty), None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply an outer bridge",
      )
  }
  let formula = twin_equality(equality, outer, value)
  let trigger = if left_bridge { inner } else { outer }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [[trigger]],
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify a bridge axiom",
      )
  }
  let origin = twin_origin(name, [])
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot declare a bridge axiom",
      )
  }
  TheoryDecl(declaration)
}

///|
fn make_twin_bridge_uncached(
  context : @identity.CompilationContext,
  ty : @logic.Ty,
  equality : @logic.LSymbol,
) -> TwinBridge raise TransformError {
  let stage = @identity.Twin
  let protect_origin = twin_origin(b"t2tb", [b"encoding:unprotected"])
  let unprotect_origin = twin_origin(b"tb2t", [b"encoding:unprotecting"])
  let protect = @logic.LSymbol::new_function(
    context,
    b"t2tb",
    protect_origin,
    [ty],
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create a protecting bridge",
      )
  }
  let unprotect = @logic.LSymbol::new_function(
    context,
    b"tb2t",
    unprotect_origin,
    [ty],
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create an unprotecting bridge",
      )
  }
  {
    ty,
    protect,
    unprotect,
    declarations: [
      twin_parameter_item(context, protect),
      twin_parameter_item(context, unprotect),
      twin_bridge_axiom(
        context, b"BridgeL", ty, protect, unprotect, equality, true,
      ),
      twin_bridge_axiom(
        context, b"BridgeR", ty, protect, unprotect, equality, false,
      ),
    ],
  }
}

///|
fn make_twin_bridge(
  context : @identity.CompilationContext,
  ty : @logic.Ty,
  equality : @logic.LSymbol,
) -> TwinBridge raise TransformError {
  let cache = twin_bridge_cache.val
  match cache.get(ty) {
    Some(entries) =>
      for entry in entries {
        if entry.equality == equality {
          return entry.bridge
        }
      }
    None => ()
  }
  let bridge = make_twin_bridge_uncached(context, ty, equality)
  // Why3's Wty.memoized bridge remains live for as long as the kept type is
  // live. Mark its declarations as persistent so every following
  // declaration-level transform can reproduce the same cross-goal cache.
  let bridge_declarations = twin_bridge_declarations.val
  for item in bridge.declarations {
    if item is TheoryDecl(declaration) {
      declaration_cache_retain(declaration)
      bridge_declarations[declaration.declaration_id()] = ()
    }
  }
  twin_bridge_declarations.val = bridge_declarations
  let entries = match cache.get(ty) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({ equality, bridge })
  cache[ty] = entries
  twin_bridge_cache.val = cache
  bridge
}

///|
fn find_twin_bridge(
  bridges : ArrayView[TwinBridge],
  ty : @logic.Ty,
) -> TwinBridge? {
  for bridge in bridges {
    if bridge.ty == ty {
      return Some(bridge)
    }
  }
  None
}

///|
fn mark_twin_bridge(seen : Array[@logic.Ty], ty : @logic.Ty) -> Unit {
  if !seen.contains(ty) {
    seen.push(ty)
  }
}

///|
fn rebind_term_identifiers(
  term : @logic.Term,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  match term.view() {
    Tvar(variable) =>
      match aliases.get(variable) {
        Some(replacement) =>
          copy_term_decoration(term, @logic.Term::variable(replacement))
        None => term
      }
    Tlet(variable, value, body) => {
      let body_aliases = aliases.copy()
      ignore(body_aliases.remove(variable))
      let replacement = @logic.Term::let_in(
        variable,
        rebind_term_identifiers(value, aliases, stage),
        rebind_term_identifiers(body, body_aliases, stage),
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebind identifiers below a let",
          )
      }
      copy_term_decoration(term, replacement)
    }
    Tcase(scrutinee, branches) => {
      let mapped_branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        let body_aliases = aliases.copy()
        for variable in view.pattern.bound_variables() {
          ignore(body_aliases.remove(variable))
        }
        mapped_branches.push(
          (
            view.pattern,
            rebind_term_identifiers(view.body, body_aliases, stage),
          ),
        )
      }
      let replacement = @logic.Term::case(
        rebind_term_identifiers(scrutinee, aliases, stage),
        mapped_branches,
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebind identifiers below a case",
          )
      }
      copy_term_decoration(term, replacement)
    }
    Teps(variable, body) => {
      let body_aliases = aliases.copy()
      ignore(body_aliases.remove(variable))
      let replacement = @logic.Term::epsilon(
        variable,
        rebind_term_identifiers(body, body_aliases, stage),
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebind identifiers below an epsilon",
          )
      }
      copy_term_decoration(term, replacement)
    }
    Tquant(quantifier, binders, triggers, body) => {
      let body_aliases = aliases.copy()
      for binder in binders {
        ignore(body_aliases.remove(binder))
      }
      let mapped_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              rebind_term_identifiers(trigger, body_aliases, stage)
            }
          ]
        }
      ]
      let replacement = @logic.Term::quantify(
        quantifier,
        binders,
        mapped_triggers,
        rebind_term_identifiers(body, body_aliases, stage),
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebind identifiers below a quantifier",
          )
      }
      copy_term_decoration(term, replacement)
    }
    _ =>
      map_plain(
        term,
        child => rebind_term_identifiers(child, aliases, stage),
        stage,
      )
  }
}

///|
fn twin_clone_binder(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
) -> @logic.VSymbol raise TransformError {
  let view = variable.view()
  let origin = derived_generated_origin(
    @identity.Twin,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  variable.clone_as(context, view.name, origin, view.ty, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Twin,
        "cannot open a twin-transform binder",
      )
  }
}

///|
fn twin_rebuild_pattern(
  pattern : @logic.Pattern,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.Pattern raise TransformError {
  match pattern.view() {
    Pwild(ty) => @logic.Pattern::wild(ty)
    Pvar(variable) =>
      @logic.Pattern::variable(
        match aliases.get(variable) {
          Some(replacement) => replacement
          None => variable
        },
      )
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        symbol,
        [
          for argument in arguments => twin_rebuild_pattern(argument, aliases)
        ],
        ty,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.Twin,
            "cannot rebuild an opened twin pattern",
          )
      }
    Por(left, right, _) =>
      @logic.Pattern::or(
        twin_rebuild_pattern(left, aliases),
        twin_rebuild_pattern(right, aliases),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.Twin,
            "cannot rebuild an opened twin or-pattern",
          )
      }
    Pas(inner, variable, _) =>
      @logic.Pattern::as_pattern(
        twin_rebuild_pattern(inner, aliases),
        match aliases.get(variable) {
          Some(replacement) => replacement
          None => variable
        },
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.Twin,
            "cannot rebuild an opened twin as-pattern",
          )
      }
  }
}

///|
fn twin_rewrite_term(
  context : @identity.CompilationContext,
  term : @logic.Term,
  bridges : ArrayView[TwinBridge],
  seen : Array[@logic.Ty],
) -> @logic.Term raise TransformError {
  let stage = @identity.Twin
  let recurse = fn(child) -> @logic.Term raise TransformError {
    twin_rewrite_term(context, child, bridges, seen)
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let mapped = [ for argument in arguments => recurse(argument) ]
      let view = symbol.view()
      let replacement = if is_builtin_equality(symbol) ||
        view.role is Constructor(_) ||
        view.role is Projection {
        @logic.Term::elaborated_apply(symbol, mapped, term.ty(), None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild an exempt twin application",
            )
        }
      } else {
        if mapped.length() != view.argument_types.length() {
          return fail_transform(
            InvariantFailure,
            stage,
            "twin application arity mismatch",
          )
        }
        let converted : Array[@logic.Term] = []
        for index, argument in mapped {
          guard argument.ty() is Some(actual) else {
            return fail_transform(
              InvariantFailure,
              stage,
              "twin application has a formula argument",
            )
          }
          let formal = view.argument_types[index]
          if actual == formal {
            converted.push(argument)
          } else {
            match find_twin_bridge(bridges, actual) {
              None => converted.push(argument)
              Some(bridge) => {
                mark_twin_bridge(seen, actual)
                match argument.view() {
                  Tapp(inner_symbol, _, inner_arguments) if inner_symbol ==
                    bridge.unprotect &&
                    inner_arguments.length() == 1 =>
                    converted.push(inner_arguments[0])
                  _ => {
                    let protected_argument = @logic.Term::elaborated_apply(
                      bridge.protect,
                      [argument],
                      Some(actual),
                      None,
                    ) catch {
                      _ =>
                        return fail_transform(
                          InvariantFailure,
                          stage,
                          "cannot protect a twin argument",
                        )
                    }
                    converted.push(protected_argument)
                  }
                }
              }
            }
          }
        }
        let application = @logic.Term::elaborated_apply(
          symbol,
          converted,
          term.ty(),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild a twin application",
            )
        }
        match (term.ty(), view.result_type) {
          (Some(actual), Some(formal)) if actual != formal =>
            match find_twin_bridge(bridges, actual) {
              None => application
              Some(bridge) => {
                mark_twin_bridge(seen, actual)
                @logic.Term::elaborated_apply(
                  bridge.unprotect,
                  [application],
                  Some(actual),
                  None,
                ) catch {
                  _ =>
                    return fail_transform(
                      InvariantFailure,
                      stage,
                      "cannot unprotect a twin result",
                    )
                }
              }
            }
          _ => application
        }
      }
      copy_term_decoration(term, replacement)
    }
    Tif(condition, then_branch, else_branch) => {
      // Why3's fallback t_map_unsafe rebuilds Tif through an OCaml function
      // application.  OCaml 4.14 evaluates those arguments right-to-left, and
      // twin bridge discovery observes that order.
      let mapped_else = recurse(else_branch)
      let mapped_then = recurse(then_branch)
      let mapped_condition = recurse(condition)
      let replacement = @logic.Term::if_then_else(
        mapped_condition,
        mapped_then,
        mapped_else,
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebuild a twin conditional",
          )
      }
      copy_term_decoration(term, replacement)
    }
    Tlet(variable, value, body) => {
      // Why3 opens the closure before mapping it. Even when the optimized
      // closer returns the original closure, opening has already emitted the
      // identifier-clone observer event.
      let opened = twin_clone_binder(context, variable)
      let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
      aliases[variable] = opened
      let opened_body = rebind_term_identifiers(body, aliases, @identity.Twin)
      let mapped_value = recurse(value)
      let mapped_body = recurse(opened_body)
      let replacement = if mapped_body == opened_body {
        if mapped_value == value {
          term
        } else {
          @logic.Term::let_in(variable, mapped_value, body, None) catch {
            _ =>
              return fail_transform(
                InvariantFailure,
                stage,
                "cannot rebuild a twin let value",
              )
          }
        }
      } else {
        @logic.Term::let_in(opened, mapped_value, mapped_body, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot close a rewritten twin let",
            )
        }
      }
      copy_term_decoration(term, replacement)
    }
    Tcase(scrutinee, branches) => {
      let mapped_scrutinee = recurse(scrutinee)
      let mapped_branches : Array[(@logic.Pattern, @logic.Term)] = []
      let mut branches_changed = false
      for branch in branches {
        let view = branch.view()
        let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
        let variables = view.pattern.bound_variables().to_owned()
        variables.sort_by((left, right) => {
          guard_compare_semantic_ids(left.semantic_id(), right.semantic_id())
        })
        for variable in variables {
          aliases[variable] = twin_clone_binder(context, variable)
        }
        let opened_pattern = twin_rebuild_pattern(view.pattern, aliases)
        let opened_body = rebind_term_identifiers(
          view.body,
          aliases,
          @identity.Twin,
        )
        let mapped_body = recurse(opened_body)
        if mapped_body == opened_body {
          mapped_branches.push((view.pattern, view.body))
        } else {
          branches_changed = true
          mapped_branches.push((opened_pattern, mapped_body))
        }
      }
      let replacement = if mapped_scrutinee == scrutinee && !branches_changed {
        term
      } else {
        @logic.Term::case(mapped_scrutinee, mapped_branches, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild a twin case",
            )
        }
      }
      copy_term_decoration(term, replacement)
    }
    Teps(variable, body) => {
      let opened = twin_clone_binder(context, variable)
      let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
      aliases[variable] = opened
      let opened_body = rebind_term_identifiers(body, aliases, @identity.Twin)
      let mapped_body = recurse(opened_body)
      let replacement = if mapped_body == opened_body {
        term
      } else {
        @logic.Term::epsilon(opened, mapped_body, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot close a rewritten twin epsilon",
            )
        }
      }
      copy_term_decoration(term, replacement)
    }
    Tquant(quantifier, binders, triggers, body) => {
      let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
      let opened_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let opened = twin_clone_binder(context, binder)
        aliases[binder] = opened
        opened_binders.push(opened)
      }
      let opened_body = rebind_term_identifiers(body, aliases, @identity.Twin)
      let opened_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              rebind_term_identifiers(trigger, aliases, @identity.Twin)
            }
          ]
        }
      ]
      // Why3 evaluates the quantifier body before its parallel trigger-map
      // binding.
      let mapped_body = recurse(opened_body)
      let mapped_triggers : Array[Array[@logic.Term]] = []
      for group in opened_triggers {
        mapped_triggers.push([ for trigger in group => recurse(trigger) ])
      }
      let mut triggers_changed = false
      for index, group in opened_triggers {
        if mapped_triggers[index] != group {
          triggers_changed = true
          break
        }
      }
      let replacement = if mapped_body == opened_body && !triggers_changed {
        term
      } else {
        @logic.Term::quantify(
          quantifier,
          opened_binders,
          mapped_triggers,
          mapped_body,
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild a twin quantifier",
            )
        }
      }
      copy_term_decoration(term, replacement)
    }
    Tbinop(operator, left, right) => {
      // As with Tif, Why3's fallback mapper evaluates constructor arguments
      // right-to-left.
      let mapped_right = recurse(right)
      let mapped_left = recurse(left)
      let replacement = @logic.Term::binary(
        operator,
        mapped_left,
        mapped_right,
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebuild a twin binary term",
          )
      }
      copy_term_decoration(term, replacement)
    }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn twin_rewrite_proposition(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  kind : @logic.PropositionKind,
  proposition : @logic.PrSymbol,
  formula : @logic.Term,
  bridges : ArrayView[TwinBridge],
  seen : Array[@logic.Ty],
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let rewritten = twin_rewrite_term(context, formula, bridges, seen)
  if kind != Pgoal && rewritten.strict_alpha_equivalent(formula) {
    return TheoryDecl(declaration)
  }
  let declaration = @logic.Decl::proposition(
    context,
    declaration.origin(),
    kind,
    proposition,
    rewritten,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild a twin proposition",
      )
  }
  TheoryDecl(declaration)
}

///|
priv struct TwinDeclarationCacheEntry {
  generation : Int64
  persistent : Bool
  kept_types : Array[@logic.Ty]
  output : Array[@theory.TheoryItem]
}

///|
let twin_declaration_cache : Ref[
  Map[@identity.DeclarationId, Array[TwinDeclarationCacheEntry]],
] = Ref(Map([]))

///|
fn twin_transform_declaration_uncached(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  bridges : ArrayView[TwinBridge],
) -> Array[@theory.TheoryItem] raise TransformError {
  let seen : Array[@logic.Ty] = []
  let rewritten = match declaration.view() {
    Dprop(kind, proposition, formula) =>
      twin_rewrite_proposition(
        context, declaration, kind, proposition, formula, bridges, seen,
      )
    Dlogic(_) | Dind(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        @identity.Twin,
        "logic or inductive declaration requires the full twin definition branch",
      )
    Dtype(_) | Ddata(_) | Dparam(_) => TheoryDecl(declaration)
  }
  let output : Array[@theory.TheoryItem] = []
  for ty in seen.rev() {
    guard find_twin_bridge(bridges, ty) is Some(bridge) else {
      return fail_transform(
        InvariantFailure,
        @identity.Twin,
        "missing selected twin bridge",
      )
    }
    for item in bridge.declarations {
      output.push(item)
    }
  }
  output.push(rewritten)
  output
}

///|
fn twin_transform_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  retain_persistent_outputs : Bool,
  bridges : ArrayView[TwinBridge],
) -> Array[@theory.TheoryItem] raise TransformError {
  if declaration.view() is Dprop(Pgoal, _, _) {
    return twin_transform_declaration_uncached(context, declaration, bridges)
  }
  let kept_types = [ for bridge in bridges => bridge.ty ]
  let generation = current_declaration_cache_generation()
  let persistent = retain_persistent_outputs &&
    declaration_cache_is_persistent(declaration)
  let cache = twin_declaration_cache.val
  match cache.get(declaration.declaration_id()) {
    Some(entries) =>
      for entry in entries {
        let live = if entry.persistent {
          persistent
        } else {
          !persistent && entry.generation == generation
        }
        if live && entry.kept_types == kept_types {
          return entry.output
        }
      }
    None => ()
  }
  let output = twin_transform_declaration_uncached(
    context, declaration, bridges,
  )
  if persistent {
    for item in output {
      if item is TheoryDecl(output_declaration) {
        declaration_cache_retain(output_declaration)
      }
    }
  }
  let entries = match cache.get(declaration.declaration_id()) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({ generation, persistent, kept_types, output })
  cache[declaration.declaration_id()] = entries
  twin_declaration_cache.val = cache
  output
}

///|
pub fn encoding_twin(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.Twin
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let kept = kept_type_set(task)
  let mut equality : @logic.LSymbol? = None
  for item in task.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dparam(symbol) &&
      is_builtin_equality(symbol) {
      equality = Some(symbol)
    }
  }
  guard equality is Some(equality) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no equality declaration",
    )
  }
  let kept_types = [ for entry in kept => entry.0 ]
  let (type_symbol_order, _) = discrimination_declaration_order(
    task.view().items,
  )
  kept_types.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let bridges : Array[TwinBridge] = []
  for ty in kept_types {
    bridges.push(make_twin_bridge(context, ty, equality))
  }
  let retain_persistent_outputs = !task_has_dynamic_encoding_kept(task)
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        for
          mapped in twin_transform_declaration(
            context, declaration, retain_persistent_outputs, bridges,
          ) {
          result.push(mapped)
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => result.push(item)
    }
  }
  checked_task(task, result, stage)
}

///|
priv struct GuardSymbolEncoding {
  original : @logic.LSymbol
  encoded : @logic.LSymbol
  add_type_arguments : Bool
}

///|
priv struct GuardSymbolEncodingCacheEntry {
  arguments : Array[@logic.Ty]
  result_type : @logic.Ty?
  encoding : GuardSymbolEncoding
}

///|
let guard_symbol_encoding_cache : Ref[
  Map[@identity.SemanticId, Array[GuardSymbolEncodingCacheEntry]],
] = Ref(Map([]))

///|
priv struct GuardTypeRepresentation {
  type_symbol : @logic.TypeSymbol
  encoded : @logic.LSymbol
}

///|
priv struct GuardTypeRepresentationCacheEntry {
  type_type : @logic.Ty
  representation : GuardTypeRepresentation
}

///|
let guard_type_representation_cache : Ref[
  Map[@identity.SemanticId, Array[GuardTypeRepresentationCacheEntry]],
] = Ref(Map([]))

///|
priv struct GuardBase {
  universal_symbol : @logic.TypeSymbol
  universal_type : @logic.Ty
  type_symbol : @logic.TypeSymbol
  type_type : @logic.Ty
  sort_symbol : @logic.LSymbol
  witness_symbol : @logic.LSymbol
}

///|
priv struct GuardBaseCacheEntry {
  anchor : @identity.SemanticId
  base : GuardBase
}

///|
let guard_base_cache : Ref[Array[GuardBaseCacheEntry]] = Ref([])

///|
fn guard_origin(
  name : BytesView,
  span : @identity.SourceSpan?,
  attributes : ArrayView[Bytes],
) -> @identity.Origin {
  @identity.Origin::generated(@identity.Guards, name, span, attributes)
}

///|
fn guard_abstract_type(
  context : @identity.CompilationContext,
  name : BytesView,
) -> (@logic.TypeSymbol, @logic.Ty) raise TransformError {
  let stage = @identity.Guards
  let origin = guard_origin(name, None, [])
  let symbol = @logic.TypeSymbol::new_abstract(context, name, origin, [], None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot create an encoding sort")
  }
  let ty = @logic.Ty::app(symbol, [], None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot apply an encoding sort")
  }
  (symbol, ty)
}

///|
fn guard_type_item(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let declaration = @logic.Decl::type_declaration(
    context,
    symbol.origin(),
    [symbol],
    None,
  ) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot declare an encoding sort")
  }
  TheoryDecl(declaration)
}

///|
fn guard_parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let declaration = @logic.Decl::parameter(
    context,
    symbol.view().origin,
    symbol,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot declare an encoded symbol",
      )
  }
  TheoryDecl(declaration)
}

///|
fn guard_monomorphic_type(
  ty : @logic.Ty,
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
) -> @logic.Ty {
  if kept.contains(ty) {
    ty
  } else {
    universal_type
  }
}

///|
fn guard_type_contains_symbol(
  ty : @logic.Ty,
  expected : @logic.TypeSymbol,
) -> Bool {
  match ty.view() {
    TyVar(_) => false
    TyApp(symbol, arguments) =>
      symbol == expected ||
      arguments.any(argument => guard_type_contains_symbol(argument, expected))
  }
}

///|
fn guard_keeps_type_declaration(
  symbol : @logic.TypeSymbol,
  kept : Map[@logic.Ty, Unit],
) -> Bool {
  if symbol.view().definition is Alias(_) {
    return false
  }
  for entry in kept {
    if guard_type_contains_symbol(entry.0, symbol) {
      return true
    }
  }
  false
}

///|
fn guard_has_origin_attribute(
  origin : @identity.Origin,
  attribute : BytesView,
) -> Bool {
  origin.attributes().any(value => value[:] == attribute)
}

///|
fn guard_ordered_type_variables(
  variables : ArrayView[@logic.TyVarSymbol],
) -> Array[@logic.TyVarSymbol] {
  let ordered = variables.to_owned()
  ordered.sort_by((left, right) => {
    let left = left.semantic_id().local_id()
    let right = right.semantic_id().local_id()
    if left < right {
      -1
    } else if left > right {
      1
    } else {
      0
    }
  })
  ordered
}

///|
fn guard_encoded_symbol(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
  type_type : @logic.Ty,
  universal_type : @logic.Ty,
  kept : Map[@logic.Ty, Unit],
) -> GuardSymbolEncoding? raise TransformError {
  let stage = @identity.Guards
  let view = symbol.view()
  if !(view.role is Ordinary) {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "constructor survived algebraic elimination",
    )
  }
  if is_builtin_equality(symbol) {
    return None
  }
  let protects_arguments = !guard_has_origin_attribute(
    view.origin,
    b"encoding:unprotecting",
  )
  let protects_result = !guard_has_origin_attribute(
    view.origin,
    b"encoding:unprotected",
  )
  let arguments : Array[@logic.Ty] = []
  for _ in view.type_parameters {
    arguments.push(type_type)
  }
  for ty in view.argument_types {
    arguments.push(
      if protects_arguments {
        guard_monomorphic_type(ty, kept, universal_type)
      } else {
        universal_type
      },
    )
  }
  let result_type = match view.result_type {
    None => None
    Some(ty) =>
      Some(
        if protects_result {
          guard_monomorphic_type(ty, kept, universal_type)
        } else {
          universal_type
        },
      )
  }
  if view.type_parameters.is_empty() &&
    arguments[:] == view.argument_types &&
    result_type == view.result_type {
    return None
  }
  let cache = guard_symbol_encoding_cache.val
  match cache.get(symbol.semantic_id()) {
    Some(entries) =>
      for entry in entries {
        if entry.arguments == arguments && entry.result_type == result_type {
          return Some(entry.encoding)
        }
      }
    None => ()
  }
  let origin = derived_generated_origin(
    @identity.Guards,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  let encoded = match result_type {
    Some(result_type) =>
      @logic.LSymbol::new_function(
        context,
        view.name,
        origin,
        arguments,
        result_type,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create an encoded function",
          )
      }
    None =>
      @logic.LSymbol::new_predicate(context, view.name, origin, arguments, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create an encoded predicate",
          )
      }
  }
  let encoding = {
    original: symbol,
    encoded,
    add_type_arguments: !view.type_parameters.is_empty(),
  }
  let entries = match cache.get(symbol.semantic_id()) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({ arguments, result_type, encoding })
  cache[symbol.semantic_id()] = entries
  guard_symbol_encoding_cache.val = cache
  Some(encoding)
}

///|
fn find_guard_symbol_encoding(
  encodings : ArrayView[GuardSymbolEncoding],
  symbol : @logic.LSymbol,
) -> GuardSymbolEncoding? {
  for encoding in encodings {
    if encoding.original == symbol {
      return Some(encoding)
    }
  }
  None
}

///|
fn guard_type_representation(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
  type_type : @logic.Ty,
) -> GuardTypeRepresentation raise TransformError {
  let stage = @identity.Guards
  let cache = guard_type_representation_cache.val
  match cache.get(symbol.semantic_id()) {
    Some(entries) =>
      for entry in entries {
        if entry.type_type == type_type {
          return entry.representation
        }
      }
    None => ()
  }
  let view = symbol.view()
  let origin = derived_generated_origin(
    @identity.Guards,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  let arguments = [ for _ in view.parameters => type_type ]
  let encoded = @logic.LSymbol::new_function(
    context,
    view.name,
    origin,
    arguments,
    type_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot create a type representation",
      )
  }
  let representation = { type_symbol: symbol, encoded }
  let entries = match cache.get(symbol.semantic_id()) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({ type_type, representation })
  cache[symbol.semantic_id()] = entries
  guard_type_representation_cache.val = cache
  representation
}

///|
fn find_guard_type_representation(
  representations : ArrayView[GuardTypeRepresentation],
  symbol : @logic.TypeSymbol,
) -> @logic.LSymbol? {
  for representation in representations {
    if representation.type_symbol == symbol {
      return Some(representation.encoded)
    }
  }
  None
}

///|
fn guard_type_term(
  ty : @logic.Ty,
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  representations : ArrayView[GuardTypeRepresentation],
  type_type : @logic.Ty,
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  match ty.view() {
    TyVar(variable) =>
      match type_variables.get(variable) {
        Some(term) => term
        None =>
          fail_transform(
            InvariantFailure,
            stage,
            "missing encoded type variable",
          )
      }
    TyApp(symbol, arguments) => {
      guard find_guard_type_representation(representations, symbol)
        is Some(representation) else {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "missing type representation symbol " + symbol.view().name.to_string(),
        )
      }
      let terms = [
        for argument in arguments => {
          guard_type_term(argument, type_variables, representations, type_type)
        }
      ]
      @logic.Term::elaborated_apply(
        representation,
        terms,
        Some(type_type),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot apply a type representation",
          )
      }
    }
  }
}

///|
fn guard_encoded_variable(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  let stage = @identity.Guards
  let view = variable.view()
  let ty = if guard_has_origin_attribute(view.origin, b"encoding:unprotected") {
    universal_type
  } else {
    guard_monomorphic_type(view.ty, kept, universal_type)
  }
  if ty == view.ty {
    return variable
  }
  let origin = derived_generated_origin(
    @identity.Guards,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  variable.clone_as(context, view.name, origin, ty, None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot encode a value variable")
  }
}

///|
fn guard_encoded_binder(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  let encoded = guard_encoded_variable(context, variable, kept, universal_type)
  if encoded == variable {
    let view = variable.view()
    let origin = derived_generated_origin(
      @identity.Guards,
      view.name,
      view.origin,
      derived_generated_attributes(view.origin),
    )
    variable.clone_as(context, view.name, origin, view.ty, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.Guards,
          "cannot clone an encoded binder identifier",
        )
    }
  } else {
    encoded
  }
}

///|
fn guard_instantiated_type(
  instantiation : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
  variable : @logic.TyVarSymbol,
) -> @logic.Ty? {
  for entry in instantiation {
    if entry.0 == variable {
      return Some(entry.1)
    }
  }
  None
}

///|
fn guard_binary_formula(
  operator : @logic.BinaryLogicOp,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::binary(operator, left, right, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar formula",
      )
  }
}

///|
fn guard_not_formula(term : @logic.Term) -> @logic.Term raise TransformError {
  @logic.Term::not(term, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar negation",
      )
  }
}

///|
fn guard_if_formula(
  condition : @logic.Term,
  then_branch : @logic.Term,
  else_branch : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::if_then_else(condition, then_branch, else_branch, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar conditional",
      )
  }
}

///|
fn guard_identifier_alias(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.VSymbol raise TransformError {
  match aliases.get(variable) {
    Some(alias) => alias
    None => {
      let view = variable.view()
      let origin = derived_generated_origin(
        @identity.Guards,
        view.name,
        view.origin,
        derived_generated_attributes(view.origin),
      )
      let alias = variable.clone_as(context, view.name, origin, view.ty, None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            @identity.Guards,
            "cannot clone a case binder identifier",
          )
      }
      aliases[variable] = alias
      alias
    }
  }
}

///|
fn guard_clone_pattern_identifiers(
  context : @identity.CompilationContext,
  pattern : @logic.Pattern,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.Pattern raise TransformError {
  let stage = @identity.Guards
  match pattern.view() {
    Pwild(ty) => @logic.Pattern::wild(ty)
    Pvar(variable) =>
      @logic.Pattern::variable(
        guard_identifier_alias(context, variable, aliases),
      )
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        symbol,
        [
          for argument in arguments => {
            guard_clone_pattern_identifiers(context, argument, aliases)
          }
        ],
        ty,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot clone constructor-pattern identifiers",
          )
      }
    Por(left, right, _) =>
      @logic.Pattern::or(
        guard_clone_pattern_identifiers(context, left, aliases),
        guard_clone_pattern_identifiers(context, right, aliases),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot clone or-pattern identifiers",
          )
      }
    Pas(inner, variable, _) =>
      @logic.Pattern::as_pattern(
        guard_clone_pattern_identifiers(context, inner, aliases),
        guard_identifier_alias(context, variable, aliases),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot clone as-pattern identifiers",
          )
      }
  }
}

///|
fn guard_clone_branch_pattern_identifiers(
  context : @identity.CompilationContext,
  pattern : @logic.Pattern,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.Pattern raise TransformError {
  let variables = pattern.bound_variables().to_owned()
  variables.sort_by((left, right) => {
    guard_compare_semantic_ids(left.semantic_id(), right.semantic_id())
  })
  // Why3 opens a branch by cloning its `Svs` set in identifier order before
  // rebuilding the pattern tree. Allocate all aliases in that order so
  // traversal order cannot perturb the new binder identities.
  for variable in variables {
    ignore(guard_identifier_alias(context, variable, aliases))
  }
  guard_clone_pattern_identifiers(context, pattern, aliases)
}

///|
fn guard_rebind_identifiers(
  term : @logic.Term,
  aliases : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.Term raise TransformError {
  match term.view() {
    Tvar(variable) =>
      match aliases.get(variable) {
        Some(alias) => copy_term_decoration(term, @logic.Term::variable(alias))
        None => term
      }
    _ =>
      map_plain(
        term,
        child => guard_rebind_identifiers(child, aliases),
        @identity.Guards,
      )
  }
}

///|
fn guard_collect_equal_variables(
  term : @logic.Term,
  variables : Map[@logic.VSymbol, Unit],
) -> Unit raise TransformError {
  match term.view() {
    Tvar(variable) => variables[variable] = ()
    Tapp(_, _, _) | Tconst(_) => ()
    Tif(_, then_branch, else_branch) => {
      guard_collect_equal_variables(then_branch, variables)
      guard_collect_equal_variables(else_branch, variables)
    }
    Tlet(variable, value, body) => {
      let from_value : Map[@logic.VSymbol, Unit] = Map([])
      guard_collect_equal_variables(value, from_value)
      guard_collect_equal_variables(body, variables)
      if variables.contains(variable) {
        variables.remove(variable)
        for candidate in from_value.keys() {
          variables[candidate] = ()
        }
      }
    }
    Tcase(_, branches) =>
      for branch in branches {
        guard_collect_equal_variables(branch.view().body, variables)
      }
    Teps(_, _)
    | Tquant(_, _, _, _)
    | Tbinop(_, _, _)
    | Tnot(_)
    | Ttrue
    | Tfalse =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "proposition reached equality variable collection",
      )
  }
}

///|
fn guard_is_infinite_type(
  ty : @logic.Ty,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
) -> Bool {
  match ty.view() {
    TyVar(_) => false
    TyApp(symbol, arguments) => {
      let is_function_type = symbol
        .origin()
        .attributes()
        .any(attribute => attribute == b"why3:builtin:function-type")
      if is_function_type && arguments.length() == 2 {
        guard_is_infinite_type(arguments[1], infinite_types, material_arguments)
      } else if infinite_types.contains(symbol) {
        true
      } else {
        match material_arguments.get(symbol) {
          None => false
          Some(material) => {
            let mut infinite = false
            for index, argument in arguments {
              if index < material.length() &&
                material[index] &&
                guard_is_infinite_type(
                  argument, infinite_types, material_arguments,
                ) {
                infinite = true
                break
              }
            }
            infinite
          }
        }
      }
    }
  }
}

///|
fn guard_sort_formula(
  original_type : @logic.Ty,
  encoded_variable : @logic.VSymbol,
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  representations : ArrayView[GuardTypeRepresentation],
  sort_symbol : @logic.LSymbol,
  type_type : @logic.Ty,
) -> @logic.Term raise TransformError {
  let represented_type = guard_type_term(
    original_type, type_variables, representations, type_type,
  )
  @logic.Term::elaborated_apply(
    sort_symbol,
    [represented_type, @logic.Term::variable(encoded_variable)],
    None,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot construct a variable guard",
      )
  }
}

///|
fn guard_encode_term_with_change(
  context : @identity.CompilationContext,
  term : @logic.Term,
  values : Map[@logic.VSymbol, @logic.Term],
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
  polar : Bool,
  sign : Bool,
  equal_variables : Map[@logic.VSymbol, Unit],
  changed : Ref[Bool],
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  let recurse = fn(child) -> @logic.Term raise TransformError {
    guard_encode_term_with_change(
      context, child, values, type_variables, symbol_encodings, representations,
      kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
      polar, sign, equal_variables, changed,
    )
  }
  let replacement = match term.view() {
    Tvar(variable) =>
      match values.get(variable) {
        Some(value) => value
        None => {
          let encoded = guard_encoded_variable(
            context, variable, kept, universal_type,
          )
          if encoded != variable {
            changed.val = true
          }
          @logic.Term::variable(encoded)
        }
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) && kept.contains(ty) else {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "unprotected literal requires the constant-symbol encoding",
        )
      }
      @logic.Term::constant(constant, ty, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot retain a protected literal",
          )
      }
    }
    Tapp(symbol, instantiation, arguments) => {
      if is_builtin_equality(symbol) &&
        arguments.length() == 2 &&
        (!polar || sign) {
        guard_collect_equal_variables(arguments[0], equal_variables)
        guard_collect_equal_variables(arguments[1], equal_variables)
      }
      let mapped_arguments = [ for argument in arguments => recurse(argument) ]
      let (encoded_symbol, type_arguments) = match
        find_guard_symbol_encoding(symbol_encodings, symbol) {
        Some(encoding) => {
          let type_arguments : Array[@logic.Term] = []
          if encoding.add_type_arguments {
            let parameters = guard_ordered_type_variables(
              symbol.view().type_parameters,
            )
            for parameter in parameters.rev() {
              guard guard_instantiated_type(instantiation, parameter)
                is Some(actual) else {
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "missing logic type instantiation",
                )
              }
              type_arguments.push(
                guard_type_term(
                  actual, type_variables, representations, type_type,
                ),
              )
            }
          }
          (encoding.encoded, type_arguments)
        }
        None => (symbol, [])
      }
      if encoded_symbol != symbol || !type_arguments.is_empty() {
        changed.val = true
      }
      let encoded_arguments = type_arguments
      for argument in mapped_arguments {
        encoded_arguments.push(argument)
      }
      let result_type = if encoded_symbol == symbol {
        term.ty()
      } else {
        encoded_symbol.view().result_type
      }
      @logic.Term::elaborated_apply(
        encoded_symbol,
        encoded_arguments,
        result_type,
        None,
      ) catch {
        @logic.TypeError(diagnostic) =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot apply encoded logic symbol " +
            symbol.view().name.to_string() +
            ": " +
            diagnostic.message,
          )
      }
    }
    Tif(condition, then_branch, else_branch) =>
      if term.ty() is Some(_) {
        let encoded_condition = guard_encode_term_with_change(
          context, condition, values, type_variables, symbol_encodings, representations,
          kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
          false, sign, equal_variables, changed,
        )
        guard_if_formula(
          encoded_condition,
          recurse(then_branch),
          recurse(else_branch),
        )
      } else {
        let condition_at_sign = recurse(condition)
        let condition_at_opposite = guard_encode_term_with_change(
          context,
          condition,
          values,
          type_variables,
          symbol_encodings,
          representations,
          kept,
          universal_type,
          type_type,
          sort_symbol,
          infinite_types,
          material_arguments,
          polar,
          !sign,
          equal_variables,
          changed,
        )
        let encoded_then = recurse(then_branch)
        let encoded_else = recurse(else_branch)
        if condition_at_sign == condition_at_opposite {
          guard_if_formula(condition_at_sign, encoded_then, encoded_else)
        } else if sign {
          changed.val = true
          guard_binary_formula(
            And,
            guard_binary_formula(Implies, condition_at_opposite, encoded_then),
            guard_binary_formula(
              Implies,
              guard_not_formula(condition_at_sign),
              encoded_else,
            ),
          )
        } else {
          changed.val = true
          guard_binary_formula(
            Or,
            guard_binary_formula(And, condition_at_sign, encoded_then),
            guard_binary_formula(
              And,
              guard_not_formula(condition_at_opposite),
              encoded_else,
            ),
          )
        }
      }
    Tlet(variable, value, body) => {
      let from_value : Map[@logic.VSymbol, Unit] = Map([])
      guard_collect_equal_variables(value, from_value)
      let encoded_variable = guard_encoded_binder(
        context, variable, kept, universal_type,
      )
      let body_changed = Ref(encoded_variable.view().ty != variable.view().ty)
      let nested = values.copy()
      nested[variable] = @logic.Term::variable(
        if body_changed.val {
          encoded_variable
        } else {
          variable
        },
      )
      let encoded_body = guard_encode_term_with_change(
        context, body, nested, type_variables, symbol_encodings, representations,
        kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
        polar, sign, equal_variables, body_changed,
      )
      if equal_variables.contains(variable) {
        equal_variables.remove(variable)
        for candidate in from_value.keys() {
          equal_variables[candidate] = ()
        }
      }
      let encoded_value = recurse(value)
      let (closed_variable, closed_body) = if body_changed.val {
        let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
        if encoded_variable.view().ty == variable.view().ty {
          aliases[variable] = encoded_variable
        }
        changed.val = true
        (encoded_variable, guard_rebind_identifiers(encoded_body, aliases))
      } else {
        // An unchanged open body closes back to the original binder in Why3.
        // Outer substitutions remain materialized in our eager term.
        (variable, encoded_body)
      }
      @logic.Term::let_in(closed_variable, encoded_value, closed_body, None) catch {
        _ => fail_transform(InvariantFailure, stage, "cannot encode a let term")
      }
    }
    Tcase(scrutinee, branches) => {
      guard scrutinee.ty() is Some(scrutinee_type) &&
        kept.contains(scrutinee_type) else {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "case over an unprotected type survived algebraic elimination",
        )
      }
      let encoded_branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        for variable in view.pattern.bound_variables() {
          guard kept.contains(variable.view().ty) &&
            !guard_has_origin_attribute(
              variable.view().origin,
              b"encoding:unprotected",
            ) else {
            return fail_transform(
              UnsupportedStructure,
              stage,
              "case pattern binds an unprotected value",
            )
          }
        }
        let branch_changed = Ref(false)
        let body = guard_encode_term_with_change(
          context,
          view.body,
          values,
          type_variables,
          symbol_encodings,
          representations,
          kept,
          universal_type,
          type_type,
          sort_symbol,
          infinite_types,
          material_arguments,
          polar,
          sign,
          equal_variables,
          branch_changed,
        )
        if !branch_changed.val {
          // Why3 keeps outer substitutions in the branch closure.  Our eager
          // representation must retain the substituted body while preserving
          // the unmodified pattern identifiers.
          encoded_branches.push((view.pattern, body))
        } else {
          changed.val = true
          let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
          let pattern = guard_clone_branch_pattern_identifiers(
            context,
            view.pattern,
            aliases,
          )
          encoded_branches.push(
            (pattern, guard_rebind_identifiers(body, aliases)),
          )
        }
      }
      @logic.Term::case(recurse(scrutinee), encoded_branches, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot rebuild a protected case",
          )
      }
    }
    Teps(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        stage,
        "epsilon survived elimination",
      )
    Tquant(quantifier, binders, triggers, body) => {
      let nested = values.copy()
      let encoded_binders : Array[@logic.VSymbol] = []
      let closure_changed = Ref(false)
      for binder in binders {
        let encoded = guard_encoded_binder(
          context, binder, kept, universal_type,
        )
        encoded_binders.push(encoded)
        if encoded.view().ty == binder.view().ty {
          nested[binder] = @logic.Term::variable(binder)
        } else {
          closure_changed.val = true
          nested[binder] = @logic.Term::variable(encoded)
        }
      }
      let encoded_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              guard_encode_term_with_change(
                context, trigger, nested, type_variables, symbol_encodings, representations,
                kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
                polar, sign, equal_variables, closure_changed,
              )
            }
          ]
        }
      ]
      let encoded_body = guard_encode_term_with_change(
        context, body, nested, type_variables, symbol_encodings, representations,
        kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
        polar, sign, equal_variables, closure_changed,
      )
      let mut guarded_body = encoded_body
      for index = binders.length() - 1; index >= 0; index = index - 1 {
        let original = binders[index]
        let encoded = encoded_binders[index]
        let view = original.view()
        let is_protected = kept.contains(view.ty) &&
          !guard_has_origin_attribute(view.origin, b"encoding:unprotected")
        let skip = is_protected ||
          (
            polar &&
            sign == (quantifier is ForallQuantifier) &&
            (
              !equal_variables.contains(original) ||
              guard_is_infinite_type(
                view.ty,
                infinite_types,
                material_arguments,
              )
            )
          )
        equal_variables.remove(original)
        if !skip {
          closure_changed.val = true
          let guard_formula = guard_sort_formula(
            view.ty,
            encoded,
            type_variables,
            representations,
            sort_symbol,
            type_type,
          )
          guarded_body = guard_binary_formula(
            if quantifier is ForallQuantifier {
              Implies
            } else {
              And
            },
            guard_formula,
            guarded_body,
          )
        }
      }
      let (closed_binders, closed_triggers, closed_body) = if closure_changed.val {
        let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
        for index, encoded in encoded_binders {
          if encoded.view().ty == binders[index].view().ty {
            aliases[binders[index]] = encoded
          }
        }
        changed.val = true
        (
          encoded_binders,
          [
            for group in encoded_triggers => {
              [
                for trigger in group => {
                  guard_rebind_identifiers(trigger, aliases)
                }
              ]
            }
          ],
          guard_rebind_identifiers(guarded_body, aliases),
        )
      } else {
        // The optimized Why3 closer returns the original quantifier closure
        // when its opened body and triggers were not rewritten.
        (binders.to_owned(), encoded_triggers, guarded_body)
      }
      @logic.Term::quantify(
        quantifier,
        closed_binders,
        closed_triggers,
        closed_body,
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot encode a quantifier")
      }
    }
    Tbinop(Implies, left, right) => {
      let encoded_left = guard_encode_term_with_change(
        context,
        left,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        material_arguments,
        polar,
        !sign,
        equal_variables,
        changed,
      )
      guard_binary_formula(Implies, encoded_left, recurse(right))
    }
    Tbinop(Iff, left, right) => {
      let left_at_sign = recurse(left)
      let left_at_opposite = guard_encode_term_with_change(
        context,
        left,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        material_arguments,
        polar,
        !sign,
        equal_variables,
        changed,
      )
      let right_at_sign = recurse(right)
      let right_at_opposite = guard_encode_term_with_change(
        context,
        right,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        material_arguments,
        polar,
        !sign,
        equal_variables,
        changed,
      )
      if left_at_sign == left_at_opposite && right_at_sign == right_at_opposite {
        guard_binary_formula(Iff, left_at_sign, right_at_sign)
      } else if sign {
        changed.val = true
        guard_binary_formula(
          And,
          guard_binary_formula(Implies, left_at_opposite, right_at_sign),
          guard_binary_formula(Implies, right_at_opposite, left_at_sign),
        )
      } else {
        changed.val = true
        guard_binary_formula(
          Implies,
          guard_binary_formula(Or, left_at_opposite, right_at_opposite),
          guard_binary_formula(And, left_at_sign, right_at_sign),
        )
      }
    }
    Tbinop(operator, left, right) =>
      guard_binary_formula(operator, recurse(left), recurse(right))
    Tnot(inner) => {
      let encoded = guard_encode_term_with_change(
        context,
        inner,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        material_arguments,
        polar,
        !sign,
        equal_variables,
        changed,
      )
      guard_not_formula(encoded)
    }
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_term_decoration(term, replacement)
}

///|
fn guard_type_variable(
  context : @identity.CompilationContext,
  variable : @logic.TyVarSymbol,
  type_type : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  let stage = @identity.Guards
  let name = variable.name()
  let origin = guard_origin(name, None, variable.origin().attributes())
  @logic.VSymbol::new(context, name, origin, type_type, None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot quantify an encoded type")
  }
}

///|
fn guard_encode_formula(
  context : @identity.CompilationContext,
  formula : @logic.Term,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
  sign : Bool,
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  let type_variables : Map[@logic.TyVarSymbol, @logic.Term] = Map([])
  let binders : Array[@logic.VSymbol] = []
  let free_type_variables = formula.free_type_variables()
  let free_type_variables = guard_ordered_type_variables(free_type_variables[:])
  for variable in free_type_variables {
    let binder = guard_type_variable(context, variable, type_type)
    binders.push(binder)
    type_variables[variable] = @logic.Term::variable(binder)
  }
  let encoded = guard_encode_term_with_change(
    context,
    formula,
    Map([]),
    type_variables,
    symbol_encodings,
    representations,
    kept,
    universal_type,
    type_type,
    sort_symbol,
    infinite_types,
    material_arguments,
    true,
    sign,
    Map([]),
    Ref(false),
  )
  if binders.is_empty() {
    return encoded
  }
  @logic.Term::quantify(ForallQuantifier, binders, [], encoded, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot close encoded type variables",
      )
  }
}

///|
fn guard_generated_proposition(
  context : @identity.CompilationContext,
  name : BytesView,
  formula : @logic.Term,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let origin = guard_origin(name, None, [])
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot declare an encoding axiom",
      )
  }
  TheoryDecl(declaration)
}

///|
fn guard_witness_axiom(
  context : @identity.CompilationContext,
  sort_symbol : @logic.LSymbol,
  witness_symbol : @logic.LSymbol,
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let variable = @logic.VSymbol::new(
    context,
    b"a",
    guard_origin(b"a", None, []),
    type_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot create witness type binder",
      )
  }
  let type_term = @logic.Term::variable(variable)
  let witness = @logic.Term::elaborated_apply(
    witness_symbol,
    [type_term],
    Some(universal_type),
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot apply witness")
  }
  let formula = @logic.Term::elaborated_apply(
    sort_symbol,
    [type_term, witness],
    None,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot type witness")
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [],
    formula,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot quantify witness type")
  }
  guard_generated_proposition(context, b"witness_sort", formula)
}

///|
fn guard_base(
  context : @identity.CompilationContext,
  anchor : @identity.SemanticId,
) -> GuardBase raise TransformError {
  for entry in guard_base_cache.val {
    if entry.anchor.same_context(anchor) {
      return entry.base
    }
  }
  let (universal_symbol, universal_type) = guard_abstract_type(context, b"uni")
  let (type_symbol, type_type) = guard_abstract_type(context, b"ty")
  let sort_origin = guard_origin(b"sort", None, [])
  let sort_symbol = @logic.LSymbol::new_predicate(
    context,
    b"sort",
    sort_origin,
    [type_type, universal_type],
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot create sort predicate",
      )
  }
  let witness_origin = guard_origin(b"witness", None, [])
  let witness_symbol = @logic.LSymbol::new_function(
    context,
    b"witness",
    witness_origin,
    [type_type],
    universal_type,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot create witness function",
      )
  }
  let base = {
    universal_symbol,
    universal_type,
    type_symbol,
    type_type,
    sort_symbol,
    witness_symbol,
  }
  let cache = guard_base_cache.val
  cache.push({ anchor, base })
  guard_base_cache.val = cache
  base
}

///|
fn guard_symbol_sort_axiom(
  context : @identity.CompilationContext,
  original : @logic.LSymbol,
  encoded : @logic.LSymbol,
  sort_symbol : @logic.LSymbol,
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
) -> @theory.TheoryItem? raise TransformError {
  let stage = @identity.Guards
  let view = original.view()
  guard view.result_type is Some(result_type) &&
    (
      !kept.contains(result_type) ||
      guard_has_origin_attribute(view.origin, b"encoding:unprotected")
    ) else {
    return None
  }
  let type_variables : Map[@logic.TyVarSymbol, @logic.Term] = Map([])
  let type_binders : Array[@logic.VSymbol] = []
  let ordered_type_variables = guard_ordered_type_variables(
    view.type_parameters,
  )
  for variable in ordered_type_variables {
    let binder = guard_type_variable(context, variable, type_type)
    type_binders.push(binder)
    type_variables[variable] = @logic.Term::variable(binder)
  }
  let value_binders : Array[@logic.VSymbol] = []
  for formal in view.argument_types {
    let ty = guard_monomorphic_type(formal, kept, universal_type)
    let binder = @logic.VSymbol::new(
      context,
      b"x",
      guard_origin(b"x", None, []),
      ty,
      None,
    ) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          stage,
          "cannot create sort-axiom binder",
        )
    }
    value_binders.push(binder)
  }
  let application_arguments : Array[@logic.Term] = []
  for binder in type_binders.rev() {
    application_arguments.push(@logic.Term::variable(binder))
  }
  for binder in value_binders {
    application_arguments.push(@logic.Term::variable(binder))
  }
  let application = @logic.Term::elaborated_apply(
    encoded,
    application_arguments,
    encoded.view().result_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot apply symbol in sort axiom",
      )
  }
  let result_sort = guard_type_term(
    result_type, type_variables, representations, type_type,
  )
  let formula = @logic.Term::elaborated_apply(
    sort_symbol,
    [result_sort, application],
    None,
    None,
  ) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot construct a sort axiom")
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    value_binders,
    [],
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify sort-axiom values",
      )
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    type_binders,
    [],
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify sort-axiom types",
      )
  }
  let name = view.name + b"_sort"
  Some(guard_generated_proposition(context, name, formula))
}

///|
fn guard_rebuild_proposition(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  kind : @logic.PropositionKind,
  proposition : @logic.PrSymbol,
  formula : @logic.Term,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let formula = guard_encode_formula(
    context,
    formula,
    symbol_encodings,
    representations,
    kept,
    universal_type,
    type_type,
    sort_symbol,
    infinite_types,
    material_arguments,
    !(kind is Pgoal),
  )
  let declaration = @logic.Decl::proposition(
    context,
    declaration.origin(),
    kind,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild an encoded proposition",
      )
  }
  TheoryDecl(declaration)
}

///|
priv struct GuardDeclarationSignature {
  universal_type : @logic.Ty
  type_type : @logic.Ty
  sort_symbol : @logic.LSymbol
  kept_types : Array[@logic.Ty]
  infinite_types : Array[@logic.TypeSymbol]
  material_arguments : Array[(@logic.TypeSymbol, Array[Bool])]
}

///|
priv struct GuardDeclarationCacheEntry {
  generation : Int64
  signature : GuardDeclarationSignature
  output : Array[@theory.TheoryItem]
}

///|
let guard_declaration_cache : Ref[
  Map[@identity.DeclarationId, Array[GuardDeclarationCacheEntry]],
] = Ref(Map([]))

///|
fn guard_compare_semantic_ids(
  left : @identity.SemanticId,
  right : @identity.SemanticId,
) -> Int {
  let left = left.local_id()
  let right = right.local_id()
  if left < right {
    -1
  } else if left > right {
    1
  } else {
    0
  }
}

///|
fn guard_declaration_signature(
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
) -> GuardDeclarationSignature {
  let kept_types = [ for entry in kept => entry.0 ]
  kept_types.sort_by((left, right) => {
    let left = left.allocation_order()
    let right = right.allocation_order()
    if left < right {
      -1
    } else if left > right {
      1
    } else {
      0
    }
  })
  let infinite_types = [ for entry in infinite_types => entry.0 ]
  infinite_types.sort_by((left, right) => {
    guard_compare_semantic_ids(left.semantic_id(), right.semantic_id())
  })
  let material_arguments = [
    for entry in material_arguments => (entry.0, entry.1.copy())
  ]
  material_arguments.sort_by((left, right) => {
    guard_compare_semantic_ids(left.0.semantic_id(), right.0.semantic_id())
  })
  {
    universal_type,
    type_type,
    sort_symbol,
    kept_types,
    infinite_types,
    material_arguments,
  }
}

///|
fn guard_declaration_signatures_equal(
  left : GuardDeclarationSignature,
  right : GuardDeclarationSignature,
) -> Bool {
  left.universal_type == right.universal_type &&
  left.type_type == right.type_type &&
  left.sort_symbol == right.sort_symbol &&
  left.kept_types == right.kept_types &&
  left.infinite_types == right.infinite_types &&
  left.material_arguments == right.material_arguments
}

///|
fn guard_proposition_outputs_equal(
  left : ArrayView[@theory.TheoryItem],
  right : ArrayView[@theory.TheoryItem],
) -> Bool {
  guard left is [TheoryDecl(left)] &&
    right is [TheoryDecl(right)] &&
    left.view() is Dprop(left_kind, left_proposition, left_formula) &&
    right.view() is Dprop(right_kind, right_proposition, right_formula) else {
    return false
  }
  left_kind == right_kind &&
  left_proposition == right_proposition &&
  left_formula.strict_alpha_equivalent(right_formula)
}

///|
fn guard_transform_declaration_uncached(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
) -> Array[@theory.TheoryItem] raise TransformError {
  let output : Array[@theory.TheoryItem] = []
  match declaration.view() {
    Dtype(symbols) => {
      if symbols.any(symbol => guard_keeps_type_declaration(symbol, kept)) {
        output.push(TheoryDecl(declaration))
      }
      for symbol in symbols {
        if symbol.view().definition is Alias(_) {
          continue
        }
        guard find_guard_type_representation(representations, symbol)
          is Some(representation) else {
          return fail_transform(
            InvariantFailure,
            @identity.Guards,
            "missing declared type representation",
          )
        }
        output.push(guard_parameter_item(context, representation))
      }
    }
    Ddata(declarations) => {
      output.push(TheoryDecl(declaration))
      for data in declarations {
        let symbol = data.view().type_symbol
        guard find_guard_type_representation(representations, symbol)
          is Some(representation) else {
          return fail_transform(
            InvariantFailure,
            @identity.Guards,
            "missing data type representation",
          )
        }
        output.push(guard_parameter_item(context, representation))
      }
    }
    Dparam(symbol) =>
      if !is_builtin_equality(symbol) {
        match find_guard_symbol_encoding(symbol_encodings, symbol) {
          None => output.push(TheoryDecl(declaration))
          Some(encoding) => {
            output.push(guard_parameter_item(context, encoding.encoded))
            if guard_symbol_sort_axiom(
                context,
                symbol,
                encoding.encoded,
                sort_symbol,
                representations,
                kept,
                universal_type,
                type_type,
              )
              is Some(axiom) {
              output.push(axiom)
            }
          }
        }
      }
    Dprop(kind, proposition, formula) =>
      output.push(
        guard_rebuild_proposition(
          context, declaration, kind, proposition, formula, symbol_encodings, representations,
          kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
        ),
      )
    Dlogic(_) | Dind(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        @identity.Guards,
        "complex declaration survived the frozen guards prefix",
      )
  }
  output
}

///|
fn guard_transform_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  retain_bridge_outputs : Bool,
  signature : GuardDeclarationSignature,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  material_arguments : Map[@logic.TypeSymbol, Array[Bool]],
) -> Array[@theory.TheoryItem] raise TransformError {
  if declaration.view() is Dprop(Pgoal, _, _) {
    return guard_transform_declaration_uncached(
      context, declaration, symbol_encodings, representations, kept, universal_type,
      type_type, sort_symbol, infinite_types, material_arguments,
    )
  }
  let generation = current_declaration_cache_generation()
  let persistent = retain_bridge_outputs &&
    twin_bridge_declarations.val.contains(declaration.declaration_id())
  let cache = guard_declaration_cache.val
  match cache.get(declaration.declaration_id()) {
    Some(entries) =>
      for entry in entries {
        if (persistent || entry.generation == generation) &&
          guard_declaration_signatures_equal(entry.signature, signature) {
          return entry.output
        }
      }
    None => ()
  }
  let output = guard_transform_declaration_uncached(
    context, declaration, symbol_encodings, representations, kept, universal_type,
    type_type, sort_symbol, infinite_types, material_arguments,
  )
  let entries = match cache.get(declaration.declaration_id()) {
    Some(entries) => entries.copy()
    None => []
  }
  let output = if persistent {
    let mut retained : Array[@theory.TheoryItem]? = None
    for entry in entries {
      if guard_proposition_outputs_equal(entry.output, output) {
        retained = Some(entry.output)
        break
      }
    }
    retained.unwrap_or(output)
  } else {
    output
  }
  entries.push({ generation, signature, output })
  cache[declaration.declaration_id()] = entries
  guard_declaration_cache.val = cache
  output
}

///|
pub fn encoding_guards(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.Guards
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  if task_has_meta(task, b"encoding:base") {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "custom encoding base is outside the frozen profile",
    )
  }
  let base = guard_base(context, task.context_anchor())
  let universal_symbol = base.universal_symbol
  let universal_type = base.universal_type
  let type_symbol = base.type_symbol
  let type_type = base.type_type
  let sort_symbol = base.sort_symbol
  let witness_symbol = base.witness_symbol
  let kept = kept_type_set(task)
  kept[type_type] = ()
  let infinite_types : Map[@logic.TypeSymbol, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"infinite_type", arguments: [MetaTypeSymbol(symbol)], .. } {
      infinite_types[symbol] = ()
    }
  }
  let material_arguments = algebraic_material_arguments(task)
  let mut equality_item : @theory.TheoryItem? = None
  let mut equality_symbol : @logic.LSymbol? = None
  for item in task.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dparam(symbol) &&
      is_builtin_equality(symbol) {
      equality_item = Some(item)
      equality_symbol = Some(symbol)
    }
  }
  guard equality_item is Some(equality_item) && equality_symbol is Some(_) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no equality declaration",
    )
  }
  let representations : Array[GuardTypeRepresentation] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      match declaration.view() {
        Dtype(symbols) =>
          for symbol in symbols {
            if !(symbol.view().definition is Alias(_)) {
              representations.push(
                guard_type_representation(context, symbol, type_type),
              )
            }
          }
        Ddata(declarations) =>
          for data in declarations {
            representations.push(
              guard_type_representation(
                context,
                data.view().type_symbol,
                type_type,
              ),
            )
          }
        Dparam(_) | Dlogic(_) | Dind(_, _) | Dprop(_, _, _) => ()
      }
    }
  }
  let symbol_encodings : Array[GuardSymbolEncoding] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) && declaration.view() is Dparam(symbol) {
      if guard_encoded_symbol(context, symbol, type_type, universal_type, kept)
        is Some(encoding) {
        symbol_encodings.push(encoding)
      }
    }
  }
  let declaration_signature = guard_declaration_signature(
    kept, universal_type, type_type, sort_symbol, infinite_types, material_arguments,
  )
  let retain_bridge_outputs = !task_has_dynamic_encoding_kept(task)
  let result : Array[@theory.TheoryItem] = [
    guard_type_item(context, universal_symbol),
    guard_type_item(context, type_symbol),
    equality_item,
    guard_parameter_item(context, sort_symbol),
    guard_parameter_item(context, witness_symbol),
    guard_witness_axiom(
      context, sort_symbol, witness_symbol, universal_type, type_type,
    ),
  ]
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        for
          mapped in guard_transform_declaration(
            context, declaration, retain_bridge_outputs, declaration_signature, symbol_encodings,
            representations, kept, universal_type, type_type, sort_symbol, infinite_types,
            material_arguments,
          ) {
          result.push(mapped)
        }
      TheoryUse(_) | TheoryMeta(_) => result.push(item)
      TheoryClone(_) => result.push(item)
    }
  }
  checked_task(task, result, stage)
}

///|
pub fn encoding_smt_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EncodingSmtIfPoly
  require_task_context(context, task, stage)
  task
}
