# WhyML 到 Z3 的完整最小功能实现计划

> 计划版本：2（MVP 决策冻结版）
>
> 制定日期：2026-07-20
>
> 参考实现：Why3 1.7.2
>
> Why3 1.7.2 源码：`../why3`，固定 commit `1343338d3bb1941c0d4f134283bb0790816113c4`
>
> 首个且唯一的 MVP prover profile：`z3_487.drv`，固定 Z3 4.8.12

本计划描述从现有 WhyML Parser 开始，直到能够对一个严格限定但实用的 WhyML 子集生成 VC、打印 SMT-LIB 2.6、调用 Z3 并返回兼容 Why3 1.7.2 的结果。MVP 产品面固定为 **CLI-only**：根 library package 始终为空，不承诺 MoonBit library API 兼容性；计划不实现 Why3 的其他前端、插件机制或通用 `.drv` 解释器。

本文中的 typed semantic、raw Task、每个 transform checkpoint 和 prepared Task 都以完整 canonical structure 做 exact gate。SMT 主 gate 保留用户与 snapshot 名称以及所有语义顺序，只对明确标记为 `OriginKind.Generated(stage)` 的标识符做首次出现顺序的 alpha normalization。

---

## 1. 最终结论与完成定义

首先实现带唯一符号身份和类型不变量的语义内核。完整依赖顺序为：

```text
WhyML bytes
  -> parser.Ptree
  -> 名字解析与延迟类型推导
  -> Typed Core Logic
  -> Theory / Task
  -> 纯逻辑 Z3 闭环（中间里程碑）
  -> Typed Program IR
  -> Kode / classical WP / VC
  -> 固定 Z3 driver pipeline
  -> SMT-LIB 2.6
  -> native Z3 runner
  -> ProverResult
```

本计划包含两个连续的可运行闭环：

1. **闭环 A：纯逻辑到 Z3。** 用于尽早验证类型内核、Theory、Task、transform、printer 和 runner。
2. **闭环 B：最小 WhyML 程序验证到 Z3。** 支持无副作用的非递归函数、`requires`、`ensures`、调用、`let`、`if`、`assert`、`assume`。闭环 B 完成才表示本计划完成。

MVP 的类型边界同时冻结为：

- 用户纯逻辑支持参数化 abstract/alias type，以及非递归 polymorphic constant/function/predicate 和 polymorphic axiom/lemma/goal；
- 用户 program routine 必须单态，参数、结果和表达式支持 `Bool/Int/Real/Unit`；
- trusted stdlib 中的 polymorphic routine 可以在用户 program 中实例化，但不会放宽用户 routine 的单态限制；
- user datatype、高阶应用、lambda、epsilon 和递归在本计划中仍 fail closed。

完成定义不是“Z3 对样例给出相同答案”，而是同一 fixture 在固定 oracle profile 下依次通过 typed unit、raw goal Task、每个 transform checkpoint、prepared goal Task 和 SMT token stream 的分层兼容 gate，最后才比较 prover outcome。

最终验收示例至少包括：

```whyml
module Abs
  use int.Int

  let abs (x : int) : int
    ensures { result >= 0 }
  = if x >= 0 then x else -x
end
```

预期行为：生成一个 `abs'vc`，打印为 SMT-LIB，Z3 返回 `unsat`，MoonBit 端报告 `Valid`。

---

## 2. 固定范围

### 2.1 必须支持

| 层 | 最小功能 |
|---|---|
| 输入 | 单个 `.mlw` 文件；同文件内的 `theory` 和 `module`；只能引用同文件 unit 与内置 snapshot |
| 用户可见基础环境 | 仅 `BuiltIn`、`Bool`、`Unit`、`int.Int`、`real.Real`；driver-only theory 不进入用户 resolver |
| 名字空间 | 当前文件内的 theory/module；`use`、`use import`；精确解析上述用户可见标准库 |
| 纯逻辑类型 | `bool`、`int`、`real`、`unit`、参数化 abstract/alias type、显式或推导的类型变量 |
| program 类型 | 单态 `Bool/Int/Real/Unit`；trusted stdlib polymorphic routine 可按调用点实例化 |
| 纯逻辑声明 | 参数化 abstract/alias `type`；非递归 polymorphic `constant/function/predicate`；polymorphic `axiom/lemma/goal` |
| 纯逻辑 term | 变量、精确数值、应用、等号、布尔联结、`let`、`if`、`forall`、`exists`、trigger、属性和显式 cast 的语义处理 |
| 程序声明 | 非递归、无副作用的顶层 `let` 函数；抽象 `val` 可作为被调用 routine |
| 程序表达式 | Bool/Int/Real/Unit 变量与常量、Int/Real 算术和比较、纯逻辑应用、routine 调用、`let`、`if`、`assert`、`assume` |
| 合约 | `requires`、普通 `ensures`、简单 result pattern；调用者使用被调用者 pre/post |
| VC | classical WP；函数前置/后置条件；分支、绑定、调用、assert/assume |
| transform | Why3 1.7.2 `z3_487` 所需的窄多态路径，printer 前消除全部类型变量 |
| SMT | SMT-LIB 2.6；Bool/Int/Real、无解释 sort/function/predicate、量词和 trigger；仅 generated identifier 做 alpha normalization |
| Prover | 静态 Z3 profile；超时；有界 stdout/stderr；稳定结果分类 |
| CLI | `check`、`task`、`emit-smt`、`prove`；稳定人类摘要、versioned NDJSON 和 canonical debug 输出 |
| 验证 | typed/raw/逐 transform/prepared canonical exact，SMT 受限 alpha exact，最后比较 solver outcome |

### 2.2 必须显式拒绝

以下语法可以继续被 Parser 接受，但语义层必须返回带源码位置的 `UnsupportedFeature`，不能静默近似：

- 用户 `clone`、用户 `Dmeta` 和 module interface 的完整语义；
- 用户 algebraic datatype、record、constructor、pattern matching；
- inductive/coinductive；
- lambda、epsilon 和高阶应用；
- printer 前仍残留类型变量或未经过冻结窄路径处理的多态结构；
- 递归函数和 `variant`；
- `while`、`for`、循环不变式；
- reference、mutable field、assignment、region、reads/writes、havoc；
- exception、raise、`xpost`；
- `old`、`at`、type invariant、witness；
- `let function`、`val function` 及其 pure `Dlogic/Dparam/'spec/'def` projection；MVP 只接受普通 `RLnone` 顶层 `let`/`val` routine；
- `vc:sp`、`vc:wp` 等未列入 feature manifest 白名单、且会改变 VC/encoding 的控制属性；普通 term attribute 仍按 `Bytes` 保留；
- 用户直接导入或声明 range、float、bitvector、map、string 等 driver-only theory/类型；隐藏 snapshot 中的 trusted 表示不受此条影响；
- `-L` 或其他用户 loadpath；返回 `UnsupportedFeature(ExternalLoadpath)`；
- counterexample/model、RAC；
- 产品运行时的 prover 自动探测、Whyconf、session/IDE、why3server（测试 oracle 可用隔离 Whyconf）；
- 运行时 `.drv` parser、Dynlink、插件 registry；
- Z3 之外的 prover。

属性与 meta 采用默认拒绝策略：普通、不改变语义路径的 term attributes 原样按 `Bytes` 保存；Why3 已知会改变 VC、transform 或 encoding 的控制属性必须逐个出现在机器可读 feature manifest 的 allowlist 中，否则在 manifest 指定阶段返回 `UnsupportedFeature`。用户源文件中的 `Dmeta` 在整个 MVP 中固定拒绝，不能借 trusted snapshot decoder 绕过。

### 2.3 兼容性原则

- 参考语义固定为 Why3 1.7.2，不追随最新版漂移。
- 产品兼容承诺只覆盖 CLI 行为和本文冻结的 canonical/oracle schema；跨 package 的 `pub` 只为仓库内部编译服务，不构成 library API 稳定承诺。
- `sat` 暂时保持 Why3 通用 SMT driver 的语义：`Unknown("sat")`，不能报告 `Invalid`。
- unsupported 必须 fail closed：未支持结构不得进入 printer。
- 不要求内部对象布局与 OCaml 相同，但 typed semantic、raw Task、每个 transform checkpoint、prepared Task 必须以完整 canonical structure 精确比较。
- SMT lexer 只删除注释并规范空白；用户/snapshot 名称和 declaration/assert/quantifier/pattern/command 顺序精确保留，只对 `OriginKind.Generated(stage)` 的 identifier 按首次出现 alpha-renumber。
- 不以 solver 都返回 `Valid` 作为结构等价的充分证据。

---

## 3. 当前基线

当前仓库已经具备：

- `parser` 独立 package，源输入和标识符以 `Bytes` 表示；
- WhyML 的 Ptree 风格 AST 和 byte/text 两类公开 API；
- 989 个 Why3 1.7.2 `.mlw` fixture；
- 929 个原始 Ptree S-expression 精确一致；
- 58 个双方按预期拒绝；
- 2 个有意支持的 `module M : Interface` parser extension；
- `moon check/test --target all` 的 CI；
- 根 package 暂无公开 API；MVP 将其永久保持为空，因为产品只承诺 CLI。

关键现状文件：

```text
parser/api.mbt
parser/ast_ident_type.mbt
parser/ast_term.mbt
parser/ast_expr.mbt
parser/ast_decl.mbt
tools/check_why3_fixtures.mjs
.github/workflows/check.yml
Dockerfile
```

Parser 输出仍是未经名字解析和类型推导的源 AST。它不能直接作为 WP 或 SMT printer 的输入。

---

## 4. MoonBit package 设计

不要机械地为 Why3 的每个 OCaml 文件创建一个 MoonBit package。`Ty`、`Term`、`Decl` 之间共享大量不安全的内部构造器，应放在同一个 package 中，以便保持这些构造器 private。

```text
parser/                       # 现有 Ptree；本计划原则上不改其行为

core/identity/
  id.mbt                      # context-local SemanticId
  snapshot_symbol_key.mbt     # context-free stable key；stdlib/profile 共用
  name.mbt                    # Bytes 名称、属性
  origin.mbt                  # 与 parser.Span 解耦的来源信息
  context.mbt                 # fresh opaque reference token、Int64 local ID；单线程分配
  *_test.mbt

core/logic/
  type.mbt                    # TyVar、TypeSymbol、Ty
  type_subst.mbt
  type_match.mbt              # immutable Ty matching/instantiation；无 mutable unify
  symbol.mbt                  # VSymbol、LSymbol、PrSymbol
  term.mbt                    # opaque Term 与公开 TermView
  term_make.mbt               # 唯一合法 smart constructors
  term_subst.mbt
  term_freevars.mbt
  decl.mbt                    # user Dtype/Dparam/Dlogic/Dprop + trusted full-schema views
  constant.mbt                # 精确 integer/real/string constants
  known.mbt                   # 声明依赖和 known map
  diagnostic.mbt
  *_test.mbt
  *_wbtest.mbt

core/theory/
  namespace.mbt
  meta.mbt
  theory_item.mbt             # Decl/Use/CloneWitness/Meta 的有序历史
  theory.mbt
  theory_builder.mbt
  task.mbt                    # 有序、持久化 Task
  split_goal.mbt
  *_test.mbt

mlw/
  ity.mbt                     # M3 先落最小 program type
  effect.mbt                  # 首版只有 Pure
  cty.mbt                     # M3 先落 args/result/pre/post
  symbol.mbt                  # M3 先落 program/routine symbols、rs_logic
  namespace.mbt               # program namespace
  pmodule.mbt                 # M3 先落 snapshot/import 外壳
  expr.mbt                    # opaque typed Expr
  pdecl.mbt
  *_test.mbt

environment/
  environment.mbt             # 同 context 的 Theory + Pmodule registry/resolver
  resolver.mbt
  *_test.mbt

stdlib/
  snapshot_manifest.mbt       # 完整 driver Theory/Pmodule closure/schema/hash
  frozen_environment.mbt      # opaque FrozenEnvironment
  handles.mbt                 # 用户可见 StdlibHandles
  driver_symbol_catalog.mbt   # 隐藏 theory 的完整 DriverSymbolCatalog
  generated_builtin.mbt
  generated_bool.mbt
  generated_unit.mbt
  generated_int.mbt
  generated_real.mbt
  generated_driver_*.mbt      # BV/float/map/string 等私有 literal tables
  minimal_env.mbt
  *_test.mbt

elab/                         # 单一 package，延迟 IR 不跨 package 泄漏
  scope.mbt
  dty.mbt                     # package-private 延迟类型
  dty_unify.mbt               # Fresh/Link、occurs check、mutable unification
  dterm.mbt                   # package-private 延迟 term/spec
  type_pattern.mbt
  type_term.mbt
  type_decl.mbt
  type_theory.mbt
  dity.mbt
  pending_spec.mbt
  type_expr.mbt
  type_routine.mbt
  type_module.mbt
  diagnostic.mbt
  logic_api.mbt
  program_api.mbt
  *_test.mbt
  *_wbtest.mbt

vc/
  kode.mbt
  expr_to_kode.mbt
  reflow.mbt
  wp.mbt
  vc_decl.mbt
  *_test.mbt

transform/
  transform_id.mbt            # enum；不做字符串 registry
  feature_scan.mbt
  inline_trivial.mbt
  eliminate_builtin.mbt
  remove_unused.mbt
  eliminate_definition.mbt
  detect_polymorphism.mbt
  discriminate_if_poly.mbt
  eliminate_algebraic_if_poly.mbt
  monomorphise_goal.mbt
  select_kept.mbt
  encoding_smt_if_poly.mbt
  simplify_formula.mbt
  pipeline.mbt
  *_test.mbt

printer/smtv2/
  query.mbt
  name_allocator.mbt
  token_normalizer.mbt        # 仅 Generated(stage) identifier alpha-renumber
  escape.mbt
  print_type.mbt
  print_term.mbt
  print_decl.mbt
  print_task.mbt
  diagnostic.mbt
  *_test.mbt

prover/
  limits.mbt
  command.mbt                 # CommandSpec；纯数据
  raw_outcome.mbt
  result.mbt
  *_test.mbt

prover/z3/
  profile.mbt                 # 固定 transform 顺序和 syntax/remove
  command.mbt                 # 纯 argv builder
  prepared_call.mbt           # opaque PreparedCall 与只读 accessors
  prepare.mbt
  result_parser.mbt
  *_test.mbt

prover/native/
  runner.mbt                  # native-only async process runner
  bounded_capture.mbt
  timeout.mbt
  *_test.mbt

pipeline/
  check.mbt
  checked_file.mbt            # opaque CheckedFile：typed units + raw goals
  tasks.mbt
  emit_smt.mbt
  prepare_proof.mbt           # 只生成 PreparedCall，不启动进程

oracle/canonical/
  schema.mbt                  # all-target、非 test-only 的稳定 schema
  sha256.mbt                  # all-target SHA-256；canonical bytes 的唯一 hash 实现
  typed.mbt
  task.mbt
  prepared.mbt
  goal_record.mbt             # portable CanonicalGoalRecord
  ndjson.mbt
  *_test.mbt

cmd/why3/
  args.mbt
  diagnostic.mbt
  main.mbt                    # native-only；含 --canonical-json/NDJSON

tools/
  check_why3_semantics.mjs
  check_smt_tokens.mjs
  update_oracle.mjs
  contracts/                  # feature/schema/toolchain/corpus machine-readable locks
  why3_oracle/                # 测试专用 OCaml oracle
    export_stdlib.ml           # 导出完整 driver theory/pmodule closure
    export_driver.ml           # 递归导出 z3_487 imports 与 symbol inventory
    patches/driver-trace.patch
```

### 4.1 依赖 DAG

箭头统一表示“左侧 dependent 的 `moon.pkg` 直接 import 右侧 dependency”；这里不依赖传递式 package alias：

```text
core/logic       -> core/identity
core/theory      -> core/logic + core/identity
mlw              -> core/identity + core/logic + core/theory
environment      -> core/identity + core/logic + core/theory + mlw
stdlib           -> core/identity + core/logic + core/theory + mlw + environment
elab             -> parser + core/identity + core/logic + core/theory + mlw + environment
vc               -> core/identity + core/logic + core/theory + mlw
transform        -> core/identity + core/logic + core/theory
printer/smtv2    -> core/identity + core/logic + core/theory
prover/z3        -> core/identity + core/logic + core/theory + prover + transform + printer/smtv2
prover/native    -> prover + moonbitlang/async + moonbitlang/async/process
oracle/canonical -> core/identity + core/logic + core/theory + mlw + prover + prover/z3 + printer/smtv2
pipeline         -> parser + core/identity + core/logic + core/theory + mlw + environment + stdlib + elab + vc + prover + prover/z3 + printer/smtv2
cmd/why3         -> prover + prover/z3 + pipeline + prover/native + oracle/canonical + moonbitlang/async
```

`Environment` 由独立 `environment` package 所有并传入 `elab`，同时注册 pure Theory 与 program Pmodule；若实现文件直接提及上表之外 package 的公开类型，就同步把它加入对应 `moon.pkg`，CI 用 `moon check --target all` 防止图与实际 import 漂移。

必须遵守的防环规则：

- `core/*` 不 import `parser`；`elab` 负责把 `@parser.Span` 转为 `Origin`。
- `elab` 接收 `@environment.Environment`，不直接 import `stdlib`；pure/program elaboration 同处一个 package，复用同一份 `Dty/Dterm/scope/type_term`。
- `printer/smtv2` 不 import Z3。
- `prover/z3` 不 import process/filesystem，因此 profile、argv 和结果 parser 可以跨 target 测试。
- 只有 `prover/native` 和 `cmd/why3` 限制为 `+native`。
- `pipeline` 只生成 `PreparedCall`，不 import `prover/native`；启动 Z3 只发生在组合二者的 `cmd/why3`。
- `oracle/canonical` 是可由正常 executable 调用的 all-target package，不依赖 package-private test 函数。
- 不改变根模块当前 `preferred_target = "wasm-gc"`。

根 package 在整个 MVP 中保持空。下述跨 package `pub`/opaque type 只是 MoonBit package 间编译边界；产品不发布或承诺 library API。每个里程碑仍运行 `moon info`，并在同一长期实现分支上以原子 commit 提交、审查生成 `.mbti`；里程碑完成不创建独立 PR。审查 `.mbti` 的目的是发现意外边界变化，不是建立兼容性承诺。

### 4.2 API 边界

以下 typed semantic 类型公开但保持 opaque：

```text
SemanticId
SnapshotSymbolKey
CompilationContext
Origin
OriginKind
Ty
TypeSymbol
VSymbol
LSymbol
PrSymbol
Term
Decl
Theory
Task
FrozenEnvironment
StdlibHandles
DriverSymbolCatalog
Ity
Cty
RoutineSymbol
Expr
Pdecl
Pmodule
SmtQuery
CommandSpec
Z3StaticSpec
DriverSymbolResolver
Z3Profile
PreparedCall
GoalInfo
CheckedFile
```

`Environment`、trusted decoder 和所有 `generated_*.mbt` constructor 保持 private；如果因 MoonBit package 编译边界必须使用 `pub`，也不得由根 package re-export，且只能被明确列出的内部 dependency 调用。

所有者和读取协议固定如下：

```text
prover/z3.PreparedCall::raw_task()      -> Task
prover/z3.PreparedCall::prepared_task() -> Task
prover/z3.PreparedCall::query()         -> SmtQuery
prover/z3.PreparedCall::command()       -> CommandSpec
prover/z3.PreparedCall::goal_info()     -> GoalInfo

pipeline.CheckedFile::typed_units()     -> ArrayView[TypedUnitView]
pipeline.CheckedFile::raw_goals()       -> ArrayView[Task]
pipeline.prepare_proof(CheckedFile, ...) -> Array[PreparedCall]
```

`TypedUnitView` 由 `pipeline/checked_file.mbt` 所有，穷尽为 `Theory(Theory) | Module(Pmodule)`。`GoalInfo` 由 `prover/z3/prepared_call.mbt` 所有并提供只读字段：unit kind/name、goal `PrSymbol`/display name、goal ordinal、`Origin`、ordered `expl` attributes；这些字段足够生成 NDJSON selector/metadata，不让 `cmd` 反向解析 pretty text。

`oracle/canonical` 直接接受 `Theory/Pmodule/Task/PreparedCall` 的只读 view；`cmd/why3 --canonical-json` 从 `CheckedFile` 取 typed/raw，再从 `PreparedCall` 取 prepared/query/command，canonicalizer 不反向 import `pipeline`。

`pipeline.check` 每次新建一个 `CompilationContext`，调用 `minimal_env(context) -> FrozenEnvironment`，并在 opaque `CheckedFile` 内共同持有该 frozen environment、typed units 和 raw goals。`FrozenEnvironment` 内部同时拥有用户 resolver 用的 `Environment`、公开标准库句柄 `StdlibHandles`、完整隐藏目录 `DriverSymbolCatalog` 和已校验 manifest；这些部分不能被 caller 拆开或替换。

静态 Z3 profile 通过 `FrozenEnvironment` 中的 catalog eagerly 绑定 manifest 的每一个 driver entry。任一 key 缺失、symbol kind 不符、digest 不符或 context 不符时立即返回 `BindError`；不能只按本次 Task 的实际引用做 lazy binding。用户 resolver 永远看不到 `DriverSymbolCatalog`。

外部遍历通过只读 view：

```text
Ty::view() -> TyView
TypeSymbol::view() -> TypeSymbolView
VSymbol::view() -> VSymbolView
LSymbol::view() -> LSymbolView
PrSymbol::view() -> PrSymbolView
Origin::view() -> OriginView
Term::view() -> TermView
Decl::view() -> DeclView
Theory::items() -> ArrayView[TheoryItemView]
Theory::export_namespace() -> NamespaceView
Task::items() -> ArrayView[TaskItemView]
Task::declarations() -> ArrayView[Decl]          # 仅 convenience，canonical 不用
Ity::view() -> ItyView
Cty::view() -> CtyView
RoutineSymbol::view() -> RoutineSymbolView
Expr::view() -> ExprView
Pdecl::view() -> PdeclView
Pmodule::items() -> ArrayView[PmoduleItemView]
Pmodule::pure_theory() -> Theory
Pmodule::export_namespace() -> ProgramNamespaceView
SmtQuery::bytes() -> BytesView
CommandSpec::view() -> CommandSpecView
```

`CommandSpecView` 可供 runner 取得 argv，但 portable canonical encoder 只序列化 profile id、transport、limit 和 executable request；resolved path、继承环境与实际 spawn argv 只能进入 `resolved_context.json`。

这些 view enum 必须穷尽 opaque IR 的正式结构：

```text
TheoryItemView/TaskItemView = Decl | Use(TheoryKey) | Clone(CloneWitnessView) | Meta(MetaView)
PmoduleItemView             = PureDecl | ProgramDecl | Use(PmoduleKey) | Clone(PmoduleCloneWitnessView) | Meta
```

`CloneWitnessView` 暴露 source key、按 source key 排序的 type/logic/prop instantiations 和 source item identity；namespace view 暴露按 Bytes key 排序的 type/logic/prop/program entry。任何 opaque node 新增 variant 时，其 view 也必须新增 variant，使 canonicalizer 因非穷尽 match 编译失败，而不是漏序列化。

trusted snapshot decoder 的 schema 必须能无损表示当前完整 closure 实际出现的：

```text
type definitions: NoDef | Alias | Range | Float
declarations:     Ddata | Dparam | Dlogic | Dind(Ind) | Dprop
theory history:   Use | Clone | Meta
constants:        integer | real | string
```

这些 constructor 不向用户 elaborator 开放。exporter 一旦遇到 schema 未列出的 declaration/type/constant variant，M0 inventory/export gate 立即失败；必须升级 versioned schema、canonicalizer 和 vectors 后重新导出，禁止临时用 opaque payload 或放宽 decoder。

typed IR 不使用 `pub(all)` 暴露原始字段。公开 smart constructor 必须维护：

- term 类型正确；
- formula 与 bool-valued term 的区别；
- symbol arity 正确；
- trigger 合法；
- declaration 仅引用已知符号；
- substitution 捕获规避；
- Task 中 goal 位于最后且之后不能追加 declaration。

---

## 5. 跨阶段语义不变量

这些规则从第一天开始执行，不能推迟到重构阶段。

### 5.1 名称、身份与来源

- 源标识符和 WhyML 文件内容继续使用 `Bytes/BytesView`。
- 人类诊断可以在明确 UTF-8 解码边界后使用 `String`。
- 语义等价基于 `SemanticId`，不能基于名称字符串或对象物理相等。
- `CompilationContext` 每次构造都分配一个 fresh opaque reference 作为不可伪造、不可序列化的 token，并维护 context-local `Int64` 递增 ID；MVP builder 固定单线程使用，不声称 allocator 线程安全。
- `SemanticId` 逻辑上是 `(token-reference, local-id)`：相等性同时比较 token 的引用身份与 local ID；hash 实现允许只使用 local ID，因为相等对象必有相同 local ID，碰撞由 map 处理。
- 一个编译单元使用的 `Environment`、冻结 stdlib、所有 imported Theory 和当前声明必须从同一个 `CompilationContext` 实例构造。注册 Theory、构造 Decl/Task、合并 namespace 时都检查 context；跨 context 混用返回 `ContextMismatch`，即使两个 local ID 数值相同也绝不相等。
- canonicalizer 不输出 context token，只按声明/首次出现顺序重新编号，因此独立编译仍可稳定差分。
- `OriginKind = User | Snapshot | Generated(stage)` 与 display/export name、source span、attributes 分字段保存；只有 `Generated(stage)` 能进入 SMT alpha normalization。
- `SnapshotSymbolKey` 精确由 `(theory-key, theory-item-ordinal, declaration-inner-ordinal, symbol-kind, symbol-digest)` 构成。export/alias/qualified 名称另存于 namespace entry，只用于解析与显示，绝不参与 symbol identity。
- 普通 term attributes 原样以 `Bytes` 保存。会改变 VC/transform/encoding 的已知控制属性由 feature manifest 按 byte pattern 白名单控制；未命中白名单即 `UnsupportedFeature`，不能当普通属性透传。
- 不依赖 OCaml 的全局 weak hash-cons；首版可不做 hash-cons。

### 5.2 类型和 formula

- Why3 中 formula 与类型为 `bool` 的 value term 不是同一类；建议让 `Term::ty()` 返回 `Ty?`，`None` 表示 formula。
- semantic core 的 smart constructor 保持二者严格区分；但 elaborator 必须兼容 Why3 1.7.2 的 expected-kind coercion：bool value 用 `t = true` 提升为 formula，formula 用 `if f then true else false` 降为 bool value。转换节点必须显式生成并保留 location，不能在 printer 中偷偷转换。
- 延迟类型 `Dty` 只存在于 elaborator；最终 semantic `Ty` 可以含已绑定身份的 `TyVar`，但不能含未解 `Fresh/Link` cell。
- 统一必须包括 path compression、occurs check、arity check 和 strict finalize。
- 用户纯逻辑 declaration 边界将允许泛化的未解变量按 Why3 1.7.2 顺序确定性泛化，因此 abstract/alias type、symbol 与 proposition 可以多态；不允许泛化的位置仍由 strict finalize 报 `TypeError`。
- 用户 program routine 的 `Cty` 在 finalize 时必须完全单态；trusted stdlib polymorphic routine 只能在调用点实例化为单态 `Cty`。任何用户 routine type variable 都在 elaboration 阶段拒绝，不能依赖 SMT monomorphisation 补救。
- `detect_polymorphism` 到 `encoding_smt_if_poly` 只处理受支持的纯逻辑窄路径；printer 前的 feature scan 必须证明 Task 中没有残余 type variable。

### 5.3 有序性和确定性

- Theory declaration、Task declaration、argument、trigger、assert 的顺序保持原始语义顺序。
- `Map` 仅用于 lookup；不能直接用其遍历顺序决定 SMT 输出。
- 需要顺序的结构同时保存有序 `Array` 和索引 Map。
- canonicalizer 为 bound variable 使用 de Bruijn index。semantic canonical structure 保留 symbol origin；SMT normalizer 仅为 `Generated(stage)` 标识符按 token stream 首次出现分配序号，用户与 snapshot 名称逐 token 保留。
- 整数直接复用现有 `BigInt`；实数直接复用 Parser 的精确 `RealValue(significand, pow2, pow5)` 并在 typed core 中保持该规范形，SMT/canonical 阶段再确定性转换，任何阶段都不能经过 `Double`。

### 5.4 错误分层

最少定义：

```text
ResolveError
TypeError
UnsupportedFeature
ContextMismatch
BindError
InvariantViolation
TransformError
PrintError
ConfigError
ProcessError
OutputLimitExceeded
MalformedProverOutput
ProverResult
```

`UnsupportedFeature` 至少包含 feature enum、stage、span 和简短说明。用户输入与基础设施错误统一通过 typed `raise` 传播；`ProverResult` 只表示 solver 已成功启动、完成并被结果规则分类后的 outcome，不承载 spawn、I/O、output-limit、非零未分类退出或 malformed output。用户错误、基础设施错误与内部 invariant failure 必须区分。

---

## 6. 实施里程碑

本节的 M 编号是 capability gate；第 10 节的阶段 00 至阶段 12 是同一长期实现分支上的唯一实施顺序，不对应独立 PR。对应关系固定为：M0=阶段 00，M1=阶段 01..02，M2=阶段 03，M3=阶段 04..05，M4=阶段 06，M5=阶段 07，M6=阶段 08，M7..M8=阶段 09，M9=阶段 10，M10=阶段 11，M11=阶段 12。canonical encoder 从阶段 01 起随 IR 增量实现。全部阶段、可在本地或非 PR 工作流执行的最终 gate，以及第 13 节中不依赖最终 PR 的验收项完成前不得创建 PR；完成后只创建一个面向 `main` 的最终 PR，再由该 PR 运行 PR 专属 CI gate。

每个里程碑均要求：

```bash
moon check --target all --warn-list +73
moon test <affected-packages> --target all
moon info
moon fmt
```

涉及 process 的 package 改用 `--target native`。每次 `moon info` 后审查 `.mbti`，不能直接编辑生成文件。

### M0：冻结契约、oracle 和许可

#### 实现项

- 将整个仓库的目标许可固定为 Why3 的 LGPL 2.1，并原样附带 Why3 special linking exception。阶段 00 同时更新根 `LICENSE`、`moon.mod` 的 license 字段及 README/NOTICE；任何逐段或逐行翻译保留对应 Why3 copyright，并记录翻译/修改日期。此项不再留作后续法律决策。
- 固定 Why3 `1.7.2` commit、shape version、`z3_487.drv` 完整 recursive import closure、该 closure 引用的全部 pure Theory 及传递 `use/clone` closure、prover detection data 和 semantic snapshot inventory。
- 新建机器可读 `tools/contracts/features-v1.json`。它逐项覆盖每个 Ptree variant，并记录：variant、允许形态、拒绝阶段、稳定 error kind、fixture ID 和 lane。lane 固定为：

```text
exact
reject
intentional-divergence
unsupported
```

- manifest 同时冻结 control-attribute byte allowlist；普通 term attribute 按 `Bytes` 保留，已知会改变 VC/encoding 的属性未命中 allowlist 时返回 `UnsupportedFeature`。用户 `Dmeta` 明确记录为 MVP reject。
- 最终 PR gate 使用的 corpus 固定为阶段 00 提交的 `tools/contracts/pr-corpus-v1.json` 中完整、有序、逐 fixture/goal 枚举的 inventory，并锁定其 SHA-256。该文件不得使用目录 glob、数量范围或“之后再选”的占位；增删 entry 必须走显式 schema/profile 变更。
- 冻结 portable canonical schema、trusted snapshot decoder schema 和 exporter variant inventory；exporter 遇到 schema 外 variant 时 M0 失败，先升级 schema，不能临时放宽。
- 建立 `tools/why3_oracle`、versioned `CanonicalGoalRecord`/`OracleGoalEnvelope` schema 和标准 cross-language vectors 的空骨架。
- 强 oracle gate 固定为 Linux x86_64（OCI platform `linux/amd64`）镜像；`tools/contracts/toolchain-lock.json` 保存镜像 immutable digest、所有 GitHub Action 的 full commit SHA、build recipe commit 和 runner architecture。
- MoonBit 编译工具链不纳入 oracle 镜像或 `toolchain-lock.json`：CI 通过 full-commit 固定的 `moonbit-community/setup-moonbit` 安装 `stable`，记录实际版本用于诊断，但不做 exact version/binary hash gate。`moonbitlang/async@0.20.2` 等依赖 closure 仍由 `moon.mod` 与独立 manifest 固定；Why3 commit `1343338d3bb1941c0d4f134283bb0790816113c4`、Z3 `4.8.12` 及其 binary hash 继续锁定。普通 CI 禁止 `uses: ...@main` 和 tag-only action ref；fresh runner 在 setup 后执行 `moon update && moon check`，并立即校验 dependency manifest，因此 registry 刷新不放宽精确依赖 closure。
- M0/阶段 00 完成前，不得开始会固化 identity、snapshot 或 canonical schema 的后续实现阶段；native runner spike 不接触这些 schema，可以独立并行。

#### 固定基线

```text
Why3 source/fixture commit:
1343338d3bb1941c0d4f134283bb0790816113c4

Moon toolchain:
CI setup-moonbit stable（仅记录实际版本，不进入 oracle lock）

moonbitlang/async:
0.20.2

oracle platform:
linux/amd64

Z3:
4.8.12

drivers/z3_487.drv:
e9a25b112d47c672757d9e25da2da420ad8ef53f9a93f2eb7dfcc3437ebb4ff0

drivers/smt-libv2.gen:
73687a2e3626e569f4a2bf5cb74dfd6c33c7019f8d816150538840cb4fca878a

drivers/why3.drv:
9ac85a936a0526112fec236f1b32a0d1315422071a83f7ab52010168c0eadaed

drivers/why3_smt.drv:
66101f2eea98ca0e772b29bcbec9f84896524e56c9bf8223044470b65ed9472a

share/provers-detection-data.conf:
4b27f49c6d17b8c66ac2187d0405373d73c7fc2d6aed0f1ae564b1906b1cb427
```

阶段 00 的正式 lock 文件不得含占位值：除以上固定值外，还要记录 `z3_487.drv` 的完整递归 driver import closure、全部 Theory/Pmodule/use/clone closure inventory 与 hash、feature/corpus/schema manifest hash、OCI image digest、action full commit、Why3/Z3 executable hash。MoonBit 实际版本仅作为 CI 诊断，不进入 lock。阶段 04 生成 candidate tables 时在 snapshot manifest 中新增实际 stdlib/driver exporter hash；阶段 07 增加 trace patch SHA-256、目标 Why3 commit 和 checkpoint 序列。这些后续字段只能填入已冻结 schema 的对应 artifact manifest，不能反向改写阶段 00 的 identity/schema 决策；任一已存在字段漂移都使 oracle 失败，而不是自动更新 golden。

#### 退出条件

- 当前 989 parser corpus 不回退。
- 普通 CI 不会修改 golden。
- 版本、driver 或 fixture inventory 漂移时测试立即失败。
- feature manifest 对全部 Ptree variant 穷尽，且每个 corpus entry 都有明确 feature tags、goal inventory 和 lane。
- 根 `LICENSE`/`moon.mod`/README/NOTICE 已一致改为 LGPL 2.1 + 原样 special exception；翻译文件 attribution 规则可由 CI 检查。
- oracle job 只从 digest-pinned `linux/amd64` image 与 commit-pinned actions 启动；普通 CI 只显式执行 fresh-runner 所需的 `moon update && moon check` registry bootstrap，并紧接精确 dependency manifest 校验，不隐式更新依赖 lock 或 golden。

### M1：Identity 与类型内核

参考原版：

```text
../why3/src/core/ident.ml
../why3/src/core/ty.ml
../why3/src/core/dterm.ml
```

#### 实现项

- `CompilationContext`、`SemanticId`、`OriginKind(User/Snapshot/Generated(stage))`、`Origin`、semantic attributes；context token 是 fresh opaque reference，ID 是 context-local `Int64`，builder 单线程。
- `SnapshotSymbolKey = (theory key, item ordinal, declaration-inner ordinal, symbol kind, digest)`；export/alias 名称单独进入 namespace metadata。
- `TyVarSymbol`、`TypeSymbol`、`TyVar`、`TyApp`。
- 参数化 abstract/alias/NoDef 表示；trusted decoder 可表示 Range/Float，用户 elaborator 与用户 resolver 仍拒绝这些构造。
- `core/logic` 只实现 immutable `Ty` 的 substitution、matching、instantiation 和 free vars，不保存 `Fresh/Link`。
- `elab` 拥有 `Dty = Fresh | Link | App | Known`、mutable unification、occurs check、纯逻辑泛化和 program strict finalize；`Dty/Dterm` 不出现在 semantic package 边界。
- 从本里程碑开始增量实现 versioned canonical encoder，而不是等待 Task 完成；同时在 `oracle/canonical` 内置 all-target SHA-256，并用 NIST/常用标准向量锁定实现。

#### 测试

- fresh ID 和同名不同身份；
- 两个 context 产生相同 local ID 时仍不相等；
- alias 展开和 arity mismatch；
- unify 成功/失败；
- occurs check；
- 未解变量 strict finalize；
- substitution 组合；
- `SnapshotSymbolKey` 不受 export/alias 重命名影响，ordinal/kind/digest 任一变化都会改变 key；
- `Generated(stage)`、User、Snapshot origin 的 canonical 与 SMT-normalization eligibility 分离；
- SHA-256 空串、`abc`、multi-block 标准向量在所有 target 一致；
- Bytes 非 ASCII 名称不改变 source offsets。

#### 退出条件

- 无法通过公开 API 构造 arity 错误的 semantic `Ty`。
- 所有错误包含稳定 kind 和位置。
- all-target 单测通过。

### M2：Typed Term、Symbol、Decl

参考原版：

```text
../why3/src/core/term.ml
../why3/src/core/decl.ml
../why3/src/core/dterm.ml
```

#### 实现项

- `VSymbol`、`LSymbol(args, result?)`、`PrSymbol`。
- typed term/formula node：

```text
Tvar
Tconst
Tapp
Tif
Tlet
Tquant(forall/exists)
Tbinop
Tnot
Ttrue/Tfalse
Tattr
```

- lambda/case/epsilon 可以暂有 internal enum tag，但不能由 MVP public constructor 产生。
- smart constructors 做 arity、argument type、result type、formula/value 检查。
- free variables、type variables、alpha normalization、capture-safe substitution。
- trigger 校验：只允许属于量词体且类型正确的 term。
- integer、real 与 string constant 都有精确 typed/canonical 表示；string 按 bytes/escape schema 保存，不能经过 host locale 或 lossy UTF-8 转换。
- `Dtype`、`Dparam`、非递归 polymorphic `Dlogic`、polymorphic `Dprop(Paxiom/Plemma/Pgoal)`。
- core 能只读表示完整 snapshot closure 所需的 `NoDef/Alias/Range/Float`、`Ddata/Dparam/Dlogic/Dind(Ind)/Dprop`、`Use/Clone/Meta` 及整数/实数/字符串常量。固定 closure 中的 `why3.WellFounded.WellFounded` 含一个 trusted `Dind(Ind)`；decoder 必须无损载入它并由 `eliminate_inductive` 在 printer 前消除，`Dind(Coind)` 仍是 schema 外错误。它们只能由校验 schema/hash/invariant 的 trusted snapshot decoder 载入；用户 datatype、inductive/coinductive、Range/Float 与用户 `Dmeta` 继续在 elaboration/resolution 阶段拒绝。
- `KnownMap` 检查重复符号、未知依赖、定义环和 declaration 合法性。
- 为 `oracle/canonical` 提供只读 view；canonical semantic JSON 的实现不放在 test-only API 中。

#### 测试

- function/predicate 混用；
- equality 类型不一致；
- semantic constructor 在未显式转换时拒绝 formula/value 混用；
- shadowing、alpha rename、capture avoidance；
- nested quantifier 和 trigger；
- 同一 polymorphic symbol 的多个类型实例，以及 proposition 中自由类型变量的确定性泛化；
- trusted Range/Float/String/Ddata canonical bytes 跨 target 一致，用户 constructor 无法创建这些 snapshot-only shape；
- declaration 引用未来符号；
- lemma/goal formula 类型检查。

#### 退出条件

- typed core 的公开 API 无法产生 ill-typed Term/Decl。
- canonical dump 在不同运行和不同 target 上一致。

### M3：最小 MLW 符号外壳、Theory/Pmodule Environment、冻结 semantic stdlib

参考原版：

```text
../why3/src/core/theory.ml
../why3/src/core/env.ml
../why3/src/core/task.ml
../why3/src/mlw/pmodule.ml
../why3/src/mlw/ity.ml
../why3/src/mlw/expr.ml
```

#### 实现项

- Namespace：type/logic/prop 子空间；qualified lookup；open/import 行为。
- `TheoryItem`/`TaskDecl` 有序表示 `Decl`、`Use(TheoryKey)`、`CloneWitness` 和 `Meta`。`CloneWitness` 保存 source `TheoryKey`、type/logic/prop instantiation map 与 source item identity，只能由 trusted snapshot decoder 创建；它是 import/driver history，不提供通用 clone 运算。
- `TheoryBuilder` 和不可变 `Theory`；`Decl/Use/CloneWitness/Meta` 历史顺序及 export namespace。用户 `use` 可创建 `Use`，用户 `clone` 仍拒绝；snapshot loader 才能创建 `CloneWitness`。
- 为标准库导入提前建立最小 `Ity`、Pure `Effect`、`Cty`、`RoutineSymbol(rs_logic)`、program namespace 和只读 `Pmodule` 外壳；此时不实现用户 Expr/WP。
- 独立 `Environment`：同一 context 下的用户可见 Theory + Pmodule registry，key 为字节路径和 theory/module 名；pure `use` 解析 Theory，module 中的 `use` 解析 Pmodule 及其 pure theory projection。
- 不实现通用 `clone`，也不手写删减版公理。由固定 Why3 1.7.2 exporter 递归解析 `z3_487.drv` 的全部 imports，再导出这些 driver entry 引用的所有 pure Theory 及其传递 `use/clone` closure；该闭包包含实际需要的 BV、float、map、string 等 driver theory，而不只导出用户可见的五个入口。
- 用户可见入口固定为：

```text
BuiltIn
Bool
Unit
int.Int
real.Real
```

- snapshot 的完整 pure 部分必须逐 item 保留 dependency order、qualified symbol reference、attributes、`Use`、clone source/instantiation witness、driver meta 所引用的 type/logic/prop handle，以及原版完整 algebra/range/float/string declarations/axioms；只保存 clone 结果与历史，不实现 clone evaluator。
- snapshot 的 program 部分必须保留每个 Pmodule 的 exported namespace、`RoutineSymbol`、参数/result `Ity`、`Cty`、effect、`rs_logic` 对应关系和 attributes。尤其 `int.Int` 的 `(-_)`、`>=`、`<` 等必须能在 module expression 中按 program symbol 解析，不能退化为按名字特判 LSymbol。
- exporter 产物是 checked-in、private 的 `generated_*.mbt` literal tables 与 versioned manifest；产品运行时不读取 snapshot、stdlib、driver 或 manifest 文件，不访问文件系统。
- manifest 记录导出器版本、源 commit、每个 Theory/Pmodule canonical SHA-256、完整 driver closure inventory 和总 transform-influence closure SHA-256。
- `minimal_env(context)` 返回 opaque `FrozenEnvironment`。其内部持有用户 `Environment`、用户入口 `StdlibHandles`、完整 `DriverSymbolCatalog` 和 manifest；所有 symbol 在给定 context 内重新 intern，不复用生成时 runtime ID。
- `DriverSymbolCatalog` 包含全部隐藏 theory/symbol，但不注册到用户 resolver。用户 `use` 或 qualified reference 指向 BV/float/map/string 等已知隐藏 key 时精确返回 `UnsupportedFeature(DriverOnlyTheory)`；其他未知 key 返回 `ResolveError`。
- `StdlibHandles` 明确暴露同 context 的 `bool/int/real/unit` type handle 和 MVP builtin/operator handle；类型检查、driver 和 printer 均不得按源码拼写猜测内建身份。
- program handles 同时精确暴露 `real.Real` 的常量、算术、比较 `RoutineSymbol/Cty/rs_logic`，供后续单态 Program Real elaboration 使用。
- `use` 展开和 `use import` namespace 可见性。
- 有序、持久化 `Task`；goal-last invariant。
- `split_theory`：先前 lemma 作为后续 task 的 axiom；每个 lemma/goal 形成一个单 goal Task。

#### 测试

- duplicate/open ambiguity/unbound qualified name；
- 两个 context 即使 local ID 相同也不能混用；`Environment`、stdlib snapshot、imported Theory/Pmodule、Task 和当前编译共享一个 context，跨 context 注册/建 Task 返回 `ContextMismatch`；
- `use int.Int` 与 `use import int.Int` 的可见性差异；
- theory 中 `use int.Int` 取得 pure namespace；module 中 `use int.Int` 同时取得 Pmodule program namespace，`-x`/`x >= 0` 分别解析到带 `rs_logic` 的 routine；
- 同名 shadowing；
- lemma 在后续 goal task 中变为 axiom；
- 每个 task 恰有一个末尾 goal；
- declaration 顺序稳定。
- `Use/CloneWitness/Meta` history、clone instantiation map 与 oracle canonical 顺序一致，driver update 可查询相同 history。
- 全部 driver catalog key 均可按 manifest 绑定；任意 declaration/routine/meta/rs_logic 缺失、类别错或 digest 错立即失败。
- 用户导入每个隐藏 BV/float/map/string theory 都得到精确 `UnsupportedFeature(DriverOnlyTheory)`，随机未知 theory 得到 `ResolveError`。
- trusted Range/Float/String/Ddata 在 native/js/wasm target 的 canonical bytes 完全一致。

#### 退出条件

- 可以仅用 semantic API 构造纯逻辑 Theory 并 split 成 Task。
- `abs` 的 program operators 在尚未实现用户 Expr 前已能从 Pmodule namespace 解析出精确 `RoutineSymbol/Cty/rs_logic`。
- `real.Real` 的 program operators 同样可解析到精确 `RoutineSymbol/Cty/rs_logic`。
- full canonical raw snapshot Task、完整 `DriverSymbolCatalog` inventory 与 typed stdlib Pmodule projection（忽略 runtime/context tag）均和同一 OracleContext 的 Why3 oracle 一致。

### M4：纯逻辑 elaborator

参考原版：

```text
../why3/src/parser/typing.ml
../why3/src/core/dterm.ml
```

#### 实现项

- `@parser.Pty` 到 delayed `Dty`，再 finalize 为 `Ty`。
- 作用域栈和 qualified name lookup。
- Ptree Term 到 delayed typed term，再构造 immutable Term。
- expected-kind elaboration 显式实现 Why3 Bool coercion：value-to-formula 生成 `t = true`，formula-to-value 生成 `if f then true else false`；两向都做 canonical oracle 测试。
- 支持参数化 abstract/alias `Dtype`、非递归 polymorphic `Dlogic`、polymorphic `Dprop`、`Dscope/Duse*`；在 declaration 边界按 Why3 1.7.2 精确泛化，而不是把自由类型变量报成 strict-finalize error。
- 同一文件中 theory/module 的顺序注册。
- ordinary term attributes 逐 byte 保留；control attribute 查询 M0 allowlist。用户 `Dmeta`、program declaration、clone、datatype 等在 manifest 指定阶段分类为 `UnsupportedFeature`，不能误报成一般 type error。
- diagnostic 中保留 parser span、实际/期望类型和 error kind。

#### 差分门槛

```bash
LC_ALL=C why3 --no-load-default-plugins prove --parse-only input.mlw
LC_ALL=C why3 --no-load-default-plugins prove --type-only input.mlw
```

比较 accept/reject、阶段、error kind、位置；不逐字比较诊断文案。

#### 退出条件

- MVP 纯逻辑 fixture 的接受/拒绝与 Why3 一致。
- 参数化 alias/abstract type、同一 polymorphic symbol 的多种实例、自由类型变量 goal 均通过 typed exact gate；用户 datatype/高阶/lambda/epsilon/递归保持精确拒绝。
- `oracle/canonical` 可从正式 executable 输出 typed Theory/Task NDJSON，且跨 target 稳定。
- unsupported 不会进入 Task。

### M5：静态 Z3 driver update 与 transform pipeline

参考原版：

```text
../why3/src/driver/driver.ml
../why3/drivers/z3_487.drv
../why3/drivers/smt-libv2.gen
../why3/src/transform/inlining.ml
../why3/src/transform/eliminate_definition.ml
../why3/src/transform/remove_unused.ml
../why3/src/transform/detect_polymorphism.ml
../why3/src/transform/simplify_formula.ml
```

#### 静态 profile

不实现 `.drv` parser。将 profile 编译为 typed 数据：

```text
Z3StaticSpec {                 # context-free，可全局常量
  printer = SmtV26
  transforms = [...固定 TransformId...]
  syntax = SnapshotSymbolKey -> SmtTemplate
  remove = Set[SnapshotSymbolKey] + RemoveAllProps
  metas = Array[UnboundDriverMeta[SnapshotSymbolKey]]
  remove_unused_roots = KeepAndDependencyGraph[SnapshotSymbolKey]
  preludes = Array[Bytes]
  command = Z3 argv builder
  result_patterns = fixed result rules
}

Z3Profile {                    # 绑定某个 CompilationContext 后的 typed profile
  context = ContextToken
  syntax/remove/metas = ...SemanticId/typed symbol...
  ...
}
```

`Z3StaticSpec` 不能持有某次 `minimal_env(context)` 的 `SemanticId`。context-free `SnapshotSymbolKey` 由 `core/identity` 所有，固定为 theory key、theory item ordinal、declaration 内 ordinal、symbol kind 和 manifest symbol digest；qualified export/alias 名称另存且不参与身份。因而 `stdlib` 与 `prover/z3` 无需互相 import。

`prover/z3` 只定义使用中立 core 类型的 `DriverSymbolResolver`：

```text
resolve_type(SnapshotSymbolKey)  -> Result[TypeSymbol, BindError]
resolve_logic(SnapshotSymbolKey) -> Result[LSymbol, BindError]
resolve_prop(SnapshotSymbolKey)  -> Result[PrSymbol, BindError]
```

`pipeline` 从同一次 `minimal_env` 返回的 `FrozenEnvironment` 取得 `DriverSymbolCatalog` adapter，再调用 `@z3.bind_profile(spec, resolver, context)`；该签名不出现 stdlib concrete type，所以 `prover/z3` 不 import `stdlib`。bind 必须 eagerly 遍历并解析静态 profile 的全部 syntax/remove/meta/dependency entry，而不是只绑定当前 Task 用到的 symbol；缺 key、类别/digest 不符或 context 不同立即返回 `BindError`。profile 只能在该 context 生命周期内使用，禁止跨编译全局缓存 typed profile。

绑定后的 `TypedDriverMeta` 至少覆盖本 closure 实际使用的 `encoding:kept`、`encoding:lskept`、`encoding:ignore_polymorphism_ts/ls`、`algebraic:kept`、`select_alginst_default`、`eliminate_algebraic` 和 counterexample metas。它们引用同 context 的 snapshot semantic symbol，不按名字临时查找。stdlib snapshot 同时保留 `remove_unused:keep/dependency` 与 derived operator definition；否则 driver update、`detect_polymorphism` 和 `remove_unused_keep_constants` 不可能与原版一致。

#### 原版顺序

```text
counterexamples_dependent_intros
inline_trivial
eliminate_builtin
remove_unused_keep_constants
detect_polymorphism
eliminate_definition_conditionally
eliminate_inductive
eliminate_epsilon
eliminate_literal
simplify_formula
prepare_for_counterexmp
eliminate_projections_sums
discriminate_if_poly
eliminate_algebraic_if_poly
encoding_smt_if_poly
```

#### MVP 策略

真正实现：

- driver syntax/remove/meta update；
- `counterexamples_dependent_intros` 的 no-counterexample 路径（即 `remove_unused_from_context`），不能当 no-op；
- `inline_trivial`；
- `eliminate_builtin`；
- `remove_unused_keep_constants`；
- `detect_polymorphism`；
- `eliminate_definition_conditionally` 的首版所需分支；
- `simplify_formula`。
- `discriminate_if_poly`；
- 当前 closure/fixture 所需的 `eliminate_algebraic_if_poly` 窄分支；
- `monomorphise_goal`；
- `select_kept`/`keep_field_types`、`twin`、默认 `guards`；
- `encoding_smt_if_poly`。

多态路径必须逐函数复刻 Why3 1.7.2 的决定与结构，不能以“最终已单态化”等价替代。每个上述阶段都有 instrumented checkpoint；oracle 在 raw Task 导出后为后来生成的 symbol 写入 `OriginKind.Generated(stage)`，MoonBit 在创建时写入相同 stage。printer 前的 checkpoint 必须证明没有 residual type variable。

其他 slot 不可简单删除。feature scan 按 pipeline 阶段运行，而不是对 raw Task 一次性全局拒绝：

1. raw 阶段只拒绝用户声明产生的 unsupported；允许受支持的用户纯逻辑多态、带 trusted-origin 标记的 snapshot `Ddata` 和 BuiltIn 多态 equality；
2. driver update 后验证 syntax/remove/meta 均已解析；
3. 每个 transform 前验证其前置条件，后验证应消除结构；
4. 只有证明该阶段 Task 不含对应结构时，slot 才可作为带 assertion 的 no-op；
5. printer 前拒绝残余 type variable、epsilon 以及非 manifest allowlist/未编码 datatype；trusted monomorphic Tuple0/Unit `Ddata` 是唯一可进入 M6 datatype printer 的例外。

这样 Bool/Unit snapshot 的 datatype 以及前序 transform 尚未处理的 type variable 不会被过早误杀，用户 datatype 仍在 elaboration 阶段 fail closed。

#### 逐 transform reference checkpoint

上游公开的 `Driver.prepare_task` 只返回整个 pipeline 的最终结果；`Driver.update_task` 及每次 `Trans.apply` 的中间值不能从稳定 API 取得。因此测试基线必须包含：

```text
tools/why3_oracle/patches/driver-trace.patch
```

这个小 patch 只应用到固定的 Why3 1.7.2 oracle build，在 `update_task` 后和每次 transform 后调用只读 trace callback，输出 transform id 与 canonical Task；不进入 MoonBit 运行时，也不改变待证明 Task。patch 的 SHA-256、目标 Why3 commit 和 checkpoint 顺序都纳入 M0 lock。

如果该 instrumentation 尚未落地，强差分 gate 只能声称覆盖 raw Task 与最终 prepared Task；MoonBit 内部逐步 snapshot 此时只是单元测试，不能写成“与原版逐步一致”。

#### 退出条件

- 同一个 `Z3StaticSpec` 可分别绑定两个 context；各自 symbol 均来自对应 `FrozenEnvironment.DriverSymbolCatalog`，交叉使用返回 `ContextMismatch`。
- 每一步 transform 前后都能输出 canonical task。
- 与已锁定、带 trace patch 的 oracle 逐 checkpoint 一致，并与 `Driver.prepare_task` 最终结果一致。
- goal-last invariant 每步保持。
- `detect_polymorphism`、`discriminate_if_poly`、必要的 `eliminate_algebraic_if_poly`、`monomorphise_goal`、`select_kept/keep_field_types`、`twin`、默认 `guards`、`encoding_smt_if_poly` 均有 exact checkpoint fixture。
- residual type variable、epsilon、用户 datatype 与非 allowlist datatype 一定在 printer 前失败；仅已绑定同 context、hash 校验通过的 Tuple0/Unit snapshot `Ddata` 可继续。

### M6：SMT-LIB 2.6 printer

参考原版：

```text
../why3/src/printer/smtv2.ml
../why3/drivers/smt-libv2.gen
```

#### 实现项

- 输出缓冲使用 byte-oriented `@buffer.Buffer`，最终产物为 `Bytes`。
- 确定性 identifier allocator；SMT 保留字黑名单；同名冲突处理；每个 printed identifier 携带 User/Snapshot/Generated(stage) provenance 供 token normalizer 使用。
- 内建 syntax mapping：Bool/Int/Real、equality、算术和比较。
- 单态无解释 sort：`declare-sort`。
- trusted snapshot 中仍存活的单态 nullary datatype（MVP 必需的 Tuple0/Unit shape）按 Why3 SMT-LIB 2.6 的 `declare-datatypes` 形式精确输出；只接受 manifest allowlist 中的 constructor/schema。Bool 继续走 driver syntax `Bool/true/false`，用户 datatype 和其他 algebraic shape 仍拒绝。
- symbol：`declare-fun`、非递归 `define-fun`。
- term/formula：应用、逻辑联结、`let`、`ite`、量词和 `:pattern`。
- axiom：`(assert ...)`。
- goal：

```smt2
(assert (not <goal>))
(check-sat)
```

- 按 Task 从旧到新输出，不用 lookup Map 的遍历顺序。
- `eliminate_projections_sums`、`eliminate_algebraic_if_poly` 等 slot 必须通过 instrumented oracle 证明对 allowlisted monomorphic Tuple0/Unit shape 的实际行为；若非 identity，就实现该窄分支，不能用 asserted no-op 掩盖。printer 最后防线拒绝自由类型变量、epsilon、inductive、非 allowlisted/未编码 datatype、range/float 和无 syntax 的 builtin。

#### SMT 比较

- 使用真正的 SMT lexer 删除注释和规范空白，不能用简单正则破坏 quoted symbol/string。
- 主 gate 是受限 alpha-normalized token 精确比较：用户名称和 snapshot 名称逐 token 保留；只有 provenance 为 `OriginKind.Generated(stage)` 的 identifier 才按 `(stage, token stream 首次出现)` 重新编号。
- declaration、assert、quantifier、pattern 和 command 顺序不排序。
- oracle 对 raw Task 之后首次出现的 generated symbol 标记相同 stage；若无法证明 generated provenance，默认按非 generated 名称 exact 比较。
- quoted symbol/string 的内容不得因 alpha pass 改写；生成名与用户名碰撞也只改 generated 一侧。

#### 退出条件

- 所有 SMT snapshot 在 all-target 上字节一致。
- 原版与 MoonBit token diff 通过。
- generated-name collision fixture 在两边仅通过受限 alpha normalization 对齐，用户/snapshot 拼写与全部顺序仍 exact。
- 至少一个真正使用 `unit` 的 fixture 与原版同样输出/处理 Tuple0 `declare-datatypes`，并由 Z3 解析。
- 生成的每个文件都能由固定 Z3 解析。

### M7：Z3 profile、结果 parser 与纯逻辑闭环 A

#### argv

首版静态 profile 对应 Why3 `z3_487`，默认参数保持确定性：

```text
z3
-smt2
-in
-T:<solver-seconds>            # time limit > 0 时才加入
sat.random_seed=42
nlsat.randomize=false
smt.random_seed=42
-st
```

Why3 1.7.2 探测出的原版命令使用临时文件 `%f`：

```text
z3 -smt2 -T:%t sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 -st %f
```

MoonBit runner 改用 `-in` 是明确记录的 transport divergence：它避免临时文件，但不宣称 argv 与 Why3 profile 字节相同。CLI `-t` 只接受 `0..86400` 的整数秒，默认 `10`；正值 `t` 生成完全相同的 Z3 `-T:<t>`，父进程 deadline 固定为 `4*t+1` 秒。`0` 不生成 `-T` 且不设置自动 parent deadline，但仍响应 task cancellation 并负责最终回收。oracle 必须同时跑原版 `%f` 命令和 MoonBit stdin 命令，并比较归一化 prover answer；生成的 SMT token 仍单独按受限 alpha exact 比较。

#### 结果类型

```text
Valid
Invalid
Unknown(reason)
Timeout
OutOfMemory
StepLimitExceeded
```

`Invalid` 先保留在结果协议中以避免未来 model/counterexample 阶段改动 versioned CLI schema；当前无 counterexample 的 Z3 profile 不产生该结果。`ProverResult` 只包含已成功 spawn、完成 I/O/reap 并匹配 profile 规则的上述 outcome。

结果映射：

| 输出/状态 | 结果 |
|---|---|
| `unsat` | `Valid` |
| `sat` | `Unknown("sat")` |
| `unknown` | `Unknown(normalized_reason)` |
| Z3 timeout pattern 或父进程 deadline | `Timeout` |
| Z3 OOM pattern | `OutOfMemory` |
| 已识别资源上限 | `StepLimitExceeded` |
| stdout/stderr 已匹配明确答案 | 先按 Why3 answer pattern 分类；父进程强制 timeout 可覆盖它 |
| 未匹配答案、非零未分类退出、signal、乱码或无法分类 | typed `ProcessError` 或 `MalformedProverOutput`，不构造 `ProverResult` |

通用 `z3_487` profile 没有把普通 stderr/非零退出映射为 prover outcome 的专用规则。结果 parser 是纯函数，先用 canned stdout/stderr/exit-status 单测，不依赖真实 Z3 制造边界状态，并用 Why3 oracle 锁定“已识别答案优先、进程状态兜底”的顺序；output-limit 是 runner error，在下一里程碑规定更高优先级。

#### 稳定的 result gate 边界

- Why3 `%f` 与 MoonBit `-in` 的真实 solver answer 强差分只用于能在宽裕 limit 内快速、确定结束的 `Valid/Unknown("sat")/Unknown(reason)` 目标；两边传同一个 Z3 内部 `-T`，父进程 deadline 只作更晚的回收保险。
- timeout/OOM/step-limit、signal、malformed output 和“答案后非零退出”的分类主要由共享 canned output/status vectors 验证 Why3 pattern precedence；不靠真实机器恰好在资源边界触发。
- parent-deadline、输出 cap、broken pipe 与 zombie 回收用可控 helper child process 做 runner integration；真实 Z3 timeout smoke 只断言有界结束、分类在允许集合且进程已回收，不与 `%f` oracle 要求逐次 answer 精确相同。
- 若未来要把 near-limit answer 升为强差分，必须先复刻 Why3 的 Unknown→Timeout/StepLimit heuristic，并把 CPU/wall/internal limit 与 platform 固定为新 profile；本 MVP 不做此声明。

#### 纯逻辑验收

```whyml
theory T
  use int.Int
  constant x : int
  axiom A : x = 1
  goal G : x + 1 = 2
end
```

到本里程碑应能从 Parser 一路生成 Z3 query。实际启动进程在 M8 完成。

### M8：native process runner 与 CLI 骨架

当前 `moonbitlang/async@0.20.2` 源码已确认 native target 提供：

```text
@process.spawn
@process.read_from_process
@process.write_to_process
@process.hard_cancel
Process::cancel / Process::wait
Reader::read_some(max_len=...)
@async.with_timeout
```

因此首选实现直接复用该 package，不新增 C FFI。`unimplemented.mbt` 是其他 target 的占位实现，`prover/native` 本身限制为 `+native`。

#### runner 流程

1. 默认 executable 在一次 `prove` invocation 开始时从 `PATH` 解析一次 `z3`；`--z3 PATH` 覆盖它。portable canonical command 只保存 profile/transport/limit 与 executable request，不包含 resolved absolute path 或实际 spawn argv；后两者只写 `resolved_context.json`。
2. runtime `CommandSpec` 以参数数组保存 executable request 和 argv，不保存 shell command；canonical encoder 不序列化 expanded argv，spawn 也不经过 shell。
3. 子进程继承调用者环境，但强制覆盖 `LC_ALL=C`；resolved executable、继承环境和实际 argv 只进入诊断记录。
4. 校验 executable/argument 不含 NUL；不做 shell escaping。
5. 建立 stdin、stdout、stderr 三组 pipe，在 task group 中 spawn Z3，使用 `hard_cancel()`。
6. 一个任务写完全部 SMT `Bytes` 后立即关闭 stdin；两个任务并发读取 stdout/stderr，逐块累加。
7. stdout 与 stderr 各自独立限制为 `2 MiB`。reader 必须允许检测“恰好已满后还有一个 byte”；任一路超限立即 hard-cancel、关闭全部 pipe、`wait` 回收并 raise `OutputLimitExceeded(stream, limit)`。
8. `OutputLimitExceeded` 优先于超限前已经识别的任何 solver answer；不得返回部分输出对应的 `Valid/Unknown`。
9. 正值 `t` 用 `4*t+1` 秒 parent deadline；`t=0` 不建立自动 deadline。deadline/cancellation 后 hard-cancel，随后必须 `wait`，不能遗留子进程。
10. 正常、超时、输出超限、写端 broken pipe 和 reader error 的所有路径都关闭 pipe 并回收 child。
11. 只有 spawn/I/O/exit/reap 均完成后才把 `RawProcessOutcome` 交给 `@z3.parse_result`；基础设施失败使用 typed `raise`。

不要直接使用无界 `collect_output` 作为正式实现。

只有在当前 async process API 经最小 spike 证明无法满足硬取消或有界 capture 时，才启动 C FFI fallback；启动前必须先读取 `moonbit-c-binding` skill，按其中的 ownership/native-stub 规则设计，并增加 ASan 验证。

#### CLI 骨架

```text
why3mbt check file.mlw [--json]
why3mbt task file.mlw [-T theory] [-G goal | --goal-index N] [--json | --canonical-json]
why3mbt emit-smt file.mlw [-T theory] [-G goal | --goal-index N] [-o DIR] [--json | --canonical-json]
why3mbt prove file.mlw [-T theory] [-G goal | --goal-index N] [-P z3] [--z3 PATH] [-t 0..86400] [--json | --canonical-json]
```

子命令语义固定：`check` 只 parse/elaborate，不生成 Task 或启动 transform；`task` 生成 raw Task；`emit-smt` 执行 profile bind、prepare 和 print；`prove` 按源码 goal 顺序串行运行 Z3。默认输出是稳定的人类摘要；`--json` 每个 source goal 输出一条 versioned NDJSON（`check` 从 typed declaration inventory 取 goal metadata）；`--canonical-json` 输出该阶段完整 canonical debug record。

`emit-smt` 输出 stdout 时必须恰好选择一个 goal。选择到多个 goal 时必须给 `-o DIR`；文件名固定为 `<six-digit-zero-based-ordinal>-<lowercase-hex-goal-name>.smt2`，例如 ordinal 0 为 `000000-<hex>.smt2`。goal name 直接对原始 `Bytes` 做 lowercase hex，不要求 UTF-8。

输入固定为单个 `.mlw`、同文件 unit 和内置 snapshot。任何外部 loadpath 选项返回 `UnsupportedFeature(ExternalLoadpath)`。CLI 收到无法表示为 UTF-8 的文件路径时返回 `ConfigError(NonUtf8Path)`；非 UTF-8 goal name 仍可用 `--goal-index` 选择。

退出码固定为三值协议：

```text
0  所有目标 Valid
1  parse/type/config/unsupported/internal/process/output-limit/malformed error
2  至少一个已分类 outcome 为 Unknown/Timeout/OutOfMemory/StepLimitExceeded
```

#### 退出条件

- 纯逻辑闭环 A 在真实 Z3 上完成。
- `goal true` 为 Valid；`goal false` 为 `Unknown("sat")`。
- timeout 后子进程已回收。
- stdout/stderr 各 2 MiB cap、答案后超限、broken pipe、solver 不存在、非零退出和 malformed output 的 error kind/退出码稳定。
- 默认 10 秒、`-t 0` 无自动 deadline、正值 `4*t+1` parent deadline 都有可控 helper test。
- 单 goal stdout、多 goal directory、六位 ordinal/hex filename、goal-index、三值退出码和 NDJSON schema 均通过 CLI integration。

### M9：最小 Typed Program IR 与 elaborator

参考原版：

```text
../why3/src/mlw/ity.ml
../why3/src/mlw/expr.ml
../why3/src/mlw/pdecl.ml
../why3/src/mlw/pmodule.ml
../why3/src/mlw/dexpr.ml
../why3/src/parser/typing.ml
```

#### 实现项

- 在 M3 已为 stdlib Pmodule snapshot 建立的 `Ity/Cty/RoutineSymbol/Pmodule` 外壳上扩展用户 program declaration，不能另建第二套符号或 namespace。
- 完成 `Ity` 与 core `Ty` 的映射，以及用户 `ProgramVar` 创建。
- `Effect` 在 M3 已存在；MVP 只有可验证的 `Pure`，遇到写、raise、ghost/region 等立即 unsupported。
- 用户 `Cty` 复用 snapshot routine 的同一表示：args、result、pre、post、effect；用户 routine 在 finalize 时必须单态，任一泛化/残余 type variable 返回精确 `TypeError`/`UnsupportedFeature`。
- `Ity/Cty/Expr` 覆盖 Bool/Int/Real/Unit 参数、结果与常量，并覆盖 Int/Real 算术和比较。`real.Real` 运算必须从 Pmodule namespace 解析到 snapshot 中精确 `RoutineSymbol/Cty/rs_logic`，不能按操作符拼写特判。
- trusted stdlib polymorphic routine 允许按调用点实例化为单态 argument/result；此规则不允许用户声明 polymorphic routine。
- typed Expr：

```text
Evar
Econst
EpureApp
EroutineCall
Elet
Eif
Eassert
Eassume
```

- `Pdecl` 和 `Pmodule`，其中 module 同时维护 pure Theory 投影。
- spec 两阶段 elaboration：
  - 参数类型确定后检查 `requires`；
  - result 类型和 symbol 确定后检查 `ensures`；
  - 用 `PendingSpec` 保存 Ptree 和作用域快照，不能在类型未知时提前定型。
- 仅支持非递归、普通 `RLnone` 顶层 `let` routine；简单 result binder/wildcard；普通 `val` 抽象 routine contract。
- `let function`/`val function` 在 feature classification 立即返回 unsupported；首版不实现 `Pdecl.create_let_decl` 的 pure `Dlogic/Dparam/'spec/'def` projection。
- routine call 检查参数类型和 callee pre/post。

#### 测试

- 参数和 result shadowing；
- requires 必须为 formula；
- ensures 中 result 类型；
- function body/result 类型不一致；
- if 两分支类型不一致；
- routine call arity/type；
- Real 参数、Real 结果、精确实数常量、算术、比较、requires/ensures、routine call；
- 用户 polymorphic routine 被拒绝，而 trusted stdlib polymorphic routine 的两个不同单态实例可用；
- parser 接受的 loop/recursion/mutation/exception 均得到精确 UnsupportedFeature。

#### 退出条件

- MVP program fixture 的 type-only 接受/拒绝与 Why3 对齐。
- typed routine 的 args/result/pre/post canonical dump 与 oracle 对齐。
- Program Real fixture 的 `RoutineSymbol/Cty/rs_logic`、typed Expr 与 typed Pmodule exact gate 对齐。

### M10：Kode 与 classical WP

参考原版：

```text
../why3/src/mlw/vc.ml
../why3/src/mlw/pmodule.ml
```

#### Kode 子集

```text
Kseq
Kpar
Kif
Klet
Kval
Kcut
Kstop
Kcont
```

保留 Kode 层，避免把表达式遍历和公式拼接写成一个以后无法扩展的函数。首版 `Kcont` 只允许 `Kcont 0`；任何其他 continuation depth 都是内部 invariant failure。首版不实现 `Ktag`、`Khavoc`、异常 continuation、用户选择的通用 SP optimization 和 type invariant injection；但必须复刻 Why3 1.7.2 默认 VC 路径对纯 `if` 分支自动执行的局部 pure-SP 组合，才能保持 raw VC/checkpoint 的结构与属性位置精确一致。该兼容路径不开放控制属性；在 lowering 前仍拒绝 `vc:sp`、`vc:wp` 等会选择额外路径的属性。

#### WP 规则

- 函数：`forall args. requires -> WP(body, ensures[result])`。
- value 与 `let x = e1 in e2`：固定复刻 Why3 1.7.2 的 `Klet`/`wp_let` 结构和 typed `let`，不允许以“等价 substitution”替代。
- `if c then e1 else e2`：固定复刻 `wp_if` 的节点形状、分支顺序和条件放置，不使用仅逻辑等价但结构不同的编码。
- `assert p`：证明 `p`，随后将 `p` 加入 continuation 假设。
- `assume p`：只加入 continuation 假设。
- routine call：
  - 证明 callee pre；
  - fresh result；
  - 假设 callee post；
  - 对任意满足 post 的 result 继续证明 caller continuation。
- 最终对自由变量做 `forall` closure。
- 生成 `PrSymbol` 名 `<routine>'vc`，保留 explanation 和 source location attributes。
- 复刻 Why3 的 propositional smart simplification，以及 `stop_split`、`expl:*`、source/model 属性的准确附着节点；canonical gate 比较属性位置而非只比较集合。
- 复刻 `add_vc_decl` 的 structurally-trivial VC suppression：被原版直接丢弃的 VC 不得在 MoonBit 产生一个 `goal true`。
- `Pmodule.add_pdecl` 先将 VC `Pgoal` 加入 pure Theory，再保存 program declaration。

#### 退出条件

- `requires/ensures/let/if/assert/assume/call` 的 goal 数量、顺序、名称与 Why3 一致。
- full canonical raw Task 中 stdlib、用户声明和生成 VC 的结构/顺序/属性与 oracle 一致；Why3 runtime tag 与原生 checksum只作诊断。
- 每种 WP rule 都有 Kode、raw VC 和 prepared Task 三层 snapshot；不能用“Z3 同样返回 Valid”替代结构 gate。
- 故意翻转 postcondition 后不得返回 Valid。

### M11：完整闭环 B、CI 和发布门槛

#### 最终 CLI 流程

```text
parse
-> elaborate module
-> generate VC
-> split Theory
-> prepare with static Z3 profile
-> print SMT-LIB
-> run Z3 per goal
-> aggregate results
```

#### 完成条件

- 本文开头的 `abs` 示例返回 Valid。
- 至少一个带 routine call 的合约示例返回 Valid。
- false postcondition 返回非 Valid。
- parser 989 fixture 结果不回退。
- curated MVP corpus 的 typing、full canonical raw Task、prepared Task、SMT token 和 result 分层差分全部通过。
- unsupported corpus 没有任何输入静默进入 Z3。
- pure semantic packages 保持 all-target。
- runner/CLI native 测试通过。
- `moon info` 和 `moon fmt` 后工作区无 diff。

---

## 7. 原版 Why3 differential oracle

### 7.1 分层原则

每个 fixture 保存以下阶段：

```text
Ptree
typing outcome
typed Theory/Pmodule semantic projection
raw Task
Z3 prepared Task
SMT tokens
Z3 process result
```

typed semantic 以 unit 为记录与 hash 粒度；raw Task、每个 transform checkpoint、prepared Task 和 SMT token stream 以 goal 为记录与 hash 粒度。typed/raw/checkpoint/prepared 比较完整 canonical JSON bytes，SMT 比较受限 alpha-normalized token bytes；共同使用 canonical bytes 的 SHA-256。solver result 是最后一层，不是主结构 oracle。

最终 PR corpus 将每条记录的完整 canonical JSON、完整 SMT normalized token stream 及各自 hash checked in；不能只提交 hash。nightly 全量内容不进入 git，只保存为 CI artifact，summary 中保留 hash 与 diff 索引。

### 7.2 CLI 冒烟命令

所有 Why3 CLI、OCaml oracle、stdlib exporter 和 result oracle 必须读取同一组分层 manifest：

- `semantic_profile_sha256` 只覆盖 portable canonical schema、snapshot manifest、driver/static-profile manifest、transform/checkpoint manifest 和 feature manifest；不覆盖工具安装、机器、绝对路径或 argv。
- `OracleContext` 额外固定 Why3 executable content hash/version/commit、OCI image digest/platform、`LC_ALL=C`、禁用默认插件、`--no-stdlib`、stdlib tree hash、fixture 专属且有序的 repo-relative loadpath + tree hash、driver closure 相对名 + content hash、prover-detection-data hash、Whyconf recipe，以及 Z3 version/content hash；其 hash 为 `oracle_context_sha256`。
- 公共 `CanonicalGoalRecord` 只携带 portable schema/profile/source/unit/goal/stage/content/hash，不含 `oracle_context_sha256` 或机器环境。Why3 测试包装层使用独立 `OracleGoalEnvelope { record, oracle_context_sha256 }`。

wrapper 每次另写完全不参与 semantic golden 的 `resolved_context.json`，记录绝对 executable/loadpath/datadir、实际 argv、继承/覆盖环境、生成后 `whyconf_sha256` 和 driver 实际解析路径。这样同一 semantic profile 在两个临时绝对根产生的公共 records 必须逐字节相同，oracle envelope 也应因固定 context 相同，而诊断 artifact 仍能追溯真实进程。

Why3 `-P` 会从 datadir 解析配置中的 driver basename，所以 OracleContext 固定唯一 `why3 --print-datadir` 内容树；wrapper 在运行前把 `z3_487` 解析为该 datadir 下的绝对文件，递归校验 closure hash。不得退回另一套系统 stdlib、默认 `~/.why3.conf` 或未校验的 datadir。

`tools/why3_oracle/run-fixed <fixture-id> -- ...` 是唯一 CLI 入口。它从 fixture manifest 解析并校验绝对路径，然后等价地统一加上：

```bash
LC_ALL=C why3 \
  --no-load-default-plugins \
  --no-stdlib \
  -L /absolute/pinned/why3-1.7.2/stdlib \
  -L /absolute/fixture/specific/loadpath \
  -C /absolute/fresh/oracle/why3.conf \
  ...
```

下面的命令都通过该 wrapper；显式 `-D` 示例使用 manifest 解析出的绝对路径。只有 `-P` 路径允许 Whyconf 保存 basename，但其唯一 datadir 与最终 resolved closure 必须先校验并记录。

解析与类型：

```bash
tools/why3_oracle/run-fixed fixture-id -- prove --parse-only input.mlw
tools/why3_oracle/run-fixed fixture-id -- prove --type-only input.mlw
```

namespace/theory：

```bash
tools/why3_oracle/run-fixed fixture-id -- \
  prove --print-namespace input.mlw -T Module

tools/why3_oracle/run-fixed fixture-id -- \
  prove --print-theory input.mlw -T Module
```

session goal inventory：

```bash
oracle_dir=$(mktemp -d)
tools/why3_oracle/run-fixed fixture-id -- \
  session create -o "$oracle_dir/session" input.mlw
```

`why3.drv` prepared/pretty-print 冒烟输出：

```bash
mkdir -p "$oracle_dir/pretty"
tools/why3_oracle/run-fixed fixture-id -- prove \
  -D /absolute/pinned/drivers/why3.drv \
  -o "$oracle_dir/pretty" \
  input.mlw -T Module -G Goal
```

`Driver.print_task` 即使使用 `-D why3` 也会先执行 driver update/prepare，所以这不是 raw Task。真正的 raw Task 只能由 7.3 的自定义 oracle 在 `Task.split_theory` 之后、调用任何 driver 之前导出。

Z3 prepared SMT：

```bash
mkdir -p "$oracle_dir/smt"
tools/why3_oracle/run-fixed fixture-id -- prove \
  -D /absolute/pinned/drivers/z3_487.drv \
  -o "$oracle_dir/smt" \
  input.mlw -T Module -G Goal
```

注意：

- `-o` 不创建目录。
- `--type-only` 会在 VC 前返回，不能与 `--print-theory` 组合期待 typed/VC 输出。
- 类型错误即使使用 `--json` 也可能是普通 stderr。
- 多 goal `--json` 是连续 JSON 值，不是数组；正式测试逐 goal 调用。
- 输入文件要在 `-T/-G` selector 之前出现，避免 CLI 歧义。
- wrapper 启动前校验 OracleContext 全部稳定 hash，退出 artifact 中记录 resolved argv/loadpath/datadir/driver closure；任何 CLI 或 OCaml oracle 都不得绕过它的等价配置构造器。

### 7.3 测试专用 OCaml oracle

CLI 无法稳定导出 typed Pmodule 和每一步 prepared Task。实现一个只用于测试的 Why3 1.7.2 OCaml executable，并把 typed 与 VC 分成两个独立进程/模式：

```text
typing mode（fresh process）:
  Debug.set_flag Typing.debug_type_only
  Env.read_file Pmodule.mlw_language
  Pmodule.mod_units
  导出 typed Pmodule projection 后退出

vc mode（另一个 fresh process，不设置 debug_type_only）:
  Env.read_file Pmodule.mlw_language
  Pmodule.mod_units / Pmodule.mod_theory
  Task.split_theory
  立即导出 raw Task
  Termcode.task_checksum
  Driver.prepare_task
  Driver.print_task_prepared
```

默认的 `Env.read_file Pmodule.mlw_language` 会继续生成 VC，不等价于 CLI `--type-only`。使用两个 fresh process 可避免全局 debug flag 和 Why3 环境/cache 污染另一条路径。M5 的带 patch oracle build 还要在 `update_task` 后及每次 transform 后导出 checkpoint；未应用 patch 时只导出最终 prepared Task。

两个模式都必须由 7.2 的 `OracleContext` 构造 `Env`：同一个 pinned stdlib 内容、同序 fixture loadpaths、相同 format 注册和已验证 datadir/driver closure；不允许 helper 内部另建默认 `Env.create_env`。portable `CanonicalGoalRecord` 不写 oracle 环境；oracle 输出用 `OracleGoalEnvelope` 在 record 外层附加稳定 `oracle_context_sha256`，resolved absolute paths/argv 只进旁路 artifact。

#### 隔离的 prover-result oracle

每个 fixture 的每个 goal 都用临时配置和精确 prover selector 单独执行：

```bash
oracle_dir=$(mktemp -d)
cfg="$oracle_dir/why3.conf"
tools/why3_oracle/run-fixed fixture-id --config "$cfg" -- config detect
# wrapper 随后重读配置，断言选中 entry 的 driver basename 为 z3_487，
# 在唯一已验证 datadir 中解析它，并校验 command/version/alternative/executable/closure
tools/why3_oracle/run-fixed fixture-id --config "$cfg" -- prove \
  -P 'Z3,4.8.12,' \
  -t 2 \
  --json \
  input.mlw -T Module -G Goal
```

`share/provers-detection-data.conf` 的 SHA-256 已在 M0 锁定；检测后的实际 executable、version、alternative 和 command template 写入 `resolved_context.json`。因为 Whyconf 自动检测写入 driver basename，wrapper 必须在已锁定的唯一 datadir 中解析它并校验整个 import closure；不能依赖未验证安装目录中“恰好同名”的 driver。`config detect` 前后 `oracle_context_sha256` 不变，生成配置内容另记 `whyconf_sha256`。不要复用开发者的 `~/.why3.conf`，不要用宽松的 `-P z3`，不要在一次 `--json` 调用里混入多个 goal。原版结果 oracle 走检测出的 `%f` 命令；MoonBit runner 走 `-in`，两者共享同一个 Z3 4.8.12 executable；只有 M7 定义的快速决定性目标做真实 answer 强差分，资源边界不做时序敏感的 exact gate。

oracle 的核心调用链为：

```text
typing projection（type-only process）
raw Task（VC process，split 后、driver 前）
instrumented update/transform checkpoints
final Driver.prepare_task
Driver.print_task_prepared
```

typed semantic 每个 unit 输出一条 canonical record；raw/checkpoint/prepared/SMT/result 每个 goal 各输出一条。下面是 oracle envelope 的简化示例，`record` 部分必须能从 envelope 中原样抽出并与 MoonBit 公共输出逐字节比较：

```json
{
  "oracle_context_sha256": "...",
  "record": {
    "schema": 2,
    "semantic_profile_sha256": "...",
    "fixture": "mvp/abs.mlw",
    "source_sha256": "...",
    "scope": "goal",
    "unit": "Abs",
    "goal_name_hex": "616273277663",
    "goal_ordinal": 0,
    "stage": "raw-task",
    "canonical_sha256": "...",
    "canonical": {}
  },
  "reference_diagnostics": {
    "why3_task_checksum_v6": "..."
  }
}
```

Why3 1.7.2 的 `Termcode` shape version 是 6。原生 checksum 适合快速检测 reference 漂移，但不能单独作为 gate，因为它不是完整语义哈希，且不会完整覆盖名称、location、attributes、range/float 参数等信息。MVP 不移植 OCaml `Termcode`：`why3_*_checksum_v6` 只存在于 oracle envelope 的 `reference_diagnostics`，不进入公共 `CanonicalGoalRecord`，比较器不跨实现比较它。

每个 Task 同时保存：

1. Why3 reference-only 的原生 `task_checksum_v6`；
2. 完整 canonical semantic JSON 的 SHA-256；
3. name/location/attributes projection。

#### 冻结 semantic stdlib snapshot 的 gate

首版不实现通用 `clone`，但 exporter 从固定 Why3 1.7.2 导出 `z3_487.drv` recursive imports 引用的全部 pure Theory 与传递 `use/clone` closure，并导出用户可见 `BuiltIn/Bool/Unit/int.Int/real.Real` 的 Pmodule program exports。因此：

- Why3 原生 `task_checksum_v6` 仍保存为诊断数据；runtime tag/id 差异不作为失败依据；
- full raw Task 的强 gate 是完整 canonical semantic JSON，包括 snapshot 声明、用户声明、生成 VC、goal inventory、meta/attributes 和顺序；
- typed Pmodule gate 还精确比较 exported program namespace、RoutineSymbol/Cty/rs_logic；这是 `use int.Int` 在程序表达式中可用的前提；
- snapshot/catalog gate 精确比较全部隐藏 BV/float/map/string 等 driver-only theory key、item/inner ordinal、symbol kind/digest；它们不进入用户 resolver；
- snapshot 中的 trusted `Ddata` 可以进入 raw Task，但用户 datatype 仍然 unsupported；
- prepared Task canonical semantic JSON 与 SMT token 必须精确相等；
- 任一差异都回溯到 snapshot、driver update 或 transform/VC checkpoint 修复，不能改成只比较用户/VC projection。

以后实现通用 `clone` 时，以同一 snapshot corpus 作为替换验收，不能改变这些 gate。

### 7.4 canonicalization

MoonBit 侧由 all-target `oracle/canonical` 实现唯一 canonicalizer 和 SHA-256；它不是 `_test.mbt` 私有 helper。native `cmd/why3 --canonical-json` 调用纯 `pipeline` 取得 typed/raw/checkpoint/prepared/query 值，再输出 versioned portable records。CI 通过该 executable 消费真实 package 边界，禁止 Node 脚本复制 canonicalization、SMT normalization 或 hashing 逻辑；Node 只负责排序 fixture、校验 schema/已给出的 hash 和 diff。

Typed IR/Task 的唯一遍历协议由 versioned `oracle/canonical/schema.mbt` 与 OCaml 镜像共同冻结：从顶层 ordered units、Theory items、Task declarations 到 node fields 做 preorder；每种 node 先输出 tag，再严格按 schema 列出的字段顺序访问，Array 按 index，语义无序 Map 按 canonical Bytes key 排序，`None` 也输出固定 sentinel。新增/调换字段必须升级 schema，不能依赖语言 record/Map 的运行时遍历顺序。

序列化格式固定为无多余空白的 UTF-8 JSON、schema 字段顺序和 `\n` 行结束；hash 输入是这组精确 bytes。typed content 每 unit 一条，raw/checkpoint/prepared/SMT content 每 goal 每 stage 一条；禁止 pretty-printer、平台换行或浮点 formatter 参与 hash。

`semantic_profile_sha256` 只覆盖 portable schema、snapshot、driver、transform/checkpoint 与 feature manifests。`CanonicalGoalRecord`/typed-unit record 不含机器环境；`oracle_context_sha256` 只由测试侧 `OracleGoalEnvelope` 添加。绝对路径、resolved executable 和实际 argv 永远只进入 `resolved_context.json`。

`oracle/canonical/sha256.mbt` 提供 all-target SHA-256，canonical hash 一律调用它；必须用标准 single-block/multi-block vectors 和跨 target vectors 测试。Node 不得成为 hash 真源。

- global type/logic/program/region/prop symbol 一律在上述 preorder 的第一次 encounter 分配 `(symbol-kind, next-index)`；声明、引用、meta 和 clone witness 一视同仁，不再存在“按声明或首次出现”两种策略；
- bound variable 使用 de Bruijn index；
- 不输出 Why3 `id_tag`、物理地址、hash-cons 身份和表达式运行时 tag；
- 输出 symbol 的 `OriginKind`，并对 `Generated` 输出稳定 stage enum；绝不输出 context token；
- map/namespace 按 canonical Bytes key 排序，key 相同的复合项再按 schema 字段逐级比较；
- 所有 semantic `Bytes`（名称、attribute、路径片段）用 lowercase hex 编码，不先假设 UTF-8；可读 UTF-8 只放不参与 hash 的 pretty 字段。Map 统一编码为有序 entry array，不依赖 JSON object key 规则；
- declaration、task、trigger、argument 顺序保留；
- Theory/Task 的 `Use/CloneWitness/Meta` 作为正式 node 输出；clone witness 包含 source TheoryKey 和按 schema 固定顺序遍历的 instantiation map，不能只输出展开后的 Decl；
- ordinary attributes 按 Bytes 完整保留并排序；控制属性是否允许由 feature manifest 决定，`stop_split`、`expl:*`、VC/model 属性的存在与附着节点进入 exact gate；
- 整数和有理数用精确字符串；
- path 转为 fixture-root 相对 POSIX path；
- semantic、metadata、pretty text 分字段。

先用手工构造的 cross-language schema vectors 锁定 first-encounter 编号、每个 node 字段顺序、Map tie-break、optional 和 clone witness；MoonBit 与 OCaml canonical JSON 必须逐字节一致后，Task SHA 才能成为 gate。

SMT：

- 通过 lexer 删除 comment 和规范空白；
- 保留 quoted symbol/string 的 token 内容；
- 保留 command/declaration/assert/pattern 顺序；
- 用户与 snapshot 符号名精确保留；
- 只有 `OriginKind.Generated(stage)` 的 identifier 才按 `(stage, normalized token stream 首次出现)` alpha-renumber；oracle 对 raw Task 后产生的 symbol 做同样标记；
- 受限 alpha-normalized token stream 是主 gate，不再另设可放宽用户名称或排序的辅助等价 gate。

结果：

- 比较 answer enum 和 normalized reason category；
- 不比较 elapsed time、内存、精确 step、绝对路径；
- 单独保存 raw stdout/stderr 供失败诊断。

---

## 8. Fixture 与测试矩阵

### 8.1 现有语料

- Parser：989 个完整 fixture，继续保持 929 exact / 58 reject / 2 extension。
- Typing good：优先从 `bench/typing/good`、`bench/programs/good`、`stdlib` 选取。
- Typing reject：优先从 `bench/typing/bad`、`bench/programs/bad-typing` 选取。
- Solver：从 `bench/valid`、`bench/invalid` 中只启用落在 MVP feature set 的目标。

不要把所有 fixture 目录同时加入 `-L`，否则会引入库路径歧义。manifest 为每个 fixture 单独记录 loadpaths。

### 8.2 MVP curated corpus

最终 PR gate 的 corpus 不再用数量范围描述。唯一权威清单是阶段 00 checked-in 的 `tools/contracts/pr-corpus-v1.json`：它逐项枚举 fixture path、source hash、unit、goal ordinal/name bytes、feature tags、expected stage/kind/lane，并以 manifest SHA-256 冻结。下列每一类必须由该清单中的具名 entry 覆盖；阶段 00 未填满并核对清单前不得开始依赖 corpus 的后续实现阶段：

- ID、shadowing、qualified lookup；
- unify、occurs check、arity/type mismatch；
- function/predicate/formula/value 区分；
- Bool/Int/Real；
- 参数化 abstract/alias type、同一 polymorphic symbol 的多个实例、自由类型变量 goal；
- 无解释 sort/function/predicate；
- `let/if/forall/exists/trigger`；
- axiom/lemma/goal 和 goal inventory；
- `use`、`use import`、scope；
- `requires/ensures`、result、assert、assume、routine call；
- raw VC；
- 每个已实现 transform；
- `detect_polymorphism`、`discriminate_if_poly`、必要的 `eliminate_algebraic_if_poly`、`monomorphise_goal`、`select_kept/keep_field_types`、`twin`、默认 `guards`、`encoding_smt_if_poly` 的各 checkpoint；
- SMT generated/user identifier collision、reserved word、goal 取反，以及“只可重编号 generated 名称”的反例；
- 全部 driver catalog key 的 bind inventory；用户 `use` 隐藏 BV/float/map/string 的精确 `DriverOnlyTheory` 拒绝；trusted Range/Float/String/Ddata 跨 target canonical；
- Program Real 参数、结果、常量、算术、比较、requires/ensures、routine call 和 false postcondition；
- portable profile hash 与 oracle context 分离、两个绝对根的公共 record 完全相同；
- 快速确定的真实 `unsat`、`sat -> Unknown`、`unknown`；timeout/OOM/step/signal/异常退出使用 canned parser vectors 与可控 runner helper，另留非 exact 的 Z3 timeout smoke；
- runner/CLI 的默认 10 秒、`0` 无自动 deadline、stdout/stderr 双 2 MiB cap、答案后超限、broken pipe、timeout/reap、单目标 stdout、多目标目录、三值退出码和 versioned NDJSON；
- 每个 unsupported feature 的精确拒绝阶段。

### 8.3 Mutation/metamorphic tests

对可证明 fixture 自动产生：

- 翻转 postcondition；
- 删除必要 axiom；
- 改变函数参数类型；
- 交换 implication 方向；
- 删除 if 分支条件；
- 重命名 bound variable；
- 加入无关 declaration；
- 改变绝对 fixture root。

目的：发现 binder capture、result substitution、分支条件、goal 忘记取反和 canonicalization 路径泄漏。

---

## 9. CI 与 golden 更新

### 9.1 最终 PR gate

阶段 00 至阶段 12 全部完成并通过各自本地 gate 后，才创建唯一最终 PR；以下检查全部作用于该最终 PR，不作为中间阶段开 PR 的理由。

1. 现有 `moon check --target all --warn-list +73`。
2. all-target unit tests。
3. 989 parser corpus。
4. curated typing accept/reject。
5. typed semantic 每 unit 的完整 canonical JSON + SHA-256 exact。
6. raw Task 每 goal 的原生 checksum 诊断 + 完整 canonical JSON/SHA-256 exact。
7. 每个 transform checkpoint 与 prepared Task 每 goal 的完整 canonical JSON/SHA-256 exact。
8. 每 goal 的受限 alpha-normalized SMT token stream 完整内容 + SHA-256 exact。
9. 少量快速确定的 Z3 native answer integration + 可控 helper 的 timeout/cap/reap integration。
10. 对 invalid corpus要求“绝不返回 Valid”。
11. `moon info`、`moon fmt` 后无 diff。

### 9.2 Nightly gate

- 全部 typing good/bad；
- 全部当前 supported fixture；
- typed/raw/逐 checkpoint/prepared Task/SMT 全量差分；
- 按 goal 分片和资源限额执行 solver；near-limit 结果只做稳定性观测/允许集合，不更新 exact answer golden；
- 完整 canonical JSON/token 内容只保存为 CI artifact；仓库不提交 nightly 全量内容。artifact 同时保存 Why3/MoonBit raw task、checkpoint、prepared task、SMT、stdout/stderr。

### 9.3 CI 镜像

当前 Dockerfile 只安装 Why3，没有安装 Z3。阶段 00 先冻结 `linux/amd64` oracle image contract；加入强 gate 前必须：

- oracle 镜像显式安装固定 Z3 4.8.12，但不安装 MoonBit；CI 用 `setup-moonbit` 的 `stable` channel 安装 MoonBit，并用 `moon update && moon check` 初始化 registry、解析精确版本依赖，再校验 async dependency closure manifest；
- 测试开始时断言 `z3 --version`；
- 记录并校验 Z3/Why3 二进制 SHA-256；MoonBit 只记录 CI 实际版本用于诊断，不校验版本或二进制 SHA-256；
- 保持 Why3 1.7.2 和 driver closure hash；
- 最终 PR oracle job 的 image reference 直接写入与 `toolchain-lock.json` 相同的 64-hex immutable digest，不使用变量占位或可移动 tag；所有 action 直接使用 lock 中的 full commit SHA；
- 普通 CI 的 MoonBit setup 明确使用 `version: stable`；所有 action 仍使用 full commit SHA，且不出现 `uses: ...@main`。`moon update && moon check` 只用于 fresh runner 的 registry/bootstrap，并必须紧接 dependency manifest 校验；依赖版本或 golden 更新仍只能由显式 lock-update workflow 产生 candidate diff；
- native runner 测试单独运行，pure packages 继续 all-target。

### 9.4 Golden 更新协议

普通 CI 只比较，绝不更新。专用 `update-oracle`：

1. 校验 Why3 1.7.2。
2. 校验 fixture commit 和 inventory。
3. 校验 shape version 6。
4. 校验 driver import closure SHA-256。
5. 校验 Z3 version 和 binary SHA-256。
6. 校验 setup-moonbit action commit、async 0.20.2、OCI digest、其余 action commits、feature/corpus/schema/semantic-profile hashes；MoonBit 实际版本只写入诊断，不作为拒绝条件。
7. 输出到 candidate 目录。
8. 在两个不同临时绝对路径生成两次，portable canonical records/golden 必须相同；`resolved_context.json` 可含不同绝对路径，只校验其解析关系，不参与逐字节比较。
9. 展示结构化 diff。
10. 只有显式 `--promote` 才替换 golden。
11. normalizer schema 改变时创建新版本目录，不重解释旧 golden。

---

## 10. 单分支实施顺序、并行关系与最终 PR

阶段 00 至阶段 12 全部在同一个长期实现分支上连续完成。每个阶段可以整理为一个或多个边界清晰的原子 commit，并可持续 push 到同一远端分支以备份和运行非 PR 工作流；不得为中间阶段创建 PR，也不以合并中间分支作为下游阶段的前置条件。只有全部阶段、第 9 节中可在本地或非 PR 工作流执行的总体验证，以及第 13 节中不依赖最终 PR 的验收项均通过后，才整理完整 commit 历史并创建一个面向 `main` 的最终 PR；随后只用该 PR 运行 PR 专属 CI gate 和完成最终合并审查。

```text
阶段 00  license + feature/schema/oracle/toolchain locks + full driver/theory inventory
阶段 01  identity + OriginKind + canonical base encoding + all-target SHA-256
阶段 02  Ty/Dty + polymorphic unification/generalization + trusted Range/Float schema/canonical
阶段 03  Symbol/Term/Decl + string constants + trusted Ddata schema/canonical
阶段 04  OCaml snapshot exporter + recursive driver-closure exporter + candidate generated tables
阶段 05  Theory/Task + minimal MLW shell + FrozenEnvironment + snapshot loader/catalog + raw snapshot gate
阶段 06  pure-logic elaborator + user polymorphism + OCaml typed/raw differential harness
阶段 07  complete static Z3 profile + instrumented per-checkpoint transforms including polymorphic path
阶段 08  SMT-LIB printer + generated-name normalizer + token differential
阶段 09  result parser + native runner + CLI skeleton + pure-logic closure A
阶段 10  monomorphic program IR + Real routines/expressions + program elaborator
阶段 11  Kode/classical WP + VC differential
阶段 12  closure B + complete CLI + CI/golden hardening
```

可以并行：

- native runner spike 可独立并行；spike 不提交 identity/schema/profile 决策，也不改变正式 runner/CLI error protocol。其他阶段按上表依赖顺序推进，只有在其上游 schema 已在同一分支完成并通过对应 gate 后，才可拆分不共享文件的实现工作。

不能提前：

- 阶段 00 未完成时，阶段 01 及任何会固化 identity/snapshot/canonical schema 的后续阶段不得开始；
- Term smart constructors 未稳定前不能写 VC；
- Theory/Task 未稳定前不能写 transforms；
- feature scan 未完成前不能让 printer 接受任务；
- typed program IR 未完成前不能从 Ptree 直接生成 WP。

canonicalizer 从阶段 01 起随 IR 增量实现并为每个新增 variant 添加 cross-language vector；不得推迟到 raw Task differential 阶段。每个阶段在同一分支上对受影响 target 执行对应 `moon check/test`；阶段 12 最后执行完整 `moon info`、`moon fmt` 并要求再次运行后无 diff。所有最终 gate 通过后才创建唯一 PR。

---

## 11. 风险与决策记录

| 风险 | 处理 |
|---|---|
| 把 Parser Term 当 typed Term | 使用不同 package 和 opaque typed IR，禁止直接打印 Ptree |
| 名称相同或 local ID 跨 context 碰撞 | SemanticId 带 opaque context token；跨 context 组合显式拒绝，名称只用于显示 |
| Bool value 与 formula 混淆 | core 用 `Term::ty() -> Ty?` 强制区分；elaborator 显式生成 Why3 双向 coercion |
| 完整 driver closure 拖入 clone/datatype/range/float | 不实现 evaluator；由 trusted decoder 无损载入 `z3_487` 所需完整闭包，隐藏 catalog 与用户 resolver 分离，用户构造继续 fail closed |
| 删除插件时误删 driver 语义 | 保留静态 syntax/remove/meta/transform profile |
| 跳过未实现 transform 造成不可靠 SMT | feature scan + asserted no-op + fail closed |
| 无序容器导致 SMT 漂移 | 有序 Array 为真源，Map 只 lookup |
| 同一个 Z3 结果掩盖不同公式 | typed/task/SMT 结构 oracle 为主，solver 为辅 |
| process 输出死锁或无限增长 | 并发读取、显式 cap、hard cancel、wait 回收 |
| output cap 前已识别答案被误接受 | 任一路超过独立 2 MiB 时 `OutputLimitExceeded` 覆盖此前答案并确保回收 |
| async process API target 差异 | 只在 `prover/native` 使用；其他 package 不 import 它 |
| Why3 checksum 覆盖不完整 | checksum + canonical semantic SHA-256 + metadata projection |
| 错误 golden 被自动接受 | 普通 CI 禁止更新；candidate 双生成和人工 promote |
| 生成名归一化掩盖用户差异 | provenance 默认 exact；仅 `OriginKind.Generated(stage)` 可按首次出现 alpha-renumber，名称与顺序反例进入 corpus |
| 逐行翻译的许可义务 | 整仓固定 LGPL 2.1 + Why3 special linking exception；翻译块保留 Why3 copyright 与翻译/修改日期 |

---

## 12. 本计划之外的扩展顺序

完成闭环 B 后，按依赖顺序扩展：

1. recursion 与 variant；
2. loop invariant/variant；
3. pattern、datatype、record；
4. region、reference、assignment、havoc、old/at；
5. exception/xpost；
6. clone 和 module interface；
7. 用户 polymorphic datatype、完整 algebraic encoding 与超出 MVP 窄路径的多态；
8. 用户可见 range/float/bitvector/map/string；
9. counterexample/model；
10. CVC5 静态 profile；
11. 其他现有 prover profile。

CVC5 应复用 `core`、Task、transform、SMT-LIB printer、`prover/native` 和 result protocol，只增加静态 profile/命令/结果规则，不引入插件系统。

---

## 13. 最终验收清单

- [ ] 整仓目标许可为 LGPL 2.1，并原样附带 Why3 special linking exception；根 metadata/NOTICE 一致，翻译块 attribution/date 完整。
- [ ] 阶段 00 至阶段 12 均在同一长期实现分支完成；中间阶段未创建 PR，且仅在全部最终 gate 通过后创建一个面向 `main` 的最终 PR。
- [ ] Linux x86_64 OCI digest、action commits、async 0.20.2、Why3 commit、完整 driver/theory closure、prover detection、snapshot、Z3 4.8.12 和全部相关 hash 已锁定；MoonBit 由 setup-moonbit stable 提供且明确不进入 oracle lock。
- [ ] feature manifest 穷尽 Ptree variants/形态/拒绝阶段/error kind/fixture/lane；最终 PR corpus 是具名、hash 锁定的完整 inventory。
- [ ] 989 parser corpus 无回退。
- [ ] typed core 只能通过 smart constructors 构造。
- [ ] names 使用 Bytes，semantic equality 使用带 context token 的 SemanticId，跨 context 混用被拒绝。
- [ ] context token 是 fresh opaque reference，local ID 为 Int64，equality/hash/canonical 与单线程 builder 契约均有测试。
- [ ] formula/value core 区分与 elaborator 双向 coercion、arity、类型和 capture 不变量都有单测。
- [ ] 用户纯逻辑支持参数化 abstract/alias type、非递归 polymorphic symbol 与 polymorphic axiom/lemma/goal；用户 datatype/高阶/lambda/epsilon/递归仍精确拒绝。
- [ ] ordinary term attributes 按 Bytes 保留；控制属性 default-deny allowlist 生效；用户 Dmeta 精确拒绝。
- [ ] `use import int.Int` 在 Theory 与 Pmodule 两条路径工作，program operator 解析到正确 RoutineSymbol/Cty/rs_logic。
- [ ] frozen snapshot 保留完整 driver closure 所需 NoDef/Alias/Range/Float、Ddata/Dparam/Dlogic/Dind(Ind)/Dprop、Use/Clone/Meta 和 integer/real/string constants；trusted WellFounded inductive 在 printer 前被消除，Coind 仍 fail closed。
- [ ] `minimal_env` 返回 FrozenEnvironment；公开 resolver 仅见五个入口，隐藏 DriverSymbolCatalog 全量 eager bind，DriverOnlyTheory/ResolveError 分流准确。
- [ ] pure Theory 能 split 成单 goal Task。
- [ ] pure logic 闭环 A 可以运行 Z3。
- [ ] static Z3 profile 顺序与 `z3_487.drv` 对齐。
- [ ] 多态窄路径的 detect/discriminate/eliminate/monomorphise/select-kept/twin/guards/encoding 阶段逐 checkpoint exact，printer 前无残余类型变量。
- [ ] unsupported transform input fail closed。
- [ ] typed 每 unit、raw/checkpoint/prepared 每 goal 的完整 canonical JSON 与 hash exact；SHA-256 为 MoonBit all-target 实现并通过标准向量。
- [ ] SMT token 只对 Generated(stage) 名称 alpha-renumber；用户/snapshot 名称及 declaration/assert/pattern 顺序与原版 exact。
- [ ] trusted Tuple0/Unit Ddata 走精确 `declare-datatypes`；其余 datatype fail closed。
- [ ] native runner 默认 10 秒、0 无自动 deadline、正值 `4*t+1` deadline；stdout/stderr 各 2 MiB，超限优先并回收进程。
- [ ] `unsat -> Valid`，`sat -> Unknown("sat")`。
- [ ] ProverResult 只表示成功启动并完成分类的 outcome；ContextMismatch/BindError/OutputLimitExceeded 等 typed error 不混入结果 enum。
- [ ] 最小 typed program IR 支持 Bool/Int/Real/Unit 的单态非递归纯函数、pre/post、Real 算术/比较和 call；trusted stdlib polymorphic routine 可实例化。
- [ ] Kode/classical WP 支持 let/if/assert/assume/call。
- [ ] `abs` 和 routine-call 示例通过闭环 B。
- [ ] false postcondition 不会返回 Valid。
- [ ] semantic_profile_sha256 与 oracle_context_sha256 分离；公共 record 无机器环境，绝对路径/实际 argv 只在 resolved_context.json。
- [ ] 原版 oracle 分层比较 typed semantic/full canonical raw/checkpoints/prepared/SMT/result；最终 PR 提交完整内容，nightly 内容只作 artifact。
- [ ] `check/task/emit-smt/prove` 阶段边界、源码 goal 串行顺序、单 goal stdout、多 goal目录文件名、goal-index、NDJSON 和三值退出码均符合协议。
- [ ] pure packages all-target，只有 runner/CLI native-only。
- [ ] 根 library package 为空；内部 `.mbti` 已提交审查但不承诺 library API compatibility。
- [ ] `moon check --target all --warn-list +73` 通过。
- [ ] `moon test --target all --serial` 通过。
- [ ] native runner/Z3 integration 通过。
- [ ] `moon info` 后 `.mbti` 变化符合预期。
- [ ] `moon fmt` 后工作区无差异。
