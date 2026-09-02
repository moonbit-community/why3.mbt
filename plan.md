# Why3 1.7.2 WhyML 翻译闭环补全计划

## 目标

- 在本计划范围及“固定假设”中明示的兼容性例外内，严格对齐 `../why3` 的 Why3 1.7.2 提交 `1343338d3bb1941c0d4f134283bb0790816113c4`，完成 WhyML 解析、类型检查、完整程序 IR、VC、Task、Z3 driver、SMT-LIB 和证明调用闭环。
- 发布为破坏性 `0.2.0`：以上游语义忠实度优先，允许重构包、公开类型和 canonical schema。
- 纯解析/类型/VC/SMT 管线继续支持所有 MoonBit target；文件系统、配置读取和 Z3 进程仅位于 native 层。
- 不包含 sessions、IDE、RAC/解释器、代码提取、非 Z3 prover/printer，以及 Z3 闭包之外的全量交互式 transforms。

## 架构与接口变更

- 新建无依赖的字面量语义层，统一表示 Why3 `Constant` 的整数、实数和字符串常量；`parser` 与 `core/logic` 共同依赖它，移除当前 `core/logic -> parser` 反向依赖及所有 snapshot-only 构造限制。
- 按 Why3 模型重建 MLW：
  - `Ityreg/Ityapp/Ityvar`、Region、完整类型参数/区域标志。
  - `MaskVisible/MaskTuple/MaskGhost` 和异常符号。
  - Effect 的 reads、writes、taints、covers、resets、raises、spoils、
    `eff_oneway`（`Total/Partial/Diverges`）和 ghost。
  - Cty 的 args、pre/post/xpost、oldies、effect、result、mask、freeze。
  - 完整 Expr/Cexp、赋值、匹配、循环、异常、递归、ghost、absurd、局部函数，以及 PDtype/PDlet/PDexn/PDpure、module use/clone/meta/scope。
- 将环境拆成纯 `SourceProvider` 与类型环境：
  - Provider 返回给定库路径的全部候选；零个、多个、循环依赖分别产生与官方等价的错误。
  - 提供 all-target 的内存/嵌入式 provider，以及 native 文件系统 provider。
  - 类型环境负责惰性解析、递归加载、typed-file 缓存、builtin 注册和独立 CompilationContext。
  - `pipeline.check` 改为显式接收环境；另提供使用完整嵌入式标准库的便捷入口。
- 用 canonical v3 替换 v2：覆盖全部 core/MLW 图结构，以首次遍历编号表示符号、区域、变量、例外和 routine，共享节点只定义一次；绑定变量使用 de Bruijn；集合和映射按 canonical key 排序；不序列化缓存、运行时 tag 或地址。诊断记录比较阶段、类别、警告码和源区间，不比较英文消息。
- 增加 all-target 的纯 Driver/Z3 profile 层，解析固定的 `z3_487.drv` 及其 import 闭包中实际使用的 printer、model parser、结果匹配、theory/syntax/meta/transformation 等指令；SMTv2.6 printer 和 model parser 也保持为纯逻辑。native 层只负责配置文件与 prover 探测、文件系统、进程调用及资源限制。
- `why3mbt prove` 对齐官方相关参数：多文件/stdin、`-T/-G/-g`、`-L/--no-stdlib`、`-F`、`--parse-only/--type-only`、`-C/--config`、`--extra-config`、`--no-load-default-plugins`、`-P z3`、`-D`、`-a`、`-M`、`-t/-s/-m`、`-o`、打印 theory/namespace 和 JSON；同时对齐 `-P/-D` 冲突、`-o` 只输出而不调用 prover、`-t` 接受浮点秒数、选择器作用顺序及成功/错误/存在未证目标的退出码 `0/1/2`。RAC、配置中请求加载插件、非 Z3 prover/printer 或未知 transform 明确报错；现有 check/task/emit-smt 保留为辅助命令，不作为官方兼容面。

## 实施顺序

1. 扩展 OCaml reference exporter，先定义完整 canonical v3、结构化诊断和全量 feature contract，并显式导出 module/theory 类别及 module interface；当前两个 module-interface fixture 从 extension/intentional-divergence 重分类为官方 exact 行为。迁移期间并行保留 v2 基线，最终切换时删除 v2 API 与基线。
2. 先落地无反向依赖的 `Constant`/字面量层，再完成 core 的数值、类型、term/pattern、递归 logic/data/inductive、coercion、clone、meta、theory/task smart constructors 和全部官方不变量。
3. 移植完整 Ity、region/effect/Cty，再移植 Expr 和 Pdecl；每个 effect 组合与非法别名/ghost/write/stale 情形先有单元测试。
4. 先实现不依赖 MLW 的 `SourceProvider`、库路径解析以及 Env/CompilationContext 的 builtin、循环检测和通用缓存接口，再移植 Pmodule 的 unit/namespace/use/clone/meta/scope 与 module-interface 操作，并在下一步接上 typed-file cache。上游 `Pmodule` 直接使用 `Env.env`；MoonBit 侧须把 provider/core-env 与保存 Pmodule 的 typed-env 分层，既不能漏掉该依赖，也不能制造 package 环。
5. 按官方两阶段模型移植 Dterm/Dexpr/typing，并把递归库加载接入上一步的环境：支持高阶与多态程序、数据类型/记录/range/float/private/invariant/witness、模式、递归、循环、引用、异常、old/at、完整 spec、clone/meta 和模块接口。保留并补全官方 module-interface 语义（目前由两个 fixture 覆盖）；这两个文件可通过 Why3 1.7.2 的 `why3 prove --type-only`，不是项目扩展，只是 `why3 pp --output=sexp` 的简化 parsing-only 入口拒绝且其 `Ptree.mlw_file` 也无法表示该文件头。
6. 以嵌入式原始 `.mlw` 源码替换 12MB 受限 semantic snapshot，惰性加载全部 53 个官方标准库文件；同时实现 `Env.base_language_builtin` 与 `Pmodule.mlw_language_builtin` 的按需 builtin theory/module（包括按需 tuple 家族），这些 builtin 不计入 53 个磁盘文件。native `-L` 使用同一解析和缓存路径。
7. 移植 `eval_match`、`typeinv` 和完整 VC，实现 classical WP 以及由全局 debug flag `vc_sp` 启用的 Efficient Weakest Preconditions（SP/WP 混合过程），并支持局部 `vc:sp`/`vc:wp` 切换、循环/递归终止性、异常后置条件、effects、type invariant 及其余 `vc:*` 控制属性。
8. 补齐 Z3 4.8.12 按官方探测规则选中的 `z3_487.drv` closure（文件名表示最低兼容版本 4.8.7）、transform 分支、SMTv2.6 printer/model parser、配置和 CLI；最后清除旧 Unsupported gate、受限 IR、静态五模块根和 snapshot trusted API，更新版本及 `.mbti`。

## 测试与验收

- 989 个 `.mlw` parser fixture 的当前 parsing-only 矩阵为：929 个可由 `why3 pp --output=sexp` 导出 Ptree S-expression，并与 MoonBit 逐字节比较；另外 2 个 module-interface fixture 由官方主 WhyML 入口（以 `why3 prove --type-only` 验证）接受，但 `why3 pp` 的简化 parsing-only 入口拒绝且 `Ptree.mlw_file` 无法表示其完整文件头，须由扩展后的 reference exporter 比较解析结构和 typed IR。这里的 931 只表示解析阶段接受，不能写成 931 个文件均通过类型检查。其余 58 个是当前由 `why3 pp` 得到的 parse-reject corpus；canonical v3 冻结矩阵前须用主 WhyML 入口复核阶段和类别，不能仅凭 `why3 pp` 推断 Why3 整体拒绝。复核后由 MoonBit 以结构化诊断拒绝：当前 57 个比较官方源位置，`examples/use_api/epsilon.mlw` 因当前官方 `why3 pp` 诊断没有位置而只比较类别，并要求 MoonBit 给出稳定 span；目标 intentional-divergence 数量为零。
- 以 Why3 1.7.2 的 `src/parser/ptree.ml` 为可序列化 Ptree constructor 清单的事实来源，以 `src/parser/parser.mly` 和 `src/parser/typing.ml` 为完整 WhyML 文件语法及 module-interface 语义的事实来源；`Ptree.mlw_file` 不记录 module/theory 区分和 interface，不能单独定义完整语法。所有官方合法行为进入 exact lane、非法形态进入 reject lane，不再存在项目特有的 unsupported lane；现有 feature contract 中的 169 项是本项目解析 AST 的变体清单，不再误称为“169 个 Ptree variant”。
- 全部 53 个 `stdlib/**/*.mlw` 文件均可从嵌入式资源和 native loadpath 加载；另逐项比较 `Env.base_language_builtin` 与 `Pmodule.mlw_language_builtin` 生成的 builtin theory/module 及按需 tuple 家族，公开 theory/module 与官方一致。
- 建立覆盖 `examples/` 下 446 个和 `tests/` 下 58 个 upstream `.mlw`/`.why` 文件的清单（不把 `examples_in_progress/` 混入“446 个”这个数字）：对官方可接受文件按其适用阶段比较 typed IR、VC/raw task、transform checkpoint 和 SMT token；仅允许记录依赖明确排除工具的环境性豁免，不允许语言特性豁免。
- 每项新增语言能力至少有一个端到端 fixture；Z3 结果只在固定的确定性 solver corpus 上比较，完整语料比较到 SMT token。
- 覆盖缺失库、歧义库、循环导入、clone substitution、region alias、ghost write、异常泄漏、非终止、module interface、stdin/多文件和 CLI 选择器。
- 每个切片保持 `moon check --target all --warn-list +73`、全目标 debug/release tests、Node contract tests、native ASan 和 reference differential 通过；最终执行完整 `node tools/run.mjs check --why3-root ../why3`，再运行 `moon info && moon fmt` 并审查预期的破坏性 `.mbti` 差异。

## 固定假设

- 只对齐 Why3 1.7.2 与 Z3 4.8.12；升级新版 Why3 另立项目。
- 源代码名称、属性和字符串常量保持原始 Bytes；native 路径与 CLI 参数要求有效 UTF-8。后者是相对 Why3 在 Unix 上可接受任意字节路径的明确兼容性例外，必须产生稳定诊断，且不得计入 exact lane。
- 单个 CompilationContext 保持单线程；并行编译通过相互独立的 context 实现。
- 每个迁移切片同步维护上游文件映射、许可证来源和 differential fixture，禁止通过直接重录 baseline 掩盖语义差异。
