# 当前仍存在的 upstream/layer 差异报告

- 测试执行日期：2026-07-30（Asia/Shanghai）
- 报告整理日期：2026-07-31（Asia/Shanghai）
- 分支与基准提交：`extend` / `6e582af`
- MoonBit：`moon 0.1.20260724 (5f1406a 2026-07-24)`
- Node.js：`v24.3.0`
- Why3 参考源：Why3 `1.7.2`，提交 `1343338d3bb1941c0d4f134283bb0790816113c4`
- 参考运行时缓存键：`34d127d4b8f840ed4ae880147b5a6eec91d2d3d2378f3c4490bc8602296a2772`
- 工作区状态：存在大量未提交改动；以下结果反映当前工作区，不只反映基准提交。

## 状态摘要

常规单元测试仍全部通过，但这不代表 Why3 兼容性已经达标。当前剩余问题集中在 upstream semantic 和 `mvp.mlw` 的中间表示：

| 状态 | 范围 | 数量 | 含义 |
| --- | --- | ---: | --- |
| **已确认差分** | upstream canonical semantic | **155 个文件** | MoonBit 与 Why3 都产出了合法记录，但 canonical 内容不同 |
| **目标侧明确失败** | upstream MoonBit exporter | **120 个文件** | 有明确的转换、VC generation 或输出协议错误 |
| **目标侧信号终止** | upstream MoonBit exporter | **2 个文件** | 需要隔离复跑，暂不能判断为稳定缺陷 |
| **已确认差分** | elaboration | **`mvp.mlw` 1 个 fixture** | typed canonical output 不同 |
| **已确认差分** | transform | **`mvp.mlw` 1 个 fixture** | raw-task canonical output 不同 |
| 未判定 | Why3 参考侧或采集器 | 45 个文件 | 没有形成有效的双侧比较 |
| 环境阻塞 | prover result | 24 个 goal | 锁定 OCI 参考环境不可用，尚未执行 |

最需要关注的是：

- 459 个 upstream accepted 文件中，只有 137 个完成端到端精确匹配。
- 至少 275 个文件留下了可直接定位的 MoonBit 侧问题：155 个 canonical mismatch，加上 120 个带明确错误信息的目标侧失败。
- 类型接受性仍是 `504/504`，说明问题主要不在“文件能否被接受”，而在 typed representation、VC/raw task、transform 和 SMT 输出是否与 Why3 一致。
- `mvp.mlw` 的 elaboration/raw-task 虽有差异，但该 fixture 的 16 条 SMT token stream 全部一致；这表明该 fixture 的中间表示差异尚未传播到最终 SMT token。

不同测试层的计数口径不同，不能把 upstream 文件数、layer fixture 数和 result goal 数直接相加为“唯一失败数”。

## 仍存在的 upstream semantic 差异

执行入口：

```text
node tools/run.mjs upstream --why3-root ../why3
```

官方入口先完成类型语料，然后在首个 semantic mismatch 处 fail-fast。为了得到全部 459 个文件的结果，另用临时的 non-fail-fast 收集分支执行相同的目标/参考导出、校验与比较逻辑，并保持并发度 2、每侧单文件 30 分钟上限。临时脚本已删除。

| 阶段 | 结果 | 判定 |
| --- | ---: | --- |
| 类型接受/拒绝语料 | 504 / 504 exact | 通过 |
| 其中应接受 | 459 / 459 | 通过 |
| 其中应拒绝 | 45 / 45 | 通过 |
| 完整 semantic exact | 137 / 459 | 137 个通过 |
| canonical semantic mismatch | 155 | 确认差分 |
| MoonBit 目标侧执行失败 | 122 | 不通过 |
| Why3 参考侧失败或超时 | 40 | 未形成有效差分 |
| Node 采集器字符串上限 | 5 | 未形成有效差分 |

### Canonical mismatch 首次出现阶段

下表按每个文件的第一条不同记录统计 155 个 canonical mismatch：

| 首次差分 stage | 文件数 | 所属输出层 |
| --- | ---: | --- |
| `typed-program` | **85** | module typed representation |
| `raw-task` | **33** | VC/task generation |
| `typed-semantic` | **12** | theory typed representation |
| `encoding_smt_if_poly:select_kept` | 10 | transform checkpoint |
| `smt-tokens` | 6 | 规范化 SMT token stream |
| `discriminate_if_poly` | 4 | transform checkpoint |
| `eliminate_inductive` | 3 | transform checkpoint |
| `inline_trivial` | 2 | transform checkpoint |
| **合计** | **155** |  |

差异分布说明：

- 97/155（62.6%）首次出现在 typed output，是当前最大的差异面。
- 33/155（21.3%）首次出现在 raw task，说明 VC/task generation 仍有明显不一致。
- 19/155（12.3%）首次出现在 transform checkpoint。
- 只有 6/155（3.9%）首次出现在 SMT token；多数问题在到达 SMT 输出前已经出现。

### MoonBit 目标侧执行失败

目标侧 122 个失败的主要错误分布：

| 错误 | 数量 |
| --- | ---: |
| `eliminate_literal failed` | 64 |
| VC generation 类型、符号或声明错误 | 41 |
| stdout 出现非 JSON 的 `KEEPDBG` 前缀 | 10 |
| 进程被信号终止 | 2 |
| `discriminate_if_poly:monomorphise_goal failed` | 2 |
| `eliminate_projections_sums failed` | 2 |
| task splitting 声明引用错误 | 1 |

- `eliminate_literal` 和 VC generation 两类合计 105/122，是最集中的目标侧失败来源。
- 10 个 `KEEPDBG` 属于输出协议污染：即使内部语义正确，也会因为 stdout 不是 canonical NDJSON 而无法比较。
- 2 个信号终止没有稳定错误信息，应隔离复跑后再判断：
  - `examples/prover/Prover.mlw`：`SIGKILL`
  - `examples/verifythis_2018_mind_the_gap_2.mlw`：`SIGABRT`

### 尚未形成有效差分

Why3 参考侧 40 个未完成比较的分布：

| 错误 | 数量 |
| --- | ---: |
| `smt-libv2.gen` 参考驱动异常 | 28 |
| Why3 警告伴随非零退出 | 7 |
| 进程被信号终止 | 3 |
| 30 分钟超时 | 1 |
| source inventory 与 typed environment 数量不一致 | 1 |

这 40 个参考侧问题加上 5 个 Node 字符串上限问题，不应计入已确认的 MoonBit semantic mismatch；它们仍然是覆盖缺口。

### 结果证据与隔离校正

逐文件原始结果保存在 `_build/upstream-semantic-results.json`，SHA-256 为 `29d28017a4c7fce14f3b96dcc88966459f0b98e14a28f6e1c8f990d3abb39e8b`。该原始文件保留首次全量收集结果；全量结束后的隔离复核校正了两项：

- `examples/random_access_list.mlw` 从参考侧 `SIGKILL` 校正为 record 19、`encoding_smt_if_poly:select_kept` 阶段的 canonical semantic mismatch。
- `examples/sudoku.mlw` 仍属于目标侧失败，但从 `SIGKILL` 校正为 `VC generation for 536f6c766572 failed: let-bound value has the wrong type`。

本报告的计数和下方文件集合均使用校正后的分类。

### 建议排查顺序

1. 先定位 97 个 typed-output mismatch 的共同 canonicalization/编号差异；这是覆盖面最大的类别。
2. 集中处理 64 个 `eliminate_literal` 和 41 个 VC generation 失败。
3. 清除 10 个 `KEEPDBG` stdout 污染；这是相对独立的输出协议问题。
4. 再处理 33 个 raw-task mismatch、19 个 transform mismatch 和 6 个 SMT-token mismatch。
5. 最后隔离复跑 2 个目标侧信号终止，并修复参考侧/采集器问题以补齐 45 个未判定文件。

## 仍存在的 layer 差异

执行入口：

```text
node tools/run.mjs layers all --why3-root ../why3
node tools/run.mjs layers transform --why3-root ../why3
node tools/run.mjs layers smt --why3-root ../why3
node tools/run.mjs layers result
```

`layers all` 在 elaboration 的首个 `mvp.mlw` 差分处停止。为避免 fail-fast 隐藏后续 fixture，elaboration 和 transform 各使用临时收集分支跑完全部 7 个 fixture；临时代码随后已撤销。

### `mvp.mlw` 已确认差异

| 层 | 首个差异 | 当前影响 |
| --- | --- | --- |
| elaboration | typed output 在 byte `592259`、record `1`、`$.canonical[2][2554][3][1][0][4][1][2]` 处不同；Why3 为 `550`，MoonBit 为 `551` | typed canonical 不精确一致 |
| transform | raw-task 在 byte `2056892`、line `4` 处不同；两侧长度均为 `8157791` bytes | raw-task canonical 不精确一致 |
| SMT | 无差异，16/16 token stream 精确一致且可由 Z3 解析 | 上述中间表示差异未传播到该 fixture 的 SMT token |

这两个差异来自同一个 fixture，但属于两个独立比较层，不能合并成一个已经通过的结果。

### 全部 fixture 结果

| fixture | elaboration | transform | SMT |
| --- | --- | --- | --- |
| `tools/why3_reference/fixtures/mvp.mlw` | **失败** | **失败** | 16 / 16 通过 |
| `tests/vc/false-post.mlw` | 通过 | 通过 | 1 / 1 通过 |
| `tools/why3_reference/fixtures/transform-polymorphism.mlw` | 通过 | 通过 | 1 / 1 通过 |
| `tools/why3_reference/fixtures/transform-polymorphic-definition.mlw` | 通过 | 通过 | 1 / 1 通过 |
| `tools/why3_reference/fixtures/transform-inductive.mlw` | 通过 | 通过 | 1 / 1 通过 |
| `tools/why3_reference/fixtures/smt-identifiers.mlw` | 通过 | 通过 | 1 / 1 通过 |
| `tools/why3_reference/fixtures/solver-outcomes.mlw` | 通过 | 通过 | 3 / 3 通过 |

### 通过项与证据

- elaboration 的 3 个负向诊断用例全部通过。
- transform 其余 fixture 合计 152 个 checkpoint record 精确通过。
- SMT 合计 24 条 token stream 精确一致并通过 Z3 解析，使用 Why3 `1.7.2` 和 Z3 `4.8.12`。
- elaboration 逐 fixture 结果 SHA-256：`68b04b3e297ba2c39571861e242f139f4fbffb64339b879d3224edfab79ea3f0`。
- transform 逐 fixture 结果 SHA-256：`17f3d9ea85e7b6477aea893f4a695120df8875395bccfb8430cdc50a5d29e709`。

## 尚未判定：result layer

result 层契约包含 24 个 prover-result goal。直接执行时在比较开始前失败：

```text
run-fixed: ENOENT: no such file or directory, open '/opt/reference-env/manifest.json'
```

它要求精确锁定的 OCI 镜像：

```text
ghcr.io/moonbit-community/why3.mbt-why3@sha256:7733151a936bb9fc054372dad82143ab16ca53b0b451a5d6b6875f3bd5b1726a
```

当前环境的阻塞链如下：

- Docker CLI 存在，但 `/var/run/docker.sock` 不存在。
- `ctr` 存在，但 `/run/containerd/containerd.sock` 不存在。
- 临时 rootless Docker 因系统缺少 `newuidmap` 无法启动。
- 使用临时 OCI 客户端匿名读取 GHCR 时返回 `UNAUTHORIZED`。
- 当前 `gh` 登录凭据无效，无法为需要认证的镜像提供 pull token。

因此 24 个 result goal 均未执行，不能标为通过或失败。临时 rootless/OCI 下载目录已清理。

## 已通过的本地基线

| 检查项 | 模式/后端 | 结果 |
| --- | --- | --- |
| `moon test -v` | 默认 debug / `wasm-gc` | 503 / 503 通过 |
| `moon test --target all --serial --release` | `wasm` | 507 / 507 通过 |
| 同上 | `wasm-gc` | 503 / 503 通过 |
| 同上 | `js` | 503 / 503 通过 |
| 同上 | `native` | 518 / 518 通过 |
| `moon test --target all --serial` | `wasm` | 507 / 507 通过 |
| 同上 | `wasm-gc` | 503 / 503 通过 |
| 同上 | `js` | 503 / 503 通过 |
| 同上 | `native` | 518 / 518 通过 |
| `node --test tools/*.test.mjs` | 9 个 Node.js 工具测试文件 | 9 / 9 通过 |
| `sh tools/check_native_runner_asan.sh` | native runner + ASan | 通过 |
| `node tools/run.mjs fixtures` | 989 个 WhyML fixture | 989 / 989 校验通过；931 个应接受，58 个应拒绝 |
| `node tools/run.mjs contracts --quick` | 快速契约与参考环境锁校验 | 通过 |

各 MoonBit 后端的测试数不同，是包的目标支持范围及 native 专属集成测试造成的，不代表失败或漏报。

测试编译期间的 `[0012] unreachable_code`、`[0035] reserved_keyword`、未使用函数/变量等警告均未导致常规测试失败。ASan 第一次在受限沙箱内因 LeakSanitizer 不支持 `ptrace` 环境而中止；在沙箱外用同一命令复跑成功，因此属于执行环境限制。

## 附录：upstream semantic 逐文件分类

下面五个集合互斥且合计 459 个 accepted 文件。差异审阅应优先展开“canonical semantic mismatch”和“MoonBit 目标侧执行失败”；通过列表仅用于确认基线。

<details>
<summary>已通过（参考基线）：137 个</summary>

```text
examples/WP_revisited/blocking_semantics5.mlw
examples/WP_revisited/imp_n.why
examples/WP_revisited/wp2.mlw
examples/add_list.mlw
examples/add_list_vc_sp.mlw
examples/algo63.mlw
examples/algo64.mlw
examples/algo65.mlw
examples/all_distinct.mlw
examples/amortization.mlw
examples/arm.mlw
examples/array_most_frequent.mlw
examples/assigning_meanings_to_programs.mlw
examples/avl/key_type.mlw
examples/avl/preorder.mlw
examples/balance.mlw
examples/bignum.mlw
examples/binary_sort.mlw
examples/bresenham.mlw
examples/bts/114_infix.mlw
examples/bts/12445.mlw
examples/bts/126_apply.mlw
examples/bts/12934.why
examples/bts/13002.why
examples/bts/130_extraction.mlw
examples/bts/13375.mlw
examples/bts/13849.why
examples/bts/13854.why
examples/bts/14097.mlw
examples/bts/16_subst.mlw
examples/bts/17184.mlw
examples/bts/185_apply.mlw
examples/bts/185_apply_let.mlw
examples/bts/18953.why
examples/bts/19_apply_with.mlw
examples/bts/20445.mlw
examples/bts/20619.mlw
examples/bts/20881.why
examples/bts/231_destruct.mlw
examples/bts/244_destruct_rec.mlw
examples/bts/264_destruct_if.mlw
examples/bts/265_apply.mlw
examples/bts/269_replace_under_if.mlw
examples/bts/276_shape.mlw
examples/bts/311_destruct.mlw
examples/bts/353.mlw
examples/bts/380_doc_trans.mlw
examples/bts/380_trans_space_args.mlw
examples/bts/612.mlw
examples/bts/690_reserved_keywords.mlw
examples/bts/695_remove_unused.mlw
examples/bts/71_disambiguation.mlw
examples/bts/742.mlw
examples/bts/746.mlw
examples/bts/773.mlw
examples/bts/788.mlw
examples/bts/95_char_encoding_latin1.mlw
examples/bts/ce_symbols.mlw
examples/bts/execute.mlw
examples/bts/fsetint.why
examples/bts/remove_unused_remove_cte.mlw
examples/bts/simplify.mlw
examples/cubic_root.mlw
examples/double_wp/imp.why
examples/double_wp/state.why
examples/double_wp/vm.mlw
examples/euler001.mlw
examples/f_puzzle.mlw
examples/fact.mlw
examples/fill.mlw
examples/finite_tarski.mlw
examples/flag.mlw
examples/flag2.mlw
examples/foveoos11-cm/array_max.mlw
examples/foveoos11-cm/duplets.mlw
examples/foveoos11-cm/tree_max.mlw
examples/foveoos11_challenge1.mlw
examples/foveoos11_challenge3.mlw
examples/hello-world.mlw
examples/huffman_with_two_queues.mlw
examples/i_cant_believe_it_can_sort.mlw
examples/insertion_sort.mlw
examples/insertion_sort_naive.mlw
examples/isqrt.mlw
examples/mjrty.mlw
examples/muller.mlw
examples/multiprecision/valuation.mlw
examples/pancake_sorting.mlw
examples/pigeonhole.mlw
examples/power.mlw
examples/prover/Choice.mlw
examples/prover/Nat.mlw
examples/prover/Sum.mlw
examples/selection_sort.mlw
examples/subsequence.mlw
examples/tests/alt-ergo-models.why
examples/tests/array-test.mlw
examples/tests/hashtbl-test.mlw
examples/tests/lemma_functions.mlw
examples/tests/random-test.mlw
examples/tests/replay.mlw
examples/three_idem_ring.mlw
examples/toy_compiler.mlw
examples/tree_of_list.mlw
examples/vacid_0_binary_heaps/abstract_heap.mlw
examples/vacid_0_binary_heaps/bag_of_integers.why
examples/vacid_0_binary_heaps/elements.why
examples/vacid_0_binary_heaps/heap.why
examples/vacid_0_binary_heaps/heap_implem.mlw
examples/vacid_0_binary_heaps/heapsort.mlw
examples/vacid_0_binary_heaps/test_harness.mlw
examples/verifythis_2015_relaxed_prefix.mlw
examples/verifythis_2016_matrix_multiplication/sum_extended.mlw
examples/verifythis_PrefixSumRec.mlw
examples/vstte12_two_way_sort.mlw
examples/white_and_black_balls.mlw
tests/PGCD.mlw
tests/SimpleDBPath.why
tests/SimpleDBPathSansListes.why
tests/bug-transf.why
tests/computation.why
tests/dubious_axioms.mlw
tests/infer/test_exn.mlw
tests/infer/test_if.mlw
tests/infer/test_match.mlw
tests/test-and.why
tests/test-ghost.mlw
tests/test-ind.why
tests/test-match.why
tests/test-polyrec.why
tests/test-smoke-detector.why
tests/test_args_parsing.mlw
tests/test_ghost.mlw
tests/test_itp.mlw
tests/test_merge.mlw
tests/test_smoke.mlw
tests/tests-boolean.mlw
```

</details>

<details>
<summary>仍存在 canonical semantic mismatch：155 个</summary>

```text
examples/WP_revisited/formula.why
examples/avl/avl.mlw
examples/avl/monoid.mlw
examples/avl/ral.mlw
examples/bag.mlw
examples/bellman_ford.mlw
examples/binary_sqrt.mlw
examples/binomial.mlw
examples/binomial_heap.mlw
examples/bitvectors/bitvector.why
examples/bitvectors/double.why
examples/bitvectors/neg_as_xor.why
examples/bitvectors/power2.why
examples/braun_trees.mlw
examples/bts/12475.why
examples/bts/16972.mlw
examples/bts/17137.mlw
examples/bts/20618.mlw
examples/bts/374_eliminate_if_explodes.mlw
examples/bts/438.mlw
examples/bts/559.mlw
examples/bts/587.mlw
examples/bts/753.mlw
examples/bts/79_compute_unsound.mlw
examples/bubble_sort.mlw
examples/checking_a_large_routine.mlw
examples/coincidence_count_list.mlw
examples/counting_sort.mlw
examples/decrease1.mlw
examples/dfa_example.mlw
examples/dfs.mlw
examples/dijkstra.mlw
examples/disamb.mlw
examples/division.mlw
examples/double_wp/specs.mlw
examples/edit_distance.mlw
examples/equality_up_to_spaces.mlw
examples/euler002.mlw
examples/euler011.mlw
examples/ewd673.mlw
examples/fact_vc_sp.mlw
examples/fenwick.mlw
examples/fibonacci.mlw
examples/find.mlw
examples/finger_trees.mlw
examples/flexible_arrays.mlw
examples/foveoos11_challenge2.mlw
examples/gcd_bezout.mlw
examples/gcd_bezout_vc_sp.mlw
examples/generate_all_trees.mlw
examples/gnome_sort.mlw
examples/hashtbl_impl.mlw
examples/induction.mlw
examples/infinity_of_primes.mlw
examples/insertion_sort_list.mlw
examples/inverse_in_place.mlw
examples/just_join.mlw
examples/kmp.mlw
examples/knuth_prime_numbers.mlw
examples/koda_ruskey.mlw
examples/largest_prime_factor.mlw
examples/lcp.mlw
examples/leftist_heap.mlw
examples/linear_probing.mlw
examples/linked_list_rev.mlw
examples/list_removal.mlw
examples/mergesort_array.mlw
examples/mergesort_list.mlw
examples/mergesort_queue.mlw
examples/mex.mlw
examples/min_max.mlw
examples/multiprecision/ptralias.mlw
examples/mutual_recursion.mlw
examples/my_cosine.mlw
examples/nistonacci.mlw
examples/optimal_replay.mlw
examples/pairing_heap.mlw
examples/pairing_heap_bin.mlw
examples/patience.mlw
examples/power_vc_sp.mlw
examples/prover/BacktrackArray.mlw
examples/prover/Firstorder_term_spec.mlw
examples/prover/Functions.mlw
examples/prover/ISet.mlw
examples/prover/Predicates.mlw
examples/queens.mlw
examples/quicksort.mlw
examples/random_access_list.mlw
examples/relabel.mlw
examples/remove_duplicate.mlw
examples/remove_duplicate_hash.mlw
examples/residual.mlw
examples/resizable_array.mlw
examples/ring_buffer.mlw
examples/ring_decision/ringdecision.mlw
examples/ring_decision/strassen.mlw
examples/ropes.mlw
examples/same_fringe.mlw
examples/schorr_waite.mlw
examples/schorr_waite_via_recursion.mlw
examples/schorr_waite_with_ghost_monitor.mlw
examples/sf.mlw
examples/sieve.mlw
examples/skew_heaps.mlw
examples/sorted_list.mlw
examples/space_saving.mlw
examples/sumrange.mlw
examples/tests/alt-ergo-models.mlw
examples/tests/func_literals.mlw
examples/tests/matrix-test.mlw
examples/tests/regexp-test.why
examples/topological_sorting.mlw
examples/tortoise_and_hare.mlw
examples/tower_of_hanoi.mlw
examples/tree_height.mlw
examples/tree_of_array.mlw
examples/unraveling_a_card_trick.mlw
examples/vacid_0_binary_heaps/heap_model.why
examples/vacid_0_build_maze.mlw
examples/vacid_0_sparse_array.mlw
examples/verifythis_2015_dancing_links.mlw
examples/verifythis_2015_parallel_gcd.mlw
examples/verifythis_2016_matrix_multiplication/matrices.mlw
examples/verifythis_2016_matrix_multiplication/matrices_ring_simp.mlw
examples/verifythis_2016_matrix_multiplication/naive.mlw
examples/verifythis_2017_maximum_sum_submatrix.mlw
examples/verifythis_2017_odd_even_sort_rearranging.mlw
examples/verifythis_2017_odd_even_transposition_sort.mlw
examples/verifythis_2017_pair_insertion_sort.mlw
examples/verifythis_2018_array_based_queuing_lock_1.mlw
examples/verifythis_2018_array_based_queuing_lock_2.mlw
examples/verifythis_2018_mind_the_gap_1.mlw
examples/verifythis_2018_register_allocation.mlw
examples/verifythis_2019_cartesian_trees.mlw
examples/verifythis_2021_dll_to_bst.mlw
examples/verifythis_2021_lexicographic_permutations_1.mlw
examples/verifythis_2021_shearsort_modified.mlw
examples/verifythis_fm2012_LRS.mlw
examples/vstte10_aqueue.mlw
examples/vstte10_inverting.mlw
examples/vstte10_max_sum.mlw
examples/vstte10_search_list.mlw
examples/vstte12_bfs.mlw
examples/vstte12_ring_buffer.mlw
examples/warshall_algorithm.mlw
examples/word_common_factor.mlw
examples/zeros.mlw
tests/demo-itp.mlw
tests/extract_ghost.mlw
tests/infer/test_bool.mlw
tests/infer/test_int_as_bool.mlw
tests/multiassign.mlw
tests/test-div-cvc3.why
tests/test-gappa2.why
tests/test_exec.mlw
```

</details>

<details>
<summary>仍存在 MoonBit 目标侧执行失败：122 个</summary>

```text
examples/avl/priority_queue.mlw
examples/avl/tables.mlw
examples/binary_multiplication.mlw
examples/binary_search.mlw
examples/binary_search_vc_sp.mlw
examples/bitcount.mlw
examples/bitvector_examples.mlw
examples/bitwalker.mlw
examples/bts/101_eprover_eliminate_range_literal.mlw
examples/bts/116_array_access.mlw
examples/bts/13515.mlw
examples/bts/138.mlw
examples/bts/13853.mlw
examples/bts/13853a.mlw
examples/bts/13853b.mlw
examples/bts/450_abs.mlw
examples/bts/548-neg-float-lit.mlw
examples/bts/626.mlw
examples/bts/656.mlw
examples/bts/760.mlw
examples/bts/destruct_term.mlw
examples/c_cursor/ccursor.mlw
examples/conjugate.mlw
examples/defunctionalization.mlw
examples/double_wp/compiler.mlw
examples/double_wp/logic.mlw
examples/dyck.mlw
examples/esterel.mlw
examples/euler_sieve.mlw
examples/fib_memo.mlw
examples/gcd.mlw
examples/gcd_vc_sp.mlw
examples/hackers-delight.mlw
examples/hillel_challenge.mlw
examples/incremental.mlw
examples/isqrt_von_neumann.mlw
examples/kleene_algebra.mlw
examples/locate_max.mlw
examples/max_matrix.mlw
examples/maximum_subarray.mlw
examples/mccarthy.mlw
examples/mccarthy_vc_sp.mlw
examples/multiprecision/add.mlw
examples/multiprecision/add_1.mlw
examples/multiprecision/base_info.mlw
examples/multiprecision/compare.mlw
examples/multiprecision/div.mlw
examples/multiprecision/lemmas.mlw
examples/multiprecision/lineardecision.mlw
examples/multiprecision/logical.mlw
examples/multiprecision/mpz.mlw
examples/multiprecision/mpz_abs.mlw
examples/multiprecision/mpz_add.mlw
examples/multiprecision/mpz_cmp.mlw
examples/multiprecision/mpz_cmpabs.mlw
examples/multiprecision/mpz_div.mlw
examples/multiprecision/mpz_div2exp.mlw
examples/multiprecision/mpz_getset.mlw
examples/multiprecision/mpz_mul.mlw
examples/multiprecision/mpz_mul2exp.mlw
examples/multiprecision/mpz_neg.mlw
examples/multiprecision/mpz_realloc2.mlw
examples/multiprecision/mpz_sub.mlw
examples/multiprecision/mul.mlw
examples/multiprecision/powm.mlw
examples/multiprecision/sqrt.mlw
examples/multiprecision/sqrtrem.mlw
examples/multiprecision/stringlemmas.mlw
examples/multiprecision/sub.mlw
examples/multiprecision/sub_1.mlw
examples/multiprecision/toom.mlw
examples/multiprecision/types.mlw
examples/multiprecision/util.mlw
examples/prover/Firstorder_symbol_impl.mlw
examples/prover/Firstorder_symbol_spec.mlw
examples/prover/FormulaTransformations.mlw
examples/prover/OptionFuncs.mlw
examples/prover/Prover.mlw
examples/prover/Unification.mlw
examples/queens_bv.mlw
examples/queue_two_lists.mlw
examples/register_allocation.mlw
examples/rightmostbittrick.mlw
examples/snapshotable_trees.mlw
examples/stdlib/stringCheck.mlw
examples/string_base64_encoding.mlw
examples/string_hex_encoding.mlw
examples/string_search.mlw
examples/sudoku.mlw
examples/swap.mlw
examples/tests/bitvector-test.why
examples/tests/bv-smtlib-realization.why
examples/tests/execute-tests.mlw
examples/tests/ignore.mlw
examples/tests/int32-test.mlw
examples/tests/pqueue-test.mlw
examples/tests/queue-test.mlw
examples/tests/rac.mlw
examples/tests/stack-test.mlw
examples/tests/test_elim.mlw
examples/tests/test_projections.mlw
examples/tests/times2float.mlw
examples/there_and_back_again.mlw
examples/vacid_0_red_black_trees.mlw
examples/verifythis_2016_matrix_multiplication/strassen.mlw
examples/verifythis_2016_tree_traversal.mlw
examples/verifythis_2017_tree_buffer.mlw
examples/verifythis_2018_le_rouge_et_le_noir_1.mlw
examples/verifythis_2018_le_rouge_et_le_noir_2.mlw
examples/verifythis_2018_mind_the_gap_2.mlw
examples/verifythis_2019_ghc_sort.mlw
examples/verifythis_2021_lexicographic_permutations_2.mlw
examples/verifythis_2021_shearsort.mlw
examples/verifythis_fm2012_treedel.mlw
examples/vstte10_queens.mlw
examples/vstte12_combinators.mlw
examples/vstte12_tree_reconstruction.mlw
examples/wrap_lines.mlw
tests/infer/test.mlw
tests/test-literals.mlw
tests/test-poly.why
tests/test_foreach.mlw
```

</details>

<details>
<summary>未判定：Why3 参考侧失败或超时 40 个</summary>

```text
examples/bitvectors/double_of_int.why
examples/check-builtin/ac.why
examples/check-builtin/minmax.why
examples/check-builtin/propositional.why
examples/cursor_examples.mlw
examples/logic/First.why
examples/logic/agatha.why
examples/logic/bitvectors.why
examples/logic/bvsum.mlw
examples/logic/distr.why
examples/logic/drinker.mlw
examples/logic/einstein.why
examples/logic/explicit_subst.why
examples/logic/ffx.why
examples/logic/genealogy.why
examples/logic/hello_proof.why
examples/logic/isa_planner.why
examples/logic/los_problem.why
examples/logic/scottish-private-club.why
examples/logic/sorted_list.why
examples/multiprecision/wmpn.mlw
examples/prover/Firstorder_formula_impl.mlw
examples/prover/Firstorder_formula_list_impl.mlw
examples/prover/Firstorder_formula_list_spec.mlw
examples/prover/Firstorder_formula_spec.mlw
examples/prover/Firstorder_semantics.mlw
examples/prover/Firstorder_tableau_spec.mlw
examples/prover/Firstorder_term_impl.mlw
examples/prover/ProverMain.mlw
examples/prover/ProverTest.mlw
examples/tests-provers/ceil.why
examples/tests-provers/coq-interval.why
examples/tests-provers/coq.why
examples/tests-provers/cvc3.why
examples/tests-provers/div.why
examples/tests-provers/div_real.why
examples/tests-provers/gappa.why
examples/tests-provers/metitarski.why
examples/tests-provers/polypaver.why
examples/tests-provers/zeros.mlw
```

</details>

<details>
<summary>未判定：Node 采集器字符串上限 5 个</summary>

```text
examples/multiprecision/get_str.mlw
examples/multiprecision/mpz_get_str.mlw
examples/multiprecision/mpz_set_str.mlw
examples/multiprecision/set_str.mlw
examples/prover/Firstorder_tableau_impl.mlw
```

</details>

## 验证边界

- 没有运行完整的 `node tools/run.mjs check`，因为它还会执行 `moon info`、`moon fmt` 等可能改写当前大量未提交源码的步骤。本次只更新报告，没有 MoonBit API 或源码改动。
- result 层的 24 个用例仍需要带有效 GHCR 凭据的锁定 OCI 环境才能得出结论。
- upstream non-fail-fast 收集器与 layer 临时采集分支均已删除或撤销；没有保留临时源码改动。
- `_build/` 中保留逐文件 JSON 运行产物，便于复核；它们不是源码或契约文件。
