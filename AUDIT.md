# AUDIT — `two-doors-proof-lean`

审计对象：`/Users/xcx0902/Documents/Lean/two-doors-proof-lean`
审计内容：本项目是否**正确形式化了 `editorial.md` 中用来解决 `problem.md` 的两条独立证明**。
审计方式：只读审查（未修改任何 Lean 源文件；本文件为新增）。
审计日期：2026-09-26。

---

## 0. 结论摘要

| 问题 | 结论 |
|---|---|
| 工程能否编译？ | **能**。`lake build` 成功（1720 jobs）。 |
| 有无 `sorry` / `admit` / `axiom` / `unsafe` / `native_decide` / `implemented_by`？ | **没有**（全仓 grep 为零命中；编译日志无 `declaration uses 'sorry'`）。 |
| 主线定理依赖哪些公理？ | 仅 `propext`、`Classical.choice`、`Quot.sound`（Lean/Mathlib 三条标准公理）。已用 `#print axioms` 逐个核验，**无 `sorryAx`**。 |
| `editorial.md` 的两条证明是否都被形式化？ | **是**。证明一（回文收缩 + 翻转对合）与证明二（行列式 / 形式幂级数展开）都完整、无缺口。 |
| 两条证明是否互相独立？ | **是**（除共用"定义词汇""最后的非零步骤""结尾接口组装"外）。证明一的模块链完全不导入任何行列式模块；证明二的证明链不引用任何回文/收缩引理（详见 §4，含可复核的 grep 证据）。 |
| 形式化的是不是**原题**（`problem.md`）的完整解？ | **不是**。README 已明确声明范围：形式化的对象是"已经完成归约后的**收缩简单对偶图 G + 两条不同特殊边**"，并显式排除了平面图对偶、收缩已有墙、自环/重边化简、随机有限域求值、复杂度与"答案 = d\*−2"。这些**未形式化**（详见 §6）。 |

**一句话**：如果把"两条独立证明"理解为 editorial 中"**首非零层 = 最短目标简单路径长度**"的那两条论证，本项目**正确且完整**地形式化了它们；如果把"解决 problem.md"理解为"形式化整题（含答案 d\*−2 与算法）"，则**尚未完成**，但这是 README 声明的既定范围，属"范围外"而非"证明有误"。

---

## 1. 环境与可复现性

- toolchain：`leanprover/lean4:v4.34.0`（`lean-toolchain`）。
- 依赖：`lakefile.lean` 指向 `../lib/mathlib4`（`packagesDir := "../lib/packages"`），本地已存在。
- 构建：`lake build` → `Build completed successfully (1720 jobs).`；对全部 21 个源文件 `touch` 后重编仍成功（排除"仅缓存通过"的可能）。
- 告警：116 条，全部为 lint 级（`unusedSectionVars`、`if_pos`/`if_neg` 已弃用、未使用的 `simp` 参数、`try this` 建议），**无**正确性告警，**无** `sorry` 告警。
- 未发现任何绕过手段：无 `set_option`、无 `@[extern]`、无 `attribute`、无 `unsafe`、无自定义 `axiom`。
- 规模：21 个模块，4884 行；工作区 git 树干净。

公理核验输出（`lake env lean` + `#print axioms`）：

```
TwoDoorsProof.first_nonzero_of_concrete_palindrome_reversal  → [propext, Classical.choice, Quot.sound]
TwoDoorsProof.first_nonzero_of_concrete_determinant          → [propext, Classical.choice, Quot.sound]
TwoDoorsProof.walkSum_X_eq_zero_of_no_target_path            → [propext, Classical.choice, Quot.sound]
TwoDoorsProof.walkSum_X_eq_zero_of_no_target_path_determinant→ [propext, Classical.choice, Quot.sound]
TwoDoorsProof.valid_has_target_path                         → [propext, Classical.choice, Quot.sound]
TwoDoorsProof.pathSum_X_ne_zero_of_shortest                 → [propext, Classical.choice, Quot.sound]
```

---

## 2. 记号对应表

| `editorial.md` | Lean 记号 | 位置 |
|---|---|---|
| 收缩后的对偶图、顶点集 | `V`、`G : SimpleGraph V` | 全局（作为参数） |
| 边界顶点 X / Y | `s` / `t` | `Basic.lean` |
| 特殊边 A / B | `a` / `b : Sym2 V` | `Basic.lean` |
| 封锁的普通门集合 F | `F : Set (Sym2 V)` | `Basic.lean` |
| 四条连通性条件 | `Valid s t a b F` := `¬(withoutB).Reachable s t ∧ ¬(withoutA).Reachable s t ∧ (selected).Reachable s t` | `Basic.lean:31` |
| f(d,t,{A,B})，即长度 d、A/B 各恰好一次的目标游走权和 | `walkSum' z d`（= `walkSum G s t a b z d`） | `Shortest.lean:34`、`WalkSum.lean:34` |
| P\*：最短目标**简单**路径集 | `targetPaths G s t a b d` | `WalkSum.lean:25` |
| 非简单目标游走集 | `targetNonpaths G s t a b d` | `WalkSum.lean:28` |
| 独立不定元 z(e) | `z : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)`，取 `MvPolynomial.X` | `Weights.lean`、`ConcreteDeterminant.lean` |
| 特征 2（x+x=0） | 假设 `h₂ : ∀ x, x + x = 0`；具体用 `ZMod 2` / `CharTwo.add_self_eq_zero` | 各处 |
| α, β 且 α²=β²=0 的截断环 | `Marked R := DualNumber (DualNumber R)`，`alpha := inl eps`、`beta := eps` | `Marked.lean` |
| 最短长度 d\* | `IsShortestTargetPath d` / 参数 `dStar` | `Shortest.lean:27` |

`Valid` 与 editorial 的四条件完全对应：`withoutB a F = fromEdgeSet (F ∪ {a})` 即"F ∪ {A}"，`withoutA b F = fromEdgeSet (F ∪ {b})` 即"F ∪ {B}"，`selected a b F` 即"F ∪ {A,B}"。第 1 条"仅 F 时不连通"由单调性（F ⊆ F∪{A}）免费得到——源码注释写明了这一点（只是注释，未单列引理，不影响结论）。

---

## 3. 两条证明的逐段映射

### 3.1 证明一：回文闭合段收缩 + 无不动点翻转对合

| editorial 小节 | Lean 实现 |
|---|---|
| 把 z(e) 当独立不定元，对**游走**的边权乘积求和 | `targetWalks` / `walkWeight` / `walkSum`（`WalkSum.lean`） |
| "回文闭合段不可能包含特殊边"（边数偶 + 前后半段反向同边 ⟹ 每条边出现偶数次） | `palindrome_closed_segment_special_count_even`、`palindrome_closed_segment_cannot_contain_unique_edge`（`WalkSum.lean:93,114`） |
| "回到原游走进行翻转"（保留区间外前缀/后缀，只反向 [p,q]） | `flipClosed` 及其 `length / count / weight / support` 系列；`flipWalkAt`（`Palindrome.lean:722`） |
| "特征为 2，每一对贡献为 0" | `nonpath_sum_zero`（基于 `Finset.sum_involution`，`WalkSum.lean:192`）；`walkSum_eq_pathSum_of_involution`（`:211`） |
| "先收缩回文闭合段"（只用于**确定**翻转区间，不改变原游走） | `contractInitial` 及其 `support / length / edges / count_le_one / special_count`；`path_of_scanNonpal_none`（`Contraction.lean`） |
| "确定唯一的翻转区间"（取当前顶点的**第一次到最后一次**出现；是回文就收缩，否则停止） | `lastIndex?` 及其 `none_iff / some_iff / getElem / spec`；`scanNonpal`（惰性收缩扫描，`Palindrome.lean:182`）；`scanNonpal_result` / `_result_endpoint` |
| "为什么一定能找到非回文段"（若全是回文 ⟹ 得到更短目标简单路径 ⟹ 与 d\* 最小性矛盾） | `shorter_target_path_of_scanNonpal_none`（`Contraction.lean:216`）+ `scanNonpal_ne_of_minimal`（`Shortest.lean:62`） |
| "记录的是具体出现位置，不能只记录顶点名称" | 扫描返回**原列表位置** `(r,q)`，`flipWalkAt` 直接按位置翻转；`scanned_interval_data` 给出 `getVert r = getVert q` |
| "为什么再做一次会选中同一区间"（归纳 + 前缀/后缀不受影响） | `scanNonpal_stable`（`Palindrome.lean:610`）→ `scanNonpal_flipWalkAt` → `flipFirstNonpal_scan`（`:1019`）→ `flipFirstNonpal_involutive`（`:1029`） |
| "映射没有不动点" | `flipWalkAt_ne_of_nonpalindrome` / `flipFirstNonpal_ne`（`:1047`） |
| 配对仍落在统计范围内（同长、A/B 计数不变、仍非路径） | `flipFirstNonpal_length / _count / _weight`，以及 `palindrome_reversal_certificate_of_minimal` 中 `¬IsPath` 的分支 |
| "DP 仍统计全部允许的游走，不能额外禁止普通边立即往返" | `targetWalks` 只筛 A/B 计数，不限制折返 ✔ |
| "两两抵消后只剩最短简单路径"+"最短层各路径对应不同单项式，不会抵消" | `first_nonzero_of_palindrome_reversal`（`Shortest.lean:180`）+ `pathSum_X_ne_zero_of_shortest`（`Weights.lean:110`） |
| "无目标简单路径时所有长度恒为零" | `walkSum_X_eq_zero_of_no_target_path`（`Weights.lean:161`） |

`palindrome_reversal_certificate_of_minimal`（`Shortest.lean:121`）是证明一的"证书组装点"：`pair := flipFirstNonpal p _`，逐项证明 `mem / fixedFree / involutive / weight_preserved`，随后 `walkSum_eq_pathSum_of_certificate` 把它接到特征 2 的抵消结论上。**这是完整的构造性证明，不是假设。**

### 3.2 证明二：行列式与路径展开

| editorial 小节 | Lean 实现 |
|---|---|
| 环 `F₂[z(e),α,β]/(α²,β²)`，`z̃(e) = αz`（A）、`βz`（B）、`z`（其他） | `Marked R`、`alpha`、`beta`、`markedEdgeWeight`；`alpha_sq`、`beta_sq`、`markedCoeff_powers`（只有 αβ 存活）；`marked_product_coefficient`（`Marked.lean:167`） |
| `[αβ]M^d(s,t) = f(d,t,{A,B})` | `weightedAdj_pow_walks` + `marked_matrix_pow_coefficient`（`MatrixWalk.lean:94`） |
| `Q = I − xM`，`Q^{-1} = Σ x^d M^d`（形式幂级数，不涉收敛） | `matrixGeometric`、`matrixResolvent`、`resolvent_mul_geometric`（`MatrixSeries.lean:47`，用 `abel` 直接证 `(1−xM)·Σ = 1`，**不需要 det 可逆**） |
| "逆矩阵为什么对应交换下标的余子式"（伴随矩阵恒等式） | `det_mul_geometric_eq_adjugate`（`MatrixSeries.lean:55`）；下标方向 `adjugate s t = cof(·,t,s)` 由 `CofactorPaths.cofactorMatrix_det` 显式核对 |
| "新增有向边 y，取 [y]det" | `det_add_directed_edge`、`marked_determinant_coeff_one`、`resolvent_cofactor`（`Determinant.lean:153,169,200`）——**已证，但未接入主链**（见 §5-5） |
| "分母为什么只剩普通边匹配"（长循环两两反向抵消；二元循环遇特殊边则乘积为零；对角项 1） | `nonInvolutive_perm_sum_zero`、`det_eq_perm_sum_charTwo`、`det_eq_involutive_perm_sum`、`involutive_perm_monomial_zero_of_pair`、`det_eq_of_symmetric_square_zero_difference`（`Determinant.lean`） |
| `det(Q) = D(V(G))`，常数项为 1 | `marked_denominator_eq_ordinary`、`ordinary_denominator_eq_map`、`resolvent_det_constant_one`（`DeterminantMatching.lean`）；`ordinaryDenominator_constant_one` |
| 生成恒等式 `Σ f x^d = [αβ][y]det(Q̂)/D` | `determinant_generating_identity`（`DeterminantGenerating.lean:71`）：`seriesOf(walkSum') * ordinaryDenominator = determinantNumerator` |
| "标记边所在的循环怎样变成路径"（σ 含边 t→s ⟹ 循环 `s→…→t→s`，去掉末边得简单路径） | `marked_cycle_vertices`、`marked_cycle_length`、`marked_cycle_path_shape`（`DeterminantPaths.lean`）；`pathOfPerm`、`pathComplementPerm_toList`（`PathComplement.lean`） |
| "固定路径后为什么得到补集上的匹配"（排列在 V∖V(P) 上独立分解） | `pathComplementEquiv`（`markedPerm s t ≃ Σ p, complementPerm p` 的**双射**）、`permMonomial_pathComplement`、`marked_perm_sum_eq_path_complement_det`（`PermutationTerms.lean`） |
| 余子式的路径展开 | `cofactor_path_complement_expansion`（`CofactorPaths.lean:54`） |
| 路径循环的显式权重 `x^{|P|}·Π z(e)` | `pathMatrixWeight`、`pathCycleWeight_resolvent`（`PathCycleWeights.lean:110`） |
| "D(V∖V(P)) 不含 α,β"，剩余特殊边二元循环贡献为零 | `complement_marked_det_eq_ordinary`、`complement_marked_det_is_const`（`ComplementDenominator.lean`） |
| 最终展开式（路径外匹配 + 补集分母） | `marked_cofactor_path_expansion`（`DeterminantPathExpansion.lean:578`）、`markedCoeffSeries_path_term_coeff`（`:352`）、`determinantNumerator_coeff_eq_pathSum_of_minimal`（`:678`） |
| "最低次数为什么就是最优长度" | `coeff_eq_of_mul_eq_of_previous_zero` + `first_nonzero_of_determinant_expansion`（`Shortest.lean:201,231`） |
| 具体证书 | `concreteDeterminantExpansionCertificate`、`first_nonzero_of_concrete_determinant`、`walkSum_X_eq_zero_of_no_target_path_determinant`（`ConcreteDeterminant.lean`） |

路径列表 ↔ 图上游走的双射由 `pathWalkOfChain` / `directedPathListOfWalk` / `graphPathListTargetEquiv` 完成；`graphPathListTarget_sum_eq_pathSum` 说明对路径列表求和恰等于 `pathSum'`。**证明二的证书同样是构造性的**。

---

## 4. 两条证明的独立性（可复核）

**模块级证据。** 关键标识符 `scanNonpal`、`flipWalkAt`、`flipFirstNonpal`、`path_of_scanNonpal_none`、`shorter_target_path_of_scanNonpal_none`、`palindrome_reversal_certificate_of_minimal`、`walkSum_eq_pathSum_of_certificate`、`first_nonzero_of_palindrome_reversal` 在全仓的命中位置仅为：

```
TwoDoorsProof/WalkSum.lean
TwoDoorsProof/Palindrome.lean
TwoDoorsProof/Contraction.lean
TwoDoorsProof/Shortest.lean
TwoDoorsProof/Weights.lean
```

即 `Determinant* / Marked / Matrix* / PathComplement / FintypePath / PermutationTerms / CofactorPaths / PathCycleWeights / ComplementDenominator / ConcreteDeterminant` 中**一个都没有出现**。

**导入图证据。** 证明一的链 `Weights → Shortest → Contraction → Palindrome → WalkSum → Basic` **不导入任何行列式模块**；故证明一完全独立于证明二。

**证明二对证明一的实际依赖**：仅三处，均是"共用词汇"而非"共用证明步骤"：

1. 定义词汇：`targetWalks` / `targetPaths` / `walkWeight` / `walkSum'` / `pathSum'` / `IsTargetPath` / `IsShortestTargetPath`（`WalkSum.lean`、`Shortest.lean`）——两条证明讨论同一批对象，共用不可避免。
2. 结尾的非零步骤 `pathSum_X_ne_zero_of_shortest`（`Weights.lean`）——即 editorial 末节"不同简单路径边集不同 ⟹ 最短层各路径对应不同单项式"，editorial 本身就把它作为**两条证明共用的收尾**。
3. 接口组装：`DeterminantExpansionCertificate` 与 `first_nonzero_of_determinant_expansion` 写在 `Shortest.lean` 里。

**架构小瑕（非错误）**：`Shortest.lean` 同时容纳两种证书接口，并 `import Contraction`（回文链）。因此模块图上 `ConcreteDeterminant` **传递依赖** `Palindrome`/`Contraction`，但证明上不引用其中任何引理（如 §4 grep 所示）。若希望"独立性"在模块图上也可见，可把 `DeterminantExpansionCertificate` / `first_nonzero_of_determinant_expansion` / `coeff_eq_of_mul_eq_of_previous_zero` 迁到独立模块，并让 `Shortest.lean` 只保留公共词汇。

**判定：两条证明在证明层面彼此独立，与 editorial 的"两种彼此独立的证明"一致。**

---

## 5. 陈述与 editorial 的差异（均为**包装**差异，不影响正确性）

1. **"f(d\*,t,{A,B}) = Σ_{P∈P\*} Π z(e)"**：editorial 把"最短层等于最短路径权之和"和"它非零"写成一句。Lean 把它拆成 `walkSum_eq_pathSum_of_certificate`（等号，两部分都可调用）与 `pathSum_X_ne_zero_of_shortest`（非零）；两个 headline 定理只暴露后者的 `≠ 0`。内容等价，只是没打包成一条等式。
2. **行列式路线的"最低次数"结论**以"`d ≤ d*` 时分子系数 = `pathSum' d`"（`determinantNumerator_coeff_eq_pathSum_of_minimal`）的形式给出，而非显式写出 `(Σ_P x^{|P|} Π z(e) D(V∖V(P))) / D(V(G))` 的商式。这是等价的系数级表述；`D(U)` 只用到"常数项为 1"，故无需显式写出匹配多项式。
3. **不定元的选择**：editorial 先用独立不定元证明多项式恒等式，再代入 F\_{2^64} 随机值。Lean 用 `MvPolynomial (Sym2 V) (ZMod 2)` 上取 `X` 作为通用特例，同时**保留**了任意 `[CommRing R]` + `x+x=0` 的一般定理（`first_nonzero_of_palindrome_reversal` / `first_nonzero_of_determinant_expansion`）。比 editorial 更强，但**随机代入那一步未形式化**（§6-5）。
4. **α,β 截断的实现**：用平方零代数的嵌套（`DualNumber (DualNumber R)`）而非商环；`markedCoeff_powers` 证明只有 α·β 项存活，语义等价。
5. **余子式的来源**：editorial 走"A 的 (t,s) 位置加一条带 y 的有向边，取 `[y]det`"。Lean 主链直接用 Mathlib 的 `Matrix.adjugate`（`det_mul_geometric_eq_adjugate`）。editorial 那一版本（`det_add_directed_edge` / `marked_determinant_coeff_one` / `resolvent_cofactor`）**也已证明**，但只被彼此引用、未接入主链——是"同一定理的平行写法"，不是缺口。
6. **退化情形**：`s ≠ t` 与 `a ≠ b` 在行列式路线中是显式假设（`hab` 由调用方给出；`hst` 由"存在目标路径且 a 的计数为 1 ⟹ 路径长 ≥ 1 ⟹ s ≠ t"推出，见 `ConcreteDeterminant.lean:52-59`）。若 A 或 B 退化为自环（`s(v,v) ∉ 简单图的边集`），其计数恒为 0，等价于"无目标路径 ⟹ −1"，与 editorial 的"无解"结论一致，但**未作为单独分支形式化**。

---

## 6. 范围外、**未**形式化的内容（重要）

以下内容在 editorial 中承担实质作用，但**不在**本 Lean 工程中（README 已明确声明）：

1. **平面网格 → 对偶图的对应**（editorial 前两节）：不可通行处视为墙、X/Y 边界合并、内部交点、对偶边的定义。
2. **收缩已有墙**（并查集）与"X,Y 已同点 ⟹ 直接输出 −1"。
3. **自环与重边化简**：普通门自环删除、A/B 变自环 ⟹ 无解、同端点对重边合并、普通门与特殊门平行 ⟹ 只留特殊门、A 与 B 互相平行 ⟹ 无解。工程输入按 README 约定是"已收缩的**简单**图 + 两条不同特殊边"。
4. **原题答案本身**：`min |F| = d* − 2`，以及反方向"给定目标简单路径可构造大小 `d*−2` 的合法 F"。`Basic.lean` 只证明了单向的 `valid_has_target_path`：`Valid F ⟹ 存在同时使用 a、b 的简单 s→t 路径`，且**没有**把它与 `|F|` 的数量关系（`|P| ≤ |F| + 2`）联系起来。全仓 grep 确认源码中不存在 `−2`、`answer`、`minimum`、`grid` 等表述。
5. **随机有限域求值**：F\_{2^64} 的表示与不可约多项式 `z^64 + z^4 + z^3 + z + 1`、无进位乘法、以及判零概率界 `≤ (V−1)/2^64`。
6. **算法与复杂度**：DP 的具体实现、`O(V(V+E))` / `O(N^4)` / `O(N^2)` 的界。
7. **样例验证**：`problem.md` 的样例输入/输出（`0, −1, 0, 3, −1, 7`）无法在本工程内验证。

因此，"这个工程是否形式化了**整题**"的答案是**否**；但 README 第 77–80 行已坦然声明这一点，属于**范围界定**，不是隐藏的漏洞。

---

## 7. 次要观察与清理建议（不影响正确性）

1. **重复定义**：`WalkSum.walkSum` / `pathSum`（把 `G s t` 作显式参数）与 `Shortest.walkSum'` / `pathSum'` 内容同一，可合并。
2. **未被主链引用的引理**：`Determinant.resolvent_cofactor`、`Determinant.marked_determinant_coeff_one` 仅彼此引用（`det_add_directed_edge` 亦只服务于这两者）。
3. **模块职责**：`Shortest.lean` 混合了两条路线的接口并导入 `Contraction`（见 §4）。
4. **接口不一致**：`walkSum_X_eq_zero_of_no_target_path_determinant` 需要额外假设 `hst : s ≠ t`，而回文路线的同名定理不需要；可考虑统一。
5. **116 条 lint 告警**（`unusedSectionVars`、`if_pos`/`if_neg` 已弃用、未使用 `simp` 参数、`try this`）可清理。
6. `Basic.lean` 的 `Valid` 未约束 `F` 只含门对应的边（若 `F` 含对角元素 `s(v,v)`，`fromEdgeSet` 会静默忽略）；不影响所证定理，但作为建模接口值得记录。
7. **审计自身的边界**：本次核验覆盖"可编译 + 公理干净 + 陈述与 editorial 逐条比对 + 独立性 grep"。未对每个证明项做逐行人工复核（Lean 内核已保证其正确性，前提是 §1 的无 `sorry`/无自定义公理核验成立，而该核验已通过 `#print axioms` 独立确认）。

---

## 8. 文件清单

| 模块 | 行数 | 归属 |
|---|---|---|
| `Basic.lean` | 75 | 归约后的模型 + `Valid` + `valid_has_target_path` |
| `WalkSum.lean` | 239 | 证明一：权和、回文段奇偶、翻转、特征 2 抵消 |
| `Palindrome.lean` | 1091 | 证明一：扫描、区间反转、翻转对合 |
| `Contraction.lean` | 241 | 证明一：回文段收缩、更短目标路径 |
| `Shortest.lean` | 282 | 公共：首非零层接口（两条路线共用） |
| `Weights.lean` | 178 | 公共：路径由边多重集唯一、最短层非零 |
| `Marked.lean` | 196 | 证明二：α,β 标记与系数提取 |
| `MatrixWalk.lean` | 102 | 证明二：`M^d` 枚举定长游走 |
| `MatrixSeries.lean` | 68 | 证明二：形式矩阵几何级数 |
| `Determinant.lean` | 206 | 证明二：特征 2 行列式、伴随矩阵、y-标记 |
| `DeterminantMatching.lean` | 208 | 证明二：分母 = 普通边行列式 |
| `DeterminantGenerating.lean` | 89 | 证明二：生成恒等式 |
| `DeterminantPaths.lean` | 74 | 证明二：σt=s 的循环形状 |
| `PathComplement.lean` | 324 | 证明二：路径/补集排列双射 |
| `FintypePath.lean` | 46 | 证明二：路径列表的有限编码 |
| `PermutationTerms.lean` | 202 | 证明二：单项式分解与求和 |
| `CofactorPaths.lean` | 90 | 证明二：余子式路径展开 |
| `PathCycleWeights.lean` | 183 | 证明二：路径循环权重 |
| `ComplementDenominator.lean` | 159 | 证明二：补集分母不含标记 |
| `DeterminantPathExpansion.lean` | 714 | 证明二：最终展开与系数比较 |
| `ConcreteDeterminant.lean` | 117 | 证明二：具体证书与主线定理 |
| **合计** | **4884** | |
