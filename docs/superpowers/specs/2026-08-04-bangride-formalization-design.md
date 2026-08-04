# Bang-Ride Theorem 5.1 核心的 Lean 零 axiom 形式化 — 设计文档

- 日期：2026-08-04
- 来源论文：Shi, Sass, Wu, Kim, Ma, Shin, Findeisen, Braatz, *Bang-Ride Optimal Control: Monotonicity, External Positivity, and Fast Battery Charging*, arXiv:2508.09010v3 (2025-09-16)
- 目标：用 Lean 4.32.2 + Mathlib v4.32.2 **零 axiom** 形式化 Theorem 5.1 的证明核心（协态动力学的外部正性），并验证/修正其证明引理
- 用户目标：最大化能力展示（形式化验证 + 对最优控制理论的理解），独立项目，可单独推 GitHub

## 1. 数学背景（论文摘要）

论文考虑标量输入最优控制问题 (2)：`min ∫₀^tf l(x)dt + φ(x(tf))`，约束 `s(x,u) ≤ 0, h(x) ≤ 0, z(x(tf)) ≥ 0`。Theorem 5.1 针对线性系统

```
ẋ = diag(a₁,…,aₙ)x + 1_{n×1}u          (26)
```

在 Assumptions 2.1, 3.3a, 3.4, 5.1 下证明切换函数 `ψ(t) = 1ᵀλ(t) = Σλₖ(t) > 0`（外部正性），从而 `u*(t) = max D(x*(t))` 且轨迹 bang-ride。

形式化范围：**Theorem 5.1 的新数学核心**——协态动力学

```
λ̇ₖ = -aₖλₖ + pₖ*[t]·ψ(t),   λₖ(tf) = λ₀ₖ   (45)
ψ(t) := 1ᵀλ(t)
```

的外部正性结论 `ψ(t) > 0 ∀ t ∈ [0,tf]`。PMP 部分（ψ ≥ 0 的推导、u = max D 的桥接）作为文档化边界，不形式化。

## 2. 假设束（Theorem51Assumptions，全部显式，零 axiom）

给定：`n`, `a : Fin n → ℝ`, `λ₀ : Fin n → ℝ`（终端协态）, `p : ℝ → Fin n → ℝ`（相对灵敏度）, `ψ : ℝ → ℝ`（切换函数）, `λ : ℝ → Fin n → ℝ`（协态轨迹）, `tf : ℝ`。

| 字段 | 陈述 | 论文出处 |
|---|---|---|
| `h51a` | `∃ j₁ j₂ : Fin n, λ₀ j₁ > λ₀ j₂ ∧ a j₁ > a j₂` | Assumption 5.1(a) |
| `h51b` | `∀ k j, λ₀ k ≥ λ₀ j → a k ≥ a j` | Assumption 5.1(b)（同向排序） |
| `h51c` | `∀ k j, λ₀ k ≥ λ₀ j → ∀ s, p s k ≤ p s j` | Assumption 5.1(c)(ii) |
| `hpsi` | `∀ t, ψ t = ∑ k, λ t k` | 定义 ψ := 1ᵀλ |
| `hpsi_nonneg` | `∀ t, ψ t ≥ 0` | PMP (8a)+(42) 引出的边界假设 |
| `hλ_ode` | `∀ k, ∀ t, HasDerivAt (λ · k) (-a k · λ t k + p t k · ψ t) t` | 式 (45)，PMP (8b) 边界 |
| `hλ_terminal` | `∀ k, λ tf k = λ₀ k` | 终值条件 |
| `hcont` | `p`、`ψ` 连续性（σ-可积/连续可微所需的正则性） | Assumption 2.1 (C¹) |
| `htf` | `0 < tf` | 时间轴非退化 |

> **符号精确性说明**：5.1(b) 的方向 `λ₀ₖ ≥ λ₀ⱼ → aₖ ≥ aⱼ`（同向，而非 OCR 曾疑的反向）已从 arXiv HTML 的 LaTeXML TeX 注解中核实（`a_{k}\geqslant a_{j}` / `λ_{k}(t_{f}^{-})\geqslant λ_{j}(t_{f}^{-})`）。

## 3. 主定理

```
theorem externallyPositive
  (A : Theorem51Assumptions) (hsgn : ∀ s k, 0 ≤ p s k) :
  ∀ t, t ∈ Icc 0 tf → 0 < ψ t
```

`hsgn`（p ≥ 0）是**修正后的附加假设**（见 §5 发现 2）；原论文 Theorem 5.1 未声明，但其证明（附录 E 的积分不等式比较）隐含需要。电池应用例（式 (37)：∂V/∂I > 0, ∂V/∂x > 0 ⟹ p > 0）满足此条件，已核实。

结论 `∀ t, ψ t > 0` 由以下三段组合得到：
1. 假设束保证 `ψ ≥ 0` 处处；
2. 主矛盾论证证明 `ψ` 在任何非空开区间上不恒为零；
3. `ψ` 连续（由 (46) 与 hcont 导出）⟹ 处处 > 0。

## 4. 证明分解（零 axiom 链）

### L1 — Chebyshev 求和不等式（`Chebyshev.lean`，纯代数，通用可复用）

```
theorem chebyshev_sum
  {n : ℕ} (a b : Fin n → ℝ)
  (hsame : ∀ i j, (a i - a j) * (b i - b j) ≥ 0) :
  (n : ℝ) * (∑ i, a i * b i) ≥ (∑ i, a i) * (∑ i, b i)

theorem chebyshev_sum_strict
  (hsame : ∀ i j, (a i - a j) * (b i - b j) ≥ 0)
  (hstrict : ∃ i j, (a i - a j) * (b i - b j) > 0) :
  (n : ℝ) * (∑ i, a i * b i) > (∑ i, a i) * (∑ i, b i)
```

证明：展开 `∑ᵢ ∑ⱼ (aᵢ-aⱼ)(bᵢ-bⱼ) = 2n·Σaᵢbᵢ - 2(Σaᵢ)(Σbᵢ)`（Finset 求和换序/分配律），各项 ≥ 0 ⟹ 结论；严格版用 Finset.sum_pos（正项存在且其余非负）。

推论（主定理用法）：
```
theorem chebyshev_zero_sum {n : ℕ} (a b : Fin n → ℝ)
  (hsame : ∀ i j, (a i - a j) * (b i - b j) ≥ 0)
  (hzero : ∑ i, b i = 0)
  (hstrict : ∃ i j, (a i - a j) * (b i - b j) > 0) :
  0 < ∑ i, a i * b i
```

注意 `h51b` 单向蕴含加上 k/j 对调即可推出 `∀ i j, (λ₀ i - λ₀ j) * (a i - a j) ≥ 0`（对 λ₀ 与 a 成立）；在时间 t 处由序保持（L3）把排序从 tf 传递过来。

### L2 — 变分常数公式（`VariationOfConstants.lean`，分析层）

```
theorem variation_of_constants
  {aₖ : ℝ} {λ0 : ℝ} (pψ : ℝ → ℝ) (λ : ℝ → ℝ)
  (hλ : ∀ t, HasDerivAt λ (-aₖ * λ t + pψ t) t)
  (hλt : λ tf = λ0) ... :
  ∀ t, t ∈ Icc 0 tf →
    λ t = Real.exp (-aₖ * (tf - t)) * λ0
          + ∫ s in t..tf, Real.exp (-aₖ * (tf - s)) * pψ s ds
```

证明路径：`d/ds (e^{aₖs}·λ(s)) = e^{aₖs}·pψ(s)`（HasDerivAt 链式法则 + exp 导数 + mul 导数），两端在 [t, tf] 上取 intervalIntegral（FTC：`intervalIntegral.integral_deriv_eq_sub` 类引理），整理得公式。需要可积性假设（hcont 提供）。

### L3 — 序保持（`OrderPreservation.lean`，修正版）

论文附录 E 声称（原引理）：`λₖ(tf) ≥ λⱼ(tf) ⟹ λₖ(t) ≥ λⱼ(t) ∀ t ≤ tf`。

**形式化结论**：
- 定理 A（反例，认证论文原引理为假）：n=2, a=(5,-1), λ₀=(100,1), p≡0, tf=2 满足假设束全部字段 + ψ ≥ 0，但 `¬ (λ₁(1.2) ≥ λ₂(1.2))`。数值：λ₁(1.2) = 100e^{-4} ≈ 1.83，λ₂(1.2) = e^{0.8} ≈ 2.23。
- 定理 B（修正版，附加假设下为真）：在 `h51b`、`h51c`、`p ≥ 0`、`ψ ≥ 0` 及符号条件 `horder` 下：

```
horder : ∀ k j, λ₀ k ≥ λ₀ j → a k = a j ∨ λ₀ j ≤ 0
```

  候选刻画（手工推演得出，实现阶段核实）：序保持失败恰发生在 `0 < λ₀ⱼ ≤ λ₀ₖ` 且 `aₖ > aⱼ`、时间间隔足够长时（指数衰减拉开差距）；`λ₀ₖ = λ₀ⱼ` 由 h51b 双向蕴含强制 `aₖ = aⱼ` 从而平凡成立。此条件排除之。电池应用例 λ₀ = (1,0,…,0)：对 (1,j) 有 λ₀ⱼ = 0 ≤ 0 ✓，对 (j,i)（j ≥ 2）有 a 与 λ₀ 全相等或平凡 ✓，满足候选条件。混合符号情形（λ₀ⱼ ≤ 0 ≤ λ₀ₖ）中积分项符号（pₖ ≤ pⱼ 使积分差 ≤ 0）在实现中进一步核实。

### L4 — 外部正性主定理（`ExternalPositivity.lean`）

```
theorem externallyPositive (A : Theorem51Assumptions)
  (hsgn : ∀ s k, 0 ≤ p s k) (horder : 序保持符号条件, 见 §4 定理 B 候选刻画) :
  ∀ t, t ∈ Icc 0 tf → 0 < ψ t
```

三步：
1. 反证：∃ (t₁,t₂) ⊆ [0,tf]，ψ ≡ 0 于 (t₁,t₂)。
2. ψ̇ ≡ 0 ⟹ (47) `0 = -Σaᵢλᵢ(t)`（ψ̇ = Σλ̇ₖ = -Σaₖλₖ + ψΣpₖ = -Σaₖλₖ）。此步只用 ODE (45)，不用 (46)。
3. 序保持 + 5.1b ⟹ λ(t) 与 a 同向排序 ⟹ Chebyshev 严格版 + Σλᵢ(t) = ψ(t) = 0 ⟹ `0 < Σaᵢλᵢ(t)`，与 (47) 矛盾。
4. ψ ≥ 0 连续且无零区间 ⟹ ψ > 0 处处（若 ψ(t₀)=0 且连续，则邻域上恒为零，矛盾）。

## 5. 预期发现（Lean 将机器证实）

1. **论文附录 E 序保持引理在 Assumption 5.1 原假设下为假**（§4 定理 A 的反例）。这是给作者团队的勘误级发现。
2. **主定理证明需要附加条件**：p ≥ 0（相对灵敏度非负）或等价符号条件。论文 §5 声称"不限制 ∂s̃ᵢ/∂x 的符号"，但其证明隐含要求；电池应用例恰好满足（式 (37) 全正）。
3. 处理策略：反例作为独立定理 + 修正版定理 + VERIFICATION.md 报告"论文证明隐含假设 + 电池实例核实"。

## 6. PMP 边界（不形式化，文档化）

- `ψ ≥ 0`：由 PMP 式 (8a) 与 (42)（μ ≤ 0, s̃_u > 0 ⟹ ψ ≥ 0）导出 → 作为假设束字段 `hpsi_nonneg`，来源文档化。
- "ψ > 0 ⟹ u*(t) = max D(x*(t)) ⟹ bang-ride"：论文 Lemma 4.1，Hamiltonian 极大化（式 (8a)）的推论 → 不形式化，VERIFICATION.md 记为已文档化边界。
- 协态 ODE (45) 与终值 λ(tf) = λ₀：来自 PMP (8b)/(9a) → 作为假设束字段。
- 相对灵敏度 p 的定义 (27)：p = [s̃_u]^{-1}·s̃_x 只进入序/符号假设（5.1c、hsgn），其定义本身不形式化。

## 7. 文件与文档

```
BangRide/Core.lean                — 假设束 structure、常用引理
BangRide/Chebyshev.lean           — L1（通用，可独立复用）
BangRide/VariationOfConstants.lean — L2
BangRide/OrderPreservation.lean   — L3（定理 A 反例 + 定理 B 修正版）
BangRide/ExternalPositivity.lean  — L4 主定理
docs/formula-mapping.md           — 论文公式 ↔ Lean 定理对照表（沿用惯例）
docs/VERIFICATION.md              — 验证报告：范围/假设/发现（反例 + 隐含假设）
docs/lean-work-notes.md           — 执行记录与 Mathlib 坑
README.md                         — 项目说明与复现命令
```

## 8. 复现与发布

```bash
export ELAN_HOME="D:/AI/lean/elan"
lake build   # 目标：全绿，零 sorry，零 axiom
```

- GitHub：新公开仓库（沿用用户既有模式：waitstonelove-crypto 系列，仓库名 `bang-ride-lean-verification` 候选）。
- 验证报告完成后，反例与修正可整理为给作者团队的正式勘误材料（用户决定是否发出）。

## 9. 成功标准

1. `lake build` 全绿；`#check` 无 `sorry`；`#print axioms` 为空（零 axiom）。
2. Chebyshev（含严格版）、变分常数 (46)、序保持反例（定理 A）、修正版序保持（定理 B）、外部正性主定理全部落盘。
3. docs/formula-mapping.md 覆盖 §2-§3 全部对应关系；VERIFICATION.md 记录发现 1-2。
4. 项目推至 GitHub（公开）。
