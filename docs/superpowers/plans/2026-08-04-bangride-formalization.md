# Bang-Ride Theorem 5.1 核心 Lean 零 axiom 形式化 — 实现计划

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 用 Lean 4.32.2 + Mathlib 零 axiom 形式化 arXiv:2508.09010 的 Theorem 5.1 证明核心：Chebyshev 求和不等式、协态线性 ODE 变分常数公式、序保持引理（反例 + 修正版）、外部正性主定理 ψ(t) > 0。

**Architecture:** 五个源文件（Core → Chebyshev → VariationOfConstants → OrderPreservation → ExternalPositivity），依赖单向无环；核心数学用 Fin 索引标量函数表达（不用矩阵 API，规避 Mathlib v4.32.2 矩阵坑）；PMP 边界（ψ ≥ 0、ODE (45)、终值）作为 Assumptions 结构体的显式假设字段，最终 `#print axioms` 为空。构建用 `lake build` + mathlib 预编译缓存。

**Tech Stack:** Lean 4.32.2（`D:\AI\lean\elan`，ELAN_HOME=D:/AI/lean/elan）、Mathlib v4.32.2、lake 构建、git。

**项目位置：`D:\AI\lean\projects\bangride`**（2026-08-04 会话重建，无历史包袱）。

**环境事实（必须遵守）：**
- 所有命令在 bash 下运行；`export ELAN_HOME="D:/AI/lean/elan"` 后使用 `lake build` / `lake env lean`
- 构建前先 `lake exe cache get` 拉 Mathlib v4.32.2 预编译 olean（避免全量编译）
- Mathlib v4.32.2 已知坑：标识符禁止 `*`/`λ`；`½` 解析失败用 `(1/2)`；矩阵缩写 `Mat` 不可用（本计划不用矩阵）；Lean 证明子代理输出上限已设 `CLAUDE_CODE_MAX_OUTPUT_TOKENS=64000`
- 提交信息用中文，风格：`docs: ...` / `feat: ...`

---

### Task 1: 项目初始化与构建链验证

**Files:**
- Create: `BangRide/Core.lean`（最小骨架，仅 namespace + trivial 定理，验证工具链）

- [ ] **Step 1: 下载 Mathlib 预编译缓存并首次构建**

```bash
cd /d/AI/lean/projects/bangride
export ELAN_HOME="D:/AI/lean/elan"
lake exe cache get
```
Expected: 输出下载若干 mathlib olean 包（无错误）。若 `cache` 子命令不存在，回退为直接 `lake build`（首次构建 mathlib 可能 30-60 分钟，放后台）。

- [ ] **Step 2: 写最小 Core.lean 骨架**（已完成：仅 `smoke_test : True := by trivial`）

- [ ] **Step 3: 构建验证**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 构建成功（无错误输出，exit code 0）。

- [ ] **Step 4: 初始化 git 并提交**

```bash
cd /d/AI/lean/projects/bangride && git init -b main && git add -A && git commit -m "chore: 项目骨架与工具链验证（lake + mathlib v4.32.2 缓存）"
```
（规格文档与实现计划已随本提交入库；后续实现全部在 `feat/bangride-formalization` 分支上进行）

---

### Task 2: Core.lean — 数据与假设束结构

**Files:**
- Modify: `BangRide/Core.lean`

- [ ] **Step 1: 写 Data / Assumptions 结构（替换 smoke_test 占位）**

```lean
import Mathlib

noncomputable section
open scoped BigOperators

namespace BangRide

/-- Theorem 5.1 的数据：系统参数与轨迹（论文 (26)(45)(46)） -/
structure Data (n : ℕ) where
  tf : ℝ
  a : Fin n → ℝ          -- 对角系统 diag(a₁,…,aₙ) 的对角元
  lam0 : Fin n → ℝ       -- 终端协态 λ(tf⁻)
  p : ℝ → Fin n → ℝ      -- 相对灵敏度 pₖ[t]（论文 (27)）
  psi : ℝ → ℝ            -- 切换函数 ψ(t) = 1ᵀλ(t)
  lam : ℝ → Fin n → ℝ    -- 协态轨迹

namespace Data
variable {n : ℕ} (D : Data n)

/-- Assumption 5.1 + 正则性假设束（Theorem 5.1 核心的形式化前提） -/
structure Assumptions (D : Data n) : Prop where
  htf : 0 < D.tf
  h51a : ∃ j₁ j₂ : Fin n, D.lam0 j₁ > D.lam0 j₂ ∧ D.a j₁ > D.a j₂
  h51b : ∀ k j : Fin n, D.lam0 k ≥ D.lam0 j → D.a k ≥ D.a j
  h51c : ∀ k j : Fin n, D.lam0 k ≥ D.lam0 j → ∀ s, D.p s k ≤ D.p s j
  hpsi_eq : ∀ t, D.psi t = ∑ k, D.lam t k
  hpsi_nonneg : ∀ t, D.psi t ≥ 0
  hp_cont : ∀ k, Continuous (fun s : ℝ => D.p s k)
  hpsi_cont : Continuous D.psi
  hlam_terminal : ∀ k, D.lam D.tf k = D.lam0 k
  hlam_ode : ∀ k, ∀ t,
    HasDerivAt (fun s : ℝ => D.lam s k) (-D.a k * D.lam t k + D.p t k * D.psi t) t

end Data
end BangRide
```

- [ ] **Step 2: 构建验证**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 构建成功。

- [ ] **Step 3: 提交**

```bash
git add -A && git commit -m "feat: Core 数据与 Assumption 5.1 假设束结构"
```

---

### Task 3: Chebyshev.lean — Chebyshev 求和不等式（通用代数层）

**Files:**
- Create: `BangRide/Chebyshev.lean`（import Mathlib，独立于 Core 可复用）

- [ ] **Step 1: 写三个定理陈述（先留证明骨架，构建确认陈述类型正确）**

```lean
import Mathlib

noncomputable section
open scoped BigOperators

namespace BangRide

/-- 同向排序序列的 Chebyshev 求和不等式：n·Σaᵢbᵢ ≥ (Σaᵢ)(Σbᵢ) -/
theorem chebyshev_sum {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0) :
    (n : ℝ) * (∑ i, a i * b i) ≥ (∑ i, a i) * (∑ i, b i) := by
  -- 核心：展开 ∑ᵢ∑ⱼ (aᵢ-aⱼ)(bᵢ-bⱼ) = 2n·Σaᵢbᵢ - 2(Σaᵢ)(Σbᵢ)，各项 ≥ 0
  have hnonneg : (0 : ℝ) ≤ ∑ i, ∑ j, (a i - a j) * (b i - b j) := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hsame i j
  have hid :
      (∑ i, ∑ j, (a i - a j) * (b i - b j))
        = 2 * (n : ℝ) * (∑ i, a i * b i) - 2 * (∑ i, a i) * (∑ i, b i) := by
    -- 用 Finset.sum_congr 逐项 ring 展开被加项，
    -- 再 simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    --   Finset.sum_mul, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul] 后 ring_nf
    -- 注意 ∑ j, b j 与 ∑ i, b i 的换名：用 Finset.sum_congr rfl (by intro; rfl) 或 simp [Finset.sum_comm]
    sorry
  nlinarith

/-- 严格版：存在严格同向对 ⟹ 严格不等式 -/
theorem chebyshev_sum_strict {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0)
    (hstrict : ∃ i j : Fin n, (a i - a j) * (b i - b j) > 0) :
    (n : ℝ) * (∑ i, a i * b i) > (∑ i, a i) * (∑ i, b i) := by
  -- 同上 hid，但 hnonneg 换为严格：Finset.sum_pos（每项 ≥ 0 且至少一项 > 0）
  -- 结构：先证 ∑ᵢ∑ⱼ (aᵢ-aⱼ)(bᵢ-bⱼ) > 0，再代入 hid，nlinarith
  sorry

/-- 推论：Σbᵢ = 0 时（主定理用法），Σaᵢbᵢ > 0 -/
theorem chebyshev_zero_sum {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0)
    (hzero : (∑ i, b i) = 0)
    (hstrict : ∃ i j : Fin n, (a i - a j) * (b i - b j) > 0) :
    0 < ∑ i, a i * b i := by
  -- 由 chebyshev_sum_strict：n·Σaᵢbᵢ > (Σaᵢ)·0 = 0；再除以 n（n > 0 需证明：Fin n 非空 ⟹ n ≥ 1，
  -- 用 nlinarith + 指数分解：n = |univ|，或直接 cases n）
  sorry

end BangRide
```

> **注意**：`sorry` 仅作开发期占位。本任务结束时**必须全部替换为完整证明**（零 sorry 是验收标准）。`hid` 的证明是本节唯一难点，迭代要点：
> 1. `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))` 展开被加项；
> 2. `simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]` 摊开二重和；
> 3. 末尾 `ring_nf` 或 `nlinarith` 合并项；`∑ j, b j` 与 `∑ i, b i` 换名用 `simpa [Finset.sum_comm]` 或 `rw [← Finset.sum_comm]`；
> 4. `chebyshev_zero_sum` 中"n > 0"：`n` 在 Fin 索引下至少为 1；若 `n = 0` 则 `Fin 0` 为空、h51a 无从给出（本定理单独使用时直接 `cases n`；n=0 时 `∑ i, b i` 为空和 = 0 与 hzero 平凡成立，但 hstrict 不可能成立 ⟹ 用 hstrict 消除该分支）。
> 5. 若 `sorry` 在单步迭代中卡住超过两轮，将 `hid` 拆为独立 `lemma` 分步证明并分别提交。

- [ ] **Step 2: 构建确认陈述可类型检查**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 三个定理的陈述部分类型检查通过（仅 sorry 警告）。

- [ ] **Step 3: 逐个补全证明（chebyshev_sum → chebyshev_sum_strict → chebyshev_zero_sum），每完成一个跑一次**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 全部通过，无 sorry、无 `warning: declaration uses 'sorry'`。

- [ ] **Step 4: 提交**

```bash
git add -A && git commit -m "feat: Chebyshev 求和不等式（含严格版与零和推论），零 sorry"
```

---

### Task 4: VariationOfConstants.lean — 变分常数公式 (46)

**Files:**
- Create: `BangRide/VariationOfConstants.lean`（import Mathlib + Core）

- [ ] **Step 1: 写前向形式（论文式 (46)）与后向形式**

```lean
import Mathlib
import BangRide.Core

noncomputable section
open scoped BigOperators

namespace BangRide

/-- 论文式 (46) 前向形式：λₖ(tf) = e^{-aₖ(tf-t)}λₖ(t) + ∫ₜ^{tf} e^{-aₖ(tf-τ)} pₖ[τ] ψ(τ) dτ
    由 ODE (45) λ̇ₖ = -aₖλₖ + pₖψ 与终值 λₖ(tf) = λ₀ₖ 经 FTC 推出（零 axiom） -/
theorem variation_of_constants_forward {n : ℕ} {D : Data n} (A : D.Assumptions) {k : Fin n} :
    ∀ t, t ∈ Set.Icc 0 D.tf →
      D.lam D.tf k = Real.exp (-D.a k * (D.tf - t)) * D.lam t k
        + ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ) dτ := by
  -- 证明路径（完整骨架）：
  -- 1) 定义 h(s) = exp(-aₖ(tf-s)) * lam s k
  -- 2) 证 ∀ s, HasDerivAt h (exp(-aₖ(tf-s)) * (p s k * psi s)) s：
  --    · hasDerivAt_exp + 链式：d/ds exp(-aₖ(tf-s)) = aₖ·exp(-aₖ(tf-s))
  --      （用 HasDerivAt.comp / HasDerivAt.mul_const 等，方向：(-aₖ(tf-s))' = aₖ）
  --    · HasDerivAt.mul h 的导数两项相消：aₖλₖ 项与 ODE 的 -aₖλₖ 项抵消，ring
  --    · 用 A.hlam_ode k
  -- 3) intervalIntegral.integral_deriv_eq_sub：
  --    ∫ s in t..D.tf, exp(-aₖ(tf-s)) * (p s k * psi s) ds = h D.tf - h t
  --    · 连续性：ContinuousOn —— 由 A.hp_cont、A.hpsi_cont 与 h 的连续（HasDerivAt.continuousAt）推出
  --    · 导数条件：步骤 2 的结果（限 Ioo）
  -- 4) h D.tf = lam D.tf k（exp 0 = 1，simp [A.hlam_terminal]），h t = exp(-aₖ(tf-t))·lam t k
  -- 5) ring 重排：lam D.tf k = exp(-aₖ(tf-t))·lam t k + ∫ …，得证
  sorry

/-- 后向形式（推导序保持引理时的辅助）：λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ - ∫ₜ^{tf} e^{aₖ(τ-t)} pₖ[τ] ψ(τ) dτ -/
theorem variation_of_constants_backward {n : ℕ} {D : Data n} (A : D.Assumptions) {k : Fin n} :
    ∀ t, t ∈ Set.Icc 0 D.tf →
      D.lam t k = Real.exp (D.a k * (D.tf - t)) * D.lam0 k
        - ∫ τ in t..D.tf, Real.exp (D.a k * (τ - t)) * (D.p τ k * D.psi τ) dτ := by
  -- 两种路径任选：
  -- (a) 与 forward 对称：h'(s) = exp(aₖs)·lam s k，∫ₜ^{tf} exp(aₖs)(p s k·psi s) = h'(tf) - h'(t)，
  --     再乘 exp(-aₖt) 重排；
  -- (b) 从 variation_of_constants_forward 代数推出：
  --     用 exp_add / exp_sub / exp_neg 与积分常数提取 ∫ c·f = c·∫ f（intervalIntegral.integral_const_mul），
  --     mul_eq_mul_left_iff 配合 exp_pos 消去 exp 因子，ring
  sorry

end BangRide
```

- [ ] **Step 2: 构建确认陈述类型检查**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 陈述通过，仅 sorry 警告。

- [ ] **Step 3: 补全 forward 证明**

关键引理提示（Mathlib v4.32.2）：
- `Real.exp_zero`, `Real.exp_add`, `Real.exp_sub`, `Real.exp_neg`, `Real.exp_nat_mul`
- `intervalIntegral.integral_deriv_eq_sub`（需要 `ContinuousOn f (Icc (min a b) (max a b))` + `∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x`，结论 `∫ x in a..b, f' x = f b - f a`）
- `HasDerivAt.continuousAt`, `Continuous.continuousOn`, `continuousOn_of_continuousAt` 类
- 积分常数提取：`intervalIntegral.integral_const_mul` / `intervalIntegral.integral_mul_const`
- `Real.exp_pos`（用于消因子）

预期迭代 1-3 轮。若 `integral_deriv_eq_sub` 的条件构造繁琐，替代：用 `intervalIntegral.integral_eq_sub_of_hasDerivAt`（存在版本）或先证 `∀ t ∈ Icc, HasDerivAt ... ` 再 `intervalIntegral.integral_deriv_eq_sub'`（若存在）。**每轮改动后跑 `lake build`。**

- [ ] **Step 4: 补全 backward 证明（推荐路径 (b)：从 forward 代数推出）**

要点：forward 给出 `λₖ(tf) = e^{-aₖ(tf-t)}λₖ(t) + ∫ₜ^{tf} e^{-aₖ(tf-τ)}pₖψ`；两边乘 `e^{aₖ(tf-t)}`（exp_add 展开 `e^{aₖ(tf-t)}·e^{-aₖ(tf-τ)} = e^{aₖ(τ-t)}`），得 `λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ - ∫ₜ^{tf} e^{aₖ(τ-t)}pₖψ`。全程 `ring_nf` + `rw [← intervalIntegral.integral_const_mul]`（把 `e^{aₖ(tf-t)}` 提出积分号——注意方向）。

- [ ] **Step 5: 零 sorry 验收 + 提交**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 全绿无 sorry。然后：

```bash
git add -A && git commit -m "feat: 变分常数公式 (46) 前向/后向形式，FTC 零 axiom 证明"
```

---

### Task 5: OrderPreservation.lean — 序保持：反例（定理 A）+ 修正版（定理 B）

**Files:**
- Create: `BangRide/OrderPreservation.lean`（import Core, VariationOfConstants）

- [ ] **Step 1: 写定理 A（论文原序保持引理的认证反例）**

```lean
import Mathlib
import BangRide.Core
import BangRide.VariationOfConstants

noncomputable section
open scoped BigOperators

namespace BangRide

/-- 反例实例：n=2, a=(5,-1), λ₀=(100,1), p≡0, tf=2
    λ₀(t) = 100e^{-5(2-t)}, λ₁(t) = e^{2-t}（满足 ODE (45) 与终值） -/
def counterexample : Data 2 where
  tf := 2
  a := ![5, -1]
  lam0 := ![100, 1]
  p := fun _ _ => 0
  psi := fun t => 100 * Real.exp (-5 * (2 - t)) + Real.exp (2 - t)
  lam := fun t k => if k = 0 then 100 * Real.exp (-5 * (2 - t)) else Real.exp (2 - t)

/-- 反例满足全部假设束字段（各假设逐项验证，见 Step 2） -/
theorem counterexample_assumptions : (counterexample : Data 2).Assumptions := by
  -- 分字段构造记录：
  -- · htf：norm_num
  -- · h51a：提供 j₁=0, j₂=1，norm_num [counterexample]（100 > 1 ∧ 5 > -1）
  -- · h51b：cases 4 个 (k,j) 组合，simp [counterexample] at *，omega/nlinarith
  --   （对：λ₀ = (100,1)：100 ≥ 1 → 5 ≥ -1 ✓；其余组合前提为假或平凡）
  -- · h51c：p ≡ 0 ⟹ 0 ≤ 0，simp [counterexample]
  -- · hpsi_eq：simp [counterexample, Fin.sum_univ_two, Finset.sum_insert] 展开两元求和
  -- · hpsi_nonneg：两指数项均 > 0（Real.exp_pos）⟹ 和 > 0，nlinarith
  -- · hp_cont：const 函数连续，exact continuous_const
  -- · hpsi_cont：指数 + 加法连续，exact (Real.continuous_exp.comp ...).add (Real.continuous_exp.comp ...) 或 continuity
  -- · hlam_terminal：simp [counterexample]
  -- · hlam_ode：逐 k：
  --   · k=0：d/dt(100e^{-5(2-t)}) = 500e^{-5(2-t)} = -5·λ₀(t)（hasDerivAt_exp 链式，ring）
  --   · k=1：d/dt(e^{2-t}) = -e^{2-t} = -(-1)·λ₁(t)（同法）
  sorry

/-- 定理 A：论文"λₖ(tf) ≥ λⱼ(tf) ⟹ λₖ(t) ≥ λⱼ(t)"在 5.1 原假设下为假。
    具体：t=1 处 λ₀(1) < λ₁(1)，但 λ₀₀ = 100 > 1 = λ₀₁。 -/
theorem order_preservation_counterexample :
    ∃ t, t ∈ Set.Icc 0 2 ∧ counterexample.lam t 0 < counterexample.lam t 1 := by
  -- 取 t = 1：需要 100·e^{-5} < e ⟺ 100 < e⁶
  -- 关键引理（本文件内）：e⁶ > 100
  -- 证明：Real.exp 6 = (Real.exp 1)^6（Real.exp_nat_mul / rw [show (6:ℝ) = 6 * 1 by norm_num]），
  --   Real.exp 1 ≥ 5/2（级数前 3 项：exp 1 ≥ 1 + 1 + 1/2，用 Real.exp_eq_tsum +
  --   tsum 部分和 ≤ 无穷和（sum_le_tsum 或 Finset.sum_le_tsum），norm_num），
  --   (5/2)^6 = 15625/64 > 100（norm_num）
  -- 然后：100·e^{-5} < e ⟺ 100 < e·e⁵ = e⁶（exp_add / exp_sub / exp_neg，nlinarith + exp_pos 消正因子）
  sorry

end BangRide
```

> 反例数值核对：λ₀(1) = 100e^{-5·(2-1)} = 100e^{-5} ≈ 0.67；λ₁(1) = e^{2-1} = e ≈ 2.72 ⟹ λ₀(1) < λ₁(1) ✓。ψ(t) = λ₀(t) + λ₁(t) > 0（两项均正）⟹ hpsi_nonneg ✓。5.1b 方向核对：λ₀₀=100 ≥ λ₀₁=1 ⟹ a₀=5 ≥ a₁=-1 ✓。

- [ ] **Step 2: 构建并补全定理 A 的所有字段证明（counterexample_assumptions 是主要工作量）**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
迭代要点：
- `Fin.sum_univ_two` 展开 `∑ k : Fin 2, ...`（或 `simp [Finset.sum_fin_eq_sum_range]` + `norm_num`）
- `if k = 0 then ... else ...` 的化简：`by_cases hk : k = 0 <;> simp [counterexample, hk]`
- HasDerivAt 链式：`(hasDerivAt_exp ...).comp` 或先 `fun_prop` 探路再手写
- 若 `hlam_ode` 的 `HasDerivAt` 陈述直接用 `fun_prop`/`simp` 无法解决，改证等价的 `Deriv` 形式或用 `hasDerivAt_iff_hasDerivWithinAt` + 手工链式

- [ ] **Step 3: 写定理 B（修正版序保持，条件为发现项）**

```lean
/-- 修正版序保持（候选条件 horder，见 spec §4；若某候选被反例击破，换下一个并记录）：
    假设：(i) 5.1b/c 序，(ii) p ≥ 0，(iii) ψ ≥ 0，(iv) 终端协态序条件。 -/
theorem orderPreservation {n : ℕ} {D : Data n} (A : D.Assumptions)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (horder : ∀ k j : Fin n, D.lam0 k > D.lam0 j → D.a k = D.a j ∨ D.lam0 j ≤ 0) :
    ∀ k j : Fin n, ∀ t, t ∈ Set.Icc 0 D.tf →
      D.lam0 k ≥ D.lam0 j → D.lam t k ≥ D.lam t j := by
  -- 结构（按论文附录 E + 符号条件修正）：
  -- 1) 反证：存在 t 使 lam t k < lam t j
  -- 2) 分 aₖ = aⱼ 与 λ₀ⱼ ≤ 0 两情况：
  --    · aₖ = aⱼ：由 forward 形式逐项相减：λₖ(tf)-λⱼ(tf) = e^{-aₖ(tf-t)}(λₖ(t)-λⱼ(t)) + ∫e^{-aₖ(tf-τ)}(pₖ-pⱼ)ψ
  --      （h51c 给 pₖ ≤ pⱼ，ψ ≥ 0 ⟹ 积分 ≤ 0；λₖ(tf) = λ₀ₖ ≥ λ₀ⱼ = λⱼ(tf) ⟹ 反证成立）
  --    · λ₀ⱼ ≤ 0：此分支的真实充分条件在实现中确定——
  --      候选 A：比较点 t 处 λⱼ(t) ≥ 0（需额外假设或由其他结构推出）；
  --      候选 B：直接要求 ∀ t k, 0 ≤ D.lam t k（分量非负，此时 term1 与积分均正，证明最顺）；
  --      候选 C：若 A/B 均不可行，把序保持本身声明为假设束字段（主定理改用 horder 字段），
  --      并把"候选条件反例"记入 VERIFICATION.md —— 注意：这会使零 axiom 目标降级为
  --      "核心代数全证 + 序保持为显式假设"，须在提交前与用户确认。
  -- 3) 逐项比较 forward 形式（term1 用 λₖ(t) < λⱼ(t) + 指数单调性；积分项用 pₖ ≤ pⱼ + ψ ≥ 0 + hsgn）
  -- 4) 得 λₖ(tf) < λⱼ(tf)，与 λ₀ₖ ≥ λ₀ⱼ 矛盾
  sorry
```

- [ ] **Step 4: 迭代定理 B 的条件发现**

流程：先试候选 B（`∀ t k, 0 ≤ lam t k` 作为额外参数，证明最直），`lake build`；若太强不符论文语境，试候选 A；每次迭代记录"条件 X 下证出 / 被反例击破"。**若两轮内均失败，停下与用户讨论条件形状，不擅自扩大假设束。**

- [ ] **Step 5: 零 sorry 验收 + 提交**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 全绿无 sorry。提交：

```bash
git add -A && git commit -m "feat: 序保持——论文原引理反例（定理 A）+ 修正版（定理 B）"
```

---

### Task 6: ExternalPositivity.lean — 外部正性主定理

**Files:**
- Create: `BangRide/ExternalPositivity.lean`（import Core, Chebyshev, OrderPreservation）

- [ ] **Step 1: 写主定理**

```lean
import Mathlib
import BangRide.Core
import BangRide.Chebyshev
import BangRide.OrderPreservation

noncomputable section
open scoped BigOperators

namespace BangRide

/-- 修正版 Theorem 5.1 核心：切换函数 ψ(t) = 1ᵀλ(t) > 0（外部正性），∀ t ∈ [0,tf]。
    假设：Assumption 5.1 束 + p ≥ 0 + 序保持条件（horder，与 Theorem B 一致）。 -/
theorem externallyPositive {n : ℕ} {D : Data n} (A : D.Assumptions)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (horder : 与 Theorem B 相同的序保持条件) :
    ∀ t, t ∈ Set.Icc 0 D.tf → 0 < D.psi t := by
  -- 结构：
  -- 1) 反设存在 t₀ ∈ [0,tf]，ψ(t₀) = 0。
  -- 2) 若 t₀ 为区间 (t₁,t₂) 内点：ψ ≥ 0 且 ψ(t₀) = 0 ⟹ ψ 在 t₀ 取局部极小 ⟹ ψ'(t₀) = 0
  -- 3) 由 (47) 推导：ψ'(t) = Σₖ λ̇ₖ(t) = -Σₖ aₖλₖ(t) + ψ(t)·Σₖ pₖ(t)（A.hlam_ode 线性组合 + A.hpsi_eq）
  --    ⟹ ψ(t₀)=0 ∧ ψ'(t₀)=0 ⟹ Σₖ aₖ·λₖ(t₀) = 0
  -- 4) Chebyshev 严格版（chebyshev_zero_sum）：
  --    · 同向：λ(t₀) 与 a 同向 —— 由 orderPreservation（h51b 的单向蕴含 + 对调 ⟹
  --      ∀ i j, (λ₀ᵢ-λ₀ⱼ)(aᵢ-aⱼ) ≥ 0，再经序保持传递到 t₀）
  --    · Σλₖ(t₀) = ψ(t₀) = 0（A.hpsi_eq）
  --    · 严格对：5.1a 的 (j₁,j₂) + 序保持的严格版（论文"λ_{j₁}(t) > λ_{j₂}(t)"；若严格版未证出，
  --      需在 Task 5 中补充严格序保持引理 orderPreservationStrict）
  -- 5) chebyshev_zero_sum ⟹ 0 < Σₖ aₖ·λₖ(t₀)，与步骤 3 的 = 0 矛盾 ⟹ ψ(t₀) ≠ 0 ⟹ ψ(t₀) > 0（A.hpsi_nonneg）
  -- 6) 端点 t₀ = 0 或 t₀ = tf：由 ψ 连续（A.hpsi_cont）与内点结论取极限（tendsto）延拓
  sorry
```

- [ ] **Step 2: 迭代证明**

要点提示：
- (47) 的推导：对 `A.hlam_ode` 各 k 用 `HasDerivAt.add`/`HasDerivAt.sum`（`Finset.sum` 版本的链式：`hasDerivAt_sum` 或逐项 add 后 `Finset.sum_induction`），由 A.hpsi_eq 组装出 `HasDerivAt D.psi (∑ k, (-aₖλₖ + pₖψ)) t`
- 若"内点局部极小 ⟹ 导数为零"过重，改直接路线：反设区间 (t₁,t₂) 上 ψ ≡ 0（论文原路线），在区间内取点用 (47)；再把"无零区间 + 连续 + ≥0 ⟹ 处处 > 0"作为最后一步（更接近论文结构，且避免测度论）
- 严格序保持：若需要，在 Task 5 补充 `orderPreservationStrict`（λ₀ₖ > λ₀ⱼ ⟹ λₖ(t) > λⱼ(t)），证明：若 λₖ(t) = λⱼ(t) 则 forward 相减 + aₖ > aⱼ + λ(t) ≥ 0（符号条件）⟹ λₖ(tf) < λⱼ(tf) 矛盾
- 每轮 `lake build`；卡住超两轮则退回"论文原路线"（区间反证 + 连续延拓）

- [ ] **Step 3: 零 sorry 验收 + 提交**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build
```
Expected: 全绿无 sorry。提交：

```bash
git add -A && git commit -m "feat: 外部正性主定理 externallyPositive（ψ>0 ∀t），零 sorry"
```

---

### Task 7: 文档（公式对照 / 验证报告 / 工作记录 / README）

**Files:**
- Create: `docs/formula-mapping.md`
- Create: `docs/VERIFICATION.md`
- Create: `docs/lean-work-notes.md`
- Create: `README.md`

- [ ] **Step 1: 写 docs/formula-mapping.md**

内容：论文公式/假设 ↔ Lean 定理/字段对照表，含：式 (45) ↔ `Assumptions.hlam_ode`；式 (46) ↔ `variation_of_constants_forward/backward`；Assumption 5.1(a/b/c) ↔ `h51a/h51b/h51c`；式 (47) ↔ 主定理证明中的 Σaₖλₖ = 0 引理；Chebyshev 不等式 ↔ `chebyshev_sum` 系列。表格风格参考既有惯例。

- [ ] **Step 2: 写 docs/VERIFICATION.md**

内容：验证范围（Theorem 5.1 核心，PMP 边界文档化——ψ≥0 与 ODE 为显式假设、u=max D 桥接不形式化）；**发现 1**：论文附录 E 序保持引理在原假设下为假（定理 A 反例，附数值）；**发现 2**：主定理需要附加条件（hsgn p≥0、序保持符号条件，记录最终采用的条件形状与迭代过程）；零 axiom 声明（`#print axioms` 空）；构建统计（job 数）。

- [ ] **Step 3: 写 docs/lean-work-notes.md 与 README.md**

work-notes：记录 Mathlib v4.32.2 新坑（本项目的：exp 级数界、intervalIntegral 引理名、HasDerivAt 组装）。README：项目简介 + 复现命令（`export ELAN_HOME="D:/AI/lean/elan" && lake exe cache get && lake build`）。

- [ ] **Step 4: 提交**

```bash
git add -A && git commit -m "docs: 公式对照表、验证报告（含序保持反例发现）、工作记录与 README"
```

---

### Task 8: 终验、axiom 审计与发布

**Files:**
- Verify: 全部源文件与文档

- [ ] **Step 1: 全量构建 + 零 sorry 审计**

```bash
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake build 2>&1 | grep -iE "sorry|warning|error" ; echo "exit=$?"
```
Expected: 无任何 `warning: declaration uses 'sorry'`、无 error。

- [ ] **Step 2: axiom 审计**

```bash
cat > /tmp/axiom_check.lean <<'EOF'
import BangRide.ExternalPositivity
open BangRide
#check externallyPositive
#check chebyshev_sum
#check chebyshev_sum_strict
#check chebyshev_zero_sum
#check variation_of_constants_forward
#check orderPreservation
#check order_preservation_counterexample
#print axioms externallyPositive
EOF
cd /d/AI/lean/projects/bangride && export ELAN_HOME="D:/AI/lean/elan" && lake env lean /tmp/axiom_check.lean
```
Expected: 七个 `#check` 输出类型签名；`#print axioms externallyPositive` 输出空列表或仅 Mathlib 自身基础公理（`propext`, `Classical.choice`, `Quot.sound` 等——若出现，VERIFICATION.md 说明"零 axiom"指**无自定义 axiom/sorry**）。

- [ ] **Step 3: 验证报告同步最终条件**

若实现中 horder/hsgn 与 spec §4 候选有出入（如补充了分量非负假设），同步更新 `docs/VERIFICATION.md` 与 `docs/formula-mapping.md`，再提交：

```bash
git add -A && git commit -m "docs: 终验同步（序保持最终条件与 axiom 审计结果）"
```

- [ ] **Step 4: 合并分支与 GitHub 发布（需用户确认后执行）**

```bash
cd /d/AI/lean/projects/bangride && git checkout main && git merge feat/bangride-formalization
gh repo create bang-ride-lean-verification --public --source . --push
```
Expected: 分支合并 + 仓库创建并推送。**若用户未确认，跳过推送并在总结中说明。**

---

## 自审记录（写作时完成）

**1. Spec 覆盖核对：**
- §3 主定理 → Task 6 ✓；§4 L1 Chebyshev → Task 3 ✓；L2 变分常数 → Task 4 ✓；L3 序保持（定理 A 反例 + 定理 B 修正）→ Task 5 ✓；L4 主矛盾 → Task 6 ✓
- §2 假设束 → Task 2 ✓；§5 发现处理 → Task 5/7（VERIFICATION.md）✓；§7 文件清单 → 各任务 ✓；§8 复现与发布 → Task 1/8 ✓；§9 成功标准 → Task 8 ✓

**2. 占位扫描：** 无 TBD/TODO；代码步骤含完整定理陈述与证明骨架；两处明确标记的"条件发现"步骤（Task 5 Step 4、Task 6 Step 2）是 spec 已声明的开放数学问题（spec §4 候选刻画），非计划占位——均有终止条件（两轮迭代失败 ⟹ 与用户确认）。

**3. 类型一致性：** `Data n` / `D.Assumptions`（Core.lean 定义的嵌套结构，Task 2 定稿）；`h51a/h51b/h51c/hpsi_nonneg/hp_cont/hpsi_cont/hlam_terminal/hlam_ode` 字段名全计划一致；`orderPreservation`/`externallyPositive`/`chebyshev_sum`/`variation_of_constants_forward` 签名在 Task 5/6/3/4 间交叉引用一致；主定理的 `horder` 明确标注"与 Theorem B 相同条件"。
