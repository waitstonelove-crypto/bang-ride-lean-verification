# 公式对照表：论文（arXiv:2508.09010v3）↔ Lean 定理

来源：Shi, Sass, Wu, Kim, Ma, Shin, Findeisen, Braatz,
*Bang-Ride Optimal Control: Monotonicity, External Positivity, and Fast Battery Charging*。

## 1. 数据结构（`BangRide.Core`）

| 论文 | Lean 定义 | 说明 |
|---|---|---|
| (26) 系统 ẋ = diag(a)x + 1u | `Data.a : Fin n → ℝ` | 对角元 aₖ |
| 终端协态 λ(tf⁻) | `Data.lam0 : Fin n → ℝ` | |
| (27) 相对灵敏度 p | `Data.p : ℝ → Fin n → ℝ` | 只保留序/符号假设 |
| 切换函数 ψ = 1ᵀλ | `Data.psi : ℝ → ℝ` + `Assumptions.hpsi_eq` | ψ(t) = Σλₖ(t) |
| (45) 协态 ODE | `Assumptions.hlam_ode` | λ̇ₖ = -aₖλₖ + pₖψ（HasDerivAt） |
| 终值条件 | `Assumptions.hlam_terminal` | λₖ(tf) = λ₀ₖ |
| Assumption 2.1 (C¹) | `Assumptions.hp_cont`/`hpsi_cont` | 连续性正则性 |
| PMP 引出的 ψ ≥ 0 | `Assumptions.hpsi_nonneg` | 区间内 ∀ t ∈ [0,tf]（PMP (8a)+(42) 的文档化边界） |

## 2. Assumption 5.1（`Assumptions` 字段）

| 论文 | Lean 字段 |
|---|---|
| 5.1(a) ∃j₁j₂: λ_{j₁}(tf⁻) > λ_{j₂}(tf⁻) ∧ a_{j₁} > a_{j₂} | `h51a` |
| 5.1(b) λₖ(tf⁻) ≥ λⱼ(tf⁻) ⟹ aₖ ≥ aⱼ | `h51b` |
| 5.1(c)(ii) λₖ(tf⁻) ≥ λⱼ(tf⁻) ⟹ pₖ[t] ≤ pⱼ[t] | `h51c` |
| 5.1(c)(i) s̃_u > 0（不形式化，仅经 p ≥ 0 进入） | `hsgn`（修正版附加假设） |

## 3. 定理层（`BangRide/Chebyshev.lean`）

| 内容 | Lean 定理 | 说明 |
|---|---|---|
| 二重和恒等式 | `double_sum_identity` | ΣᵢΣⱼ(aᵢ-aⱼ)(bᵢ-bⱼ) = 2nΣaᵢbᵢ - 2(Σaᵢ)(Σbᵢ) |
| Chebyshev 不等式 | `chebyshev_sum` | 同向排序 ⟹ nΣaᵢbᵢ ≥ (Σaᵢ)(Σbᵢ) |
| 严格版 | `chebyshev_sum_strict` | 严格同向对 ⟹ 严格不等式 |
| 零和推论 | `chebyshev_zero_sum` | Σbᵢ = 0 ⟹ 0 < Σaᵢbᵢ（主定理用法） |

## 4. 变分常数（`BangRide/VariationOfConstants.lean`）

| 论文 | Lean 定理 | 说明 |
|---|---|---|
| (46) 前向 | `Data.variation_of_constants_forward` | λₖ(tf) = e^{-aₖ(tf-t)}λₖ(t) + ∫ₜ^{tf}e^{-aₖ(tf-τ)}pₖψ |
| 后向（辅助） | `Data.variation_of_constants_backward` | λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ - ∫ₜ^{tf}e^{aₖ(τ-t)}pₖψ |

均从 (45) 经 FTC 全证（零 axiom）。

## 5. 序保持（`BangRide/OrderPreservation.lean`）

| 内容 | Lean 定理 | 说明 |
|---|---|---|
| 反例实例 | `Counterexample`（n=3, a=(5,0,-3), λ₀=(10,-1,-2)） | 假设束全字段验证 |
| **定理 A：论文原引理为假** | `order_preservation_counterexample` | λ₀₁ ≥ λ₀₂ 但 λ₁(1) < λ₂(1) |
| 核心引理 | `orderPreservationLT` | λₖ(t) < λⱼ(t) ⟹ λ₀ₖ < λ₀ⱼ |
| **定理 B：修正版** | `orderPreservation` | +轨迹分量非负 ⟹ λ₀ₖ ≥ λ₀ⱼ ⟹ λₖ(t) ≥ λⱼ(t) |
| 严格版 | `orderPreservationStrict` | λ₀ₖ > λ₀ⱼ ⟹ λₖ(t) > λⱼ(t) |

## 6. 外部正性（`BangRide/ExternalPositivity.lean`）

| 论文 | Lean 定理 | 说明 |
|---|---|---|
| (47) Σaₖλₖ = 0 | 主定理证明内部 `hsum0` | ψ(t)=0 + 局部极小 + ODE |
| **Theorem 5.1 核心（修正版）** | `Data.externallyPositive` | ∀ t ∈ (0,tf)：ψ(t) > 0 |
| Lemma 4.1（u = max D） | 不形式化 | PMP 边界，见 VERIFICATION.md §3 |
