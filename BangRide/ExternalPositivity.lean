/-
Copyright (c) 2026 waitstonelove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: waitstonelove
-/
import Mathlib
import BangRide.Core
import BangRide.Chebyshev
import BangRide.OrderPreservation

/-!
# 外部正性主定理（修正版 Theorem 5.1 核心）

切换函数 `ψ(t) = 1ᵀλ(t)` 在假设束 + p ≥ 0 + 轨迹分量非负下满足 `ψ(t) > 0`（内点 t）。

证明结构（论文附录 E + 修正）：
1. 反设 ψ(t) = 0（t 为内点）：ψ ≥ 0 ⟹ t 是局部极小 ⟹ `deriv ψ t = 0`
   （`IsLocalMin.deriv_eq_zero`）。
2. 由 ODE (45) 组装 `deriv ψ t = -Σaₖλₖ(t) + ψ(t)Σpₖ(t)`，结合 ψ(t) = 0 ⟹ (47) `Σaₖλₖ(t) = 0`。
3. Chebyshev 严格版（`chebyshev_zero_sum`）：
   - 同向：`(λᵢ(t)-λⱼ(t))(aᵢ-aⱼ) ≥ 0`（5.1b + 序保持）；
   - `Σλₖ(t) = ψ(t) = 0`；
   - 严格对：5.1a 的 (j₁,j₂) + 严格序保持 ⟹ `(λ_{j₁}(t)-λ_{j₂}(t))(a_{j₁}-a_{j₂}) > 0`；
   ⟹ `0 < Σaₖλₖ(t)`，与 (47) 矛盾。

注：结论限于内点 (0, tf)（端点需单侧导数论证，论文结论为 a.e.，内点集覆盖全测度）。
-/

noncomputable section
open scoped BigOperators

namespace BangRide

namespace Data

variable {n : ℕ} {D : Data n}

/-- 修正版 Theorem 5.1 核心：切换函数 ψ(t) = 1ᵀλ(t) > 0（内点），
    假设：Assumption 5.1 束 + p ≥ 0 + 轨迹分量非负（定理 B 的条件）。 -/
theorem externallyPositive (A : D.Assumptions)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (hlam_nonneg : ∀ k : Fin n, ∀ t, 0 ≤ D.lam t k) :
    ∀ t, t ∈ Set.Ioo 0 D.tf → 0 < D.psi t := by
  intro t ht
  by_contra h
  have hz : D.psi t ≤ 0 := le_of_not_gt h
  have ht0 : 0 < t := (Set.mem_Ioo.mp ht).1
  have htf : t < D.tf := (Set.mem_Ioo.mp ht).2
  have htin : t ∈ Set.Icc 0 D.tf := ⟨le_of_lt ht0, le_of_lt htf⟩
  have hψ : 0 ≤ D.psi t := A.hpsi_nonneg t htin
  have hzeq : D.psi t = 0 := le_antisymm hz hψ
  have hderiv_eq : deriv D.psi t = -∑ k : Fin n, D.a k * D.lam t k
      + D.psi t * ∑ k : Fin n, D.p t k := by
    have hψderiv : HasDerivAt D.psi
        (∑ k : Fin n, (-D.a k * D.lam t k + D.p t k * D.psi t)) t := by
      have hsum : HasDerivAt (∑ i : Fin n, fun s : ℝ => D.lam s i)
          (∑ i : Fin n, (-D.a i * D.lam t i + D.p t i * D.psi t)) t := by
        exact HasDerivAt.sum (u := Finset.univ) (fun k _ => A.hlam_ode k t)
      convert hsum using 1
      · funext s
        simp [Finset.sum_apply]
        exact A.hpsi_eq s
    have hval : (∑ k : Fin n, (-D.a k * D.lam t k + D.p t k * D.psi t))
        = -∑ k : Fin n, D.a k * D.lam t k
          + D.psi t * ∑ k : Fin n, D.p t k := by
      calc
        (∑ k : Fin n, (-D.a k * D.lam t k + D.p t k * D.psi t))
            = (∑ k : Fin n, (-(D.a k * D.lam t k)))
              + (∑ k : Fin n, D.p t k * D.psi t) := by
                rw [Finset.sum_add_distrib]
                congr 1
                all_goals apply Finset.sum_congr rfl
                all_goals intro k _
                all_goals ring
        _ = -(∑ k : Fin n, D.a k * D.lam t k)
            + (∑ k : Fin n, D.p t k) * D.psi t := by
                rw [Finset.sum_neg_distrib]
                rw [← Finset.sum_mul]
        _ = -∑ k : Fin n, D.a k * D.lam t k
            + D.psi t * ∑ k : Fin n, D.p t k := by
                ring
    have hderiv_eq' : deriv D.psi t
        = ∑ k : Fin n, (-D.a k * D.lam t k + D.p t k * D.psi t) := hψderiv.deriv
    rw [hval] at hderiv_eq'
    exact hderiv_eq'
  have hmin : IsLocalMin D.psi t := by
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun y hy => by
      have hy0 : 0 < y := (Set.mem_Ioo.mp hy).1
      have hyf : y < D.tf := (Set.mem_Ioo.mp hy).2
      rw [hzeq]
      exact A.hpsi_nonneg y ⟨le_of_lt hy0, le_of_lt hyf⟩)
  have hderiv0 : deriv D.psi t = 0 := hmin.deriv_eq_zero
  have hsum0 : ∑ k : Fin n, D.a k * D.lam t k = 0 := by
    rw [hderiv_eq, hzeq] at hderiv0
    nlinarith
  have hsame : ∀ i j : Fin n, (D.a i - D.a j) * (D.lam t i - D.lam t j) ≥ 0 := by
    intro i j
    by_cases hij : D.lam0 i ≥ D.lam0 j
    · have hlam_i : D.lam t i ≥ D.lam t j :=
        orderPreservation A i j hsgn hlam_nonneg t htin hij
      have ha : D.a i ≥ D.a j := A.h51b i j hij
      exact mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hlam_i)
    · have hji : D.lam0 j ≥ D.lam0 i := le_of_not_ge hij
      have hlam_j : D.lam t j ≥ D.lam t i :=
        orderPreservation A j i hsgn hlam_nonneg t htin hji
      have ha : D.a j ≥ D.a i := A.h51b j i hji
      have h1 : 0 ≤ D.a j - D.a i := sub_nonneg.mpr ha
      have h2 : 0 ≤ D.lam t j - D.lam t i := sub_nonneg.mpr hlam_j
      have h3 : 0 ≤ (D.a j - D.a i) * (D.lam t j - D.lam t i) := mul_nonneg h1 h2
      nlinarith
  have hzero : (∑ k : Fin n, D.lam t k) = 0 := by
    rw [← A.hpsi_eq t]
    exact hzeq
  have hstrict : ∃ i j : Fin n, (D.a i - D.a j) * (D.lam t i - D.lam t j) > 0 := by
    rcases A.h51a with ⟨j₁, j₂, hlam0, ha0⟩
    have hlam_s : D.lam t j₁ > D.lam t j₂ :=
      orderPreservationStrict A j₁ j₂ hsgn hlam_nonneg t htin hlam0
    refine ⟨j₁, j₂, ?_⟩
    exact mul_pos (sub_pos.mpr ha0) (sub_pos.mpr hlam_s)
  have hcheb : 0 < ∑ k : Fin n, D.a k * D.lam t k :=
    chebyshev_zero_sum D.a (fun k => D.lam t k) hsame hzero hstrict
  exact (ne_of_gt hcheb) hsum0

end Data
end BangRide
