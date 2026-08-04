/-
Copyright (c) 2026 waitstonelove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: waitstonelove
-/
import Mathlib
import BangRide.Core
import BangRide.VariationOfConstants

/-!
# 序保持引理：反例（定理 A）+ 修正版（定理 B）

论文附录 E 声称（原引理）：`λₖ(tf) ≥ λⱼ(tf) ⟹ λₖ(t) ≥ λⱼ(t)`（对任意 t ≤ tf）。

**定理 A（反例）**：该引理在 Assumption 5.1 原假设下为假。
实例：n=3, a=(5,0,-3), λ₀=(10,-1,-2), p≡0, tf=2。
协态解 λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ（ODE (45) 的解，正指数——注意：λ̇ₖ = -aₖλₖ 的解是 e^{aₖ(tf-t)}）。
对 (1,2)：λ₀₁ = -1 ≥ -2 = λ₀₂，但 t=1 处 λ₁(1) = -1 < λ₂(1) = -2e^{-3} ≈ -0.10。
所有假设字段成立（含 ψ ≥ 0：ψ(t) = 10e^{5(2-t)} - 1 - 2e^{-3(2-t)} ≥ 7 > 0）。

**定理 B（修正版）**：附加轨迹分量非负假设 `∀ k t, 0 ≤ λ t k` 下序保持成立。
（原 spec §4 的候选刻画"λ₀ⱼ ≤ 0"基于错误指数符号推导，已被本反例取代。）
-/

noncomputable section
open scoped BigOperators

-- convert 目标顺序不稳定，`all_goals first | ...` 的未用分支属正常；
-- `simp [counterexample]` 展开反例定义属有意为之（linter.flexible 为 scoped 选项，
-- 需在具体声明上用 `set_option ... in` 作用域）
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace BangRide

/-- 反例实例：n=3, a=(5,0,-3), λ₀=(10,-1,-2), p≡0, tf=2 -/
def counterexample : Data 3 where
  tf := 2
  a := (![5, 0, -3] : Fin 3 → ℝ)
  lam0 := (![10, -1, -2] : Fin 3 → ℝ)
  p := fun _ _ => 0
  psi := fun t => 10 * Real.exp (5 * (2 - t)) - 1 - 2 * Real.exp (-3 * (2 - t))
  lam := fun t k => Real.exp ((![5, 0, -3] : Fin 3 → ℝ) k * (2 - t))
    * (![10, -1, -2] : Fin 3 → ℝ) k

namespace Counterexample

/-- 反例满足全部假设束字段 -/
set_option linter.flexible false in
theorem assumptions : (counterexample : Data 3).Assumptions := by
  constructor
  · norm_num [counterexample]
  · -- h51a：j₁=0, j₂=1
    refine ⟨0, 1, ?_, ?_⟩
    · norm_num [counterexample]
    · norm_num [counterexample]
  · -- h51b：4 组 (k,j) 组合
    intro k j
    fin_cases k <;> fin_cases j <;> simp [counterexample] <;> intro h <;> nlinarith
  · -- h51c：p ≡ 0
    intro k j hkj s
    simp [counterexample]
  · -- hpsi_eq
    intro t
    change counterexample.psi t = ∑ k : Fin 3, counterexample.lam t k
    dsimp [counterexample]
    rw [Fin.sum_univ_three]
    simp [Real.exp_zero]
    ring
  · -- hpsi_nonneg：∀ t ∈ [0,2]，ψ(t) = 10e^{5(2-t)} - 1 - 2e^{-3(2-t)} ≥ 7
    intro t ht
    have hs : 0 ≤ 2 - t := by
      have htl : 0 ≤ t := (Set.mem_Icc.mp ht).1
      have htu : t ≤ 2 := (Set.mem_Icc.mp ht).2
      nlinarith
    have he1 : (1 : ℝ) ≤ Real.exp (5 * (2 - t)) := by
      exact (Real.one_le_exp_iff).2 (mul_nonneg (by norm_num) hs)
    have he2 : Real.exp (-3 * (2 - t)) ≤ 1 := by
      exact (Real.exp_le_one_iff).2 (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs)
    change (0 : ℝ) ≤ 10 * Real.exp (5 * (2 - t)) - 1 - 2 * Real.exp (-3 * (2 - t))
    nlinarith
  · -- hp_cont
    intro k
    simp [counterexample]
    exact continuous_const
  · -- hpsi_cont
    dsimp [counterexample]
    fun_prop
  · -- hlam_terminal
    intro k
    simp [counterexample, Real.exp_zero]
  · -- hlam_ode：λₖ(t) = e^{aₖ(2-t)}λ₀ₖ ⟹ λ̇ₖ = -aₖλₖ
    intro k t
    dsimp [counterexample]
    have hg : HasDerivAt (fun x : ℝ => (![5, 0, -3] : Fin 3 → ℝ) k * (2 - x))
        (-(![5, 0, -3] : Fin 3 → ℝ) k) t := by
      have hsub : HasDerivAt (fun x : ℝ => 2 - x) (-1) t := by
        convert (hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t) using 1
        all_goals first | rfl | norm_num | (funext x; rfl)
      simpa [mul_neg, neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using
        hsub.const_mul ((![5, 0, -3] : Fin 3 → ℝ) k)
    have hexp' : HasDerivAt (fun x : ℝ =>
        Real.exp ((![5, 0, -3] : Fin 3 → ℝ) k * (2 - x)))
        (Real.exp ((![5, 0, -3] : Fin 3 → ℝ) k * (2 - t))
          * -(![5, 0, -3] : Fin 3 → ℝ) k) t := by
      convert (Real.hasDerivAt_exp ((![5, 0, -3] : Fin 3 → ℝ) k * (2 - t))).comp t (hg)
        using 1
      all_goals first | rfl | (funext x; rfl)
    have hconst : HasDerivAt (fun _ : ℝ => (![10, -1, -2] : Fin 3 → ℝ) k) 0 t := by
      exact hasDerivAt_const t ((![10, -1, -2] : Fin 3 → ℝ) k)
    convert (hexp'.mul hconst) using 1
    all_goals first | rfl | ring | (funext x; dsimp; ring)

end Counterexample

/-- 定理 A：论文"λₖ(tf) ≥ λⱼ(tf) ⟹ λₖ(t) ≥ λⱼ(t)"在 Assumption 5.1 原假设下为假。
    反例（n=3, a=(5,0,-3), λ₀=(10,-1,-2), p≡0, tf=2）：
    对 (1,2)：λ₀₁ = -1 ≥ -2 = λ₀₂（且 a₁ = 0 ≥ a₂ = -3），
    但 t=1 处 λ₁(1) = -1 < λ₂(1) = -2e^{-3} ≈ -0.0996。
    所有假设字段由 `Counterexample.assumptions` 保证。 -/
set_option linter.flexible false in
theorem order_preservation_counterexample :
    ∃ t, t ∈ Set.Icc 0 2 ∧
      counterexample.lam0 1 ≥ counterexample.lam0 2 ∧
      counterexample.lam t 1 < counterexample.lam t 2 := by
  refine ⟨1, ?_, ?_, ?_⟩
  · norm_num [Set.Icc]
  · simp [counterexample]
  · -- λ₁(1) = -1 < λ₂(1) = -2·e^{-3}
    have h_e3 : (2 : ℝ) < Real.exp 3 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hpow : (2 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
      have hconn : Real.exp 1 ^ 3 = Real.exp 3 := by
        rw [← Real.exp_nat_mul 1 3]
        norm_num
      rw [hconn] at hpow
      norm_num at hpow
      nlinarith
    have h_half : Real.exp (-3) < (1 / 2 : ℝ) := by
      have hinv : (Real.exp 3)⁻¹ < (2 : ℝ)⁻¹ := by
        exact (inv_lt_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 2)).mpr h_e3
      simpa [Real.exp_neg, one_div] using hinv
    dsimp [counterexample]
    simp [Real.exp_zero]
    norm_num
    nlinarith [h_half]

/-- 核心引理（修正版序保持的反证方向）：轨迹分量非负 + p ≥ 0 + 5.1 假设下，
    `λₖ(t) < λⱼ(t) ⟹ λ₀ₖ < λ₀ⱼ`。
    证明按论文附录 E：用前向形式 (46) 逐项比较
    （指数项：λⱼ(t) ≥ 0 + aₖ ≥ aⱼ；积分项：pₖ ≤ pⱼ + p ≥ 0 + ψ ≥ 0）。 -/
theorem orderPreservationLT {n : ℕ} {D : Data n} (A : D.Assumptions) (k j : Fin n)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (hlam_nonneg : ∀ k : Fin n, ∀ t, 0 ≤ D.lam t k) :
    ∀ t, t ∈ Set.Icc 0 D.tf → D.lam t k < D.lam t j → D.lam0 k < D.lam0 j := by
  intro t ht hlt
  by_contra h
  have hkj : D.lam0 k ≥ D.lam0 j := le_of_not_gt h
  have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
  have htu : t ≤ D.tf := (Set.mem_Icc.mp ht).2
  have hs : 0 ≤ D.tf - t := by nlinarith
  have ha : D.a k ≥ D.a j := A.h51b k j hkj
  have hneg : -D.a k ≤ -D.a j := by nlinarith
  have hterm1 : Real.exp (-D.a k * (D.tf - t)) * D.lam t k
      < Real.exp (-D.a j * (D.tf - t)) * D.lam t j := by
    have he : Real.exp (-D.a k * (D.tf - t)) ≤ Real.exp (-D.a j * (D.tf - t)) := by
      exact (Real.exp_strictMono.le_iff_le).2 (mul_le_mul_of_nonneg_right hneg hs)
    have h1 : Real.exp (-D.a k * (D.tf - t)) * D.lam t k
        < Real.exp (-D.a k * (D.tf - t)) * D.lam t j := by
      exact mul_lt_mul_of_pos_left hlt (Real.exp_pos _)
    have h2 : Real.exp (-D.a k * (D.tf - t)) * D.lam t j
        ≤ Real.exp (-D.a j * (D.tf - t)) * D.lam t j := by
      exact mul_le_mul_of_nonneg_right he (hlam_nonneg j t)
    exact lt_of_lt_of_le h1 h2
  have hint : ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)
      ≤ ∫ τ in t..D.tf, Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
    have hcontk : Continuous (fun τ : ℝ =>
        Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)) := by
      exact ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).mul
        ((A.hp_cont k).mul A.hpsi_cont))
    have hcontj : Continuous (fun τ : ℝ =>
        Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ)) := by
      exact ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).mul
        ((A.hp_cont j).mul A.hpsi_cont))
    refine intervalIntegral.integral_mono_on htu
      (hcontk.intervalIntegrable t D.tf) (hcontj.intervalIntegrable t D.tf) ?_
    intro τ hτ
    have hτ1 : t ≤ τ := (Set.mem_Icc.mp hτ).1
    have hτ2 : τ ≤ D.tf := (Set.mem_Icc.mp hτ).2
    have hτ0 : 0 ≤ τ := le_trans ht0 hτ1
    have hψτ : 0 ≤ D.psi τ := A.hpsi_nonneg τ ⟨hτ0, hτ2⟩
    have hE1 : Real.exp (-D.a k * (D.tf - τ)) ≤ Real.exp (-D.a j * (D.tf - τ)) := by
      have hsτ : 0 ≤ D.tf - τ := by nlinarith
      exact (Real.exp_strictMono.le_iff_le).2 (mul_le_mul_of_nonneg_right hneg hsτ)
    have hpτ : D.p τ k ≤ D.p τ j := A.h51c k j hkj τ
    have hc1 : Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)
        ≤ Real.exp (-D.a k * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpτ hψτ)
        (le_of_lt (Real.exp_pos _))
    have hc2 : Real.exp (-D.a k * (D.tf - τ)) * (D.p τ j * D.psi τ)
        ≤ Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
      exact mul_le_mul_of_nonneg_right hE1 (mul_nonneg (hsgn τ j) hψτ)
    exact le_trans hc1 hc2
  have hltf : D.lam D.tf k < D.lam D.tf j := by
    have hf1' := Data.variation_of_constants_forward A k t ht
    have hf2' := Data.variation_of_constants_forward A j t ht
    rw [hf1', hf2']
    nlinarith [hterm1, hint]
  have hltf' : D.lam0 k < D.lam0 j := by
    simpa [A.hlam_terminal] using hltf
  exact h hltf'

/-- 定理 B（修正版序保持）：附加轨迹分量非负假设 `∀ k t, 0 ≤ λ t k` 下，
    `λ₀ₖ ≥ λ₀ⱼ ⟹ λₖ(t) ≥ λⱼ(t)`（∀ t ≤ tf）。 -/
theorem orderPreservation {n : ℕ} {D : Data n} (A : D.Assumptions) (k j : Fin n)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (hlam_nonneg : ∀ k : Fin n, ∀ t, 0 ≤ D.lam t k) :
    ∀ t, t ∈ Set.Icc 0 D.tf → D.lam0 k ≥ D.lam0 j → D.lam t k ≥ D.lam t j := by
  intro t ht hkj
  by_contra h
  have hlt : D.lam t k < D.lam t j := lt_of_not_ge h
  have hlt' : D.lam0 k < D.lam0 j := orderPreservationLT A k j hsgn hlam_nonneg t ht hlt
  exact (not_lt_of_ge hkj) hlt'

/-- 定理 B（严格版）：`λ₀ₖ > λ₀ⱼ ⟹ λₖ(t) > λⱼ(t)`（Chebyshev 严格对需要） -/
theorem orderPreservationStrict {n : ℕ} {D : Data n} (A : D.Assumptions) (k j : Fin n)
    (hsgn : ∀ s, ∀ k : Fin n, 0 ≤ D.p s k)
    (hlam_nonneg : ∀ k : Fin n, ∀ t, 0 ≤ D.lam t k) :
    ∀ t, t ∈ Set.Icc 0 D.tf → D.lam0 k > D.lam0 j → D.lam t k > D.lam t j := by
  intro t ht hkj
  by_contra h
  have hle : D.lam t k ≤ D.lam t j := le_of_not_gt h
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hlt' : D.lam0 k < D.lam0 j := orderPreservationLT A k j hsgn hlam_nonneg t ht hlt
    exact (not_lt_of_ge (le_of_lt hkj)) hlt'
  · -- λₖ(t) = λⱼ(t)：forward 相减 ⟹ λ₀ₖ ≤ λ₀ⱼ，与 λ₀ₖ > λ₀ⱼ 矛盾
    have hkj' : D.lam0 k ≥ D.lam0 j := le_of_lt hkj
    have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have htu : t ≤ D.tf := (Set.mem_Icc.mp ht).2
    have hs : 0 ≤ D.tf - t := by nlinarith
    have ha : D.a k ≥ D.a j := A.h51b k j hkj'
    have hneg : -D.a k ≤ -D.a j := by nlinarith
    have hterm1 : Real.exp (-D.a k * (D.tf - t)) * D.lam t k
        ≤ Real.exp (-D.a j * (D.tf - t)) * D.lam t j := by
      have he : Real.exp (-D.a k * (D.tf - t)) ≤ Real.exp (-D.a j * (D.tf - t)) := by
        exact (Real.exp_strictMono.le_iff_le).2 (mul_le_mul_of_nonneg_right hneg hs)
      rw [heq]
      exact mul_le_mul_of_nonneg_right he (hlam_nonneg j t)
    have hint : ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)
        ≤ ∫ τ in t..D.tf, Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
      have hcontk : Continuous (fun τ : ℝ =>
          Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)) := by
        exact ((Real.continuous_exp.comp
          (continuous_const.mul (continuous_const.sub continuous_id))).mul
          ((A.hp_cont k).mul A.hpsi_cont))
      have hcontj : Continuous (fun τ : ℝ =>
          Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ)) := by
        exact ((Real.continuous_exp.comp
          (continuous_const.mul (continuous_const.sub continuous_id))).mul
          ((A.hp_cont j).mul A.hpsi_cont))
      refine intervalIntegral.integral_mono_on htu
        (hcontk.intervalIntegrable t D.tf) (hcontj.intervalIntegrable t D.tf) ?_
      intro τ hτ
      have hτ1 : t ≤ τ := (Set.mem_Icc.mp hτ).1
      have hτ2 : τ ≤ D.tf := (Set.mem_Icc.mp hτ).2
      have hτ0 : 0 ≤ τ := le_trans ht0 hτ1
      have hψτ : 0 ≤ D.psi τ := A.hpsi_nonneg τ ⟨hτ0, hτ2⟩
      have hE1 : Real.exp (-D.a k * (D.tf - τ)) ≤ Real.exp (-D.a j * (D.tf - τ)) := by
        have hsτ : 0 ≤ D.tf - τ := by nlinarith
        exact (Real.exp_strictMono.le_iff_le).2 (mul_le_mul_of_nonneg_right hneg hsτ)
      have hpτ : D.p τ k ≤ D.p τ j := A.h51c k j hkj' τ
      have hc1 : Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)
          ≤ Real.exp (-D.a k * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpτ hψτ)
          (le_of_lt (Real.exp_pos _))
      have hc2 : Real.exp (-D.a k * (D.tf - τ)) * (D.p τ j * D.psi τ)
          ≤ Real.exp (-D.a j * (D.tf - τ)) * (D.p τ j * D.psi τ) := by
        exact mul_le_mul_of_nonneg_right hE1 (mul_nonneg (hsgn τ j) hψτ)
      exact le_trans hc1 hc2
    have hlef : D.lam D.tf k ≤ D.lam D.tf j := by
      have hf1' := Data.variation_of_constants_forward A k t ht
      have hf2' := Data.variation_of_constants_forward A j t ht
      rw [hf1', hf2']
      nlinarith [hterm1, hint]
    have hlef' : D.lam0 k ≤ D.lam0 j := by
      simpa [A.hlam_terminal] using hlef
    exact (not_lt_of_ge hlef') hkj

end BangRide
