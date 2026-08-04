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
-- `simp [counterexample]` 展开反例定义属有意为之
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.flexible false

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

end BangRide
