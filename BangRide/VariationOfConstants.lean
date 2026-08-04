/-
Copyright (c) 2026 waitstonelove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: waitstonelove
-/
import Mathlib
import BangRide.Core

/-!
# 变分常数公式（论文式 (46)）

由协态 ODE (45) `λ̇ₖ = -aₖλₖ + pₖψ` 与终值 `λₖ(tf) = λ₀ₖ` 经 FTC 推出显式解：

`λₖ(tf) = e^{-aₖ(tf-t)}·λₖ(t) + ∫ₜ^{tf} e^{-aₖ(tf-τ)}·pₖ[τ]·ψ(τ) dτ`

证明路径：对 `h(s) = e^{-aₖ(tf-s)}·λₖ(s)` 求导得
`h'(s) = e^{-aₖ(tf-s)}·pₖ(s)·ψ(s)`，两端在 `[t, tf]` 上积分（FTC）。零 axiom。
-/

noncomputable section
open scoped BigOperators

namespace BangRide

namespace Data

variable {n : ℕ} {D : Data n} (A : D.Assumptions) {k : Fin n}

/-- 前向形式（论文式 (46)）：`λₖ(tf) = e^{-aₖ(tf-t)}λₖ(t) + ∫ₜ^{tf} e^{-aₖ(tf-τ)}pₖ[τ]ψ(τ)`
    注意：`A` 必须显式出现在签名中（否则变量不会自动绑定，体内无法引用） -/
theorem variation_of_constants_forward (A : D.Assumptions) (k : Fin n) :
    ∀ t, t ∈ Set.Icc 0 D.tf →
      D.lam D.tf k = Real.exp (-D.a k * (D.tf - t)) * D.lam t k
        + ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ) := by
  intro t ht
  let g : ℝ → ℝ := fun s => -D.a k * (D.tf - s)
  let h : ℝ → ℝ := fun s => Real.exp (g s) * D.lam s k
  let f' : ℝ → ℝ := fun s => Real.exp (g s) * (D.p s k * D.psi s)
  have hg' : ∀ s, HasDerivAt g (D.a k) s := by
    intro s
    have hg2 : HasDerivAt (fun x : ℝ => D.a k * (x - D.tf)) (D.a k) s := by
      simpa using ((hasDerivAt_id s).sub_const D.tf).const_mul (D.a k)
    convert hg2 using 1
    · funext x
      ring
  have hh' : ∀ s, HasDerivAt h (f' s) s := by
    intro s
    dsimp [f', h]
    have hexp' : HasDerivAt (fun x : ℝ => Real.exp (g x)) (Real.exp (g s) * D.a k) s := by
      convert (Real.hasDerivAt_exp (g s)).comp s (hg' s) using 1
      all_goals first | rfl | (funext x; rfl)
    convert (hexp'.mul (A.hlam_ode k s)) using 1
    · rfl
    · rfl
    · dsimp [g]
      ring
  have hf'_cont : Continuous f' := by
    dsimp [f', g]
    exact ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).mul
      ((A.hp_cont k).mul A.hpsi_cont))
  have hint : IntervalIntegrable f' MeasureTheory.volume t D.tf :=
    hf'_cont.intervalIntegrable t D.tf
  have hFTC : ∫ s in t..D.tf, f' s = h D.tf - h t := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hh' x) hint
  rw [hFTC]
  dsimp [h, g]
  simp [A.hlam_terminal, Real.exp_zero]

/-- 后向形式（辅助）：`λₖ(t) = e^{aₖ(tf-t)}λ₀ₖ - ∫ₜ^{tf} e^{aₖ(τ-t)}pₖ[τ]ψ(τ)` -/
theorem variation_of_constants_backward (A : D.Assumptions) (k : Fin n) :
    ∀ t, t ∈ Set.Icc 0 D.tf →
      D.lam t k = Real.exp (D.a k * (D.tf - t)) * D.lam0 k
        - ∫ τ in t..D.tf, Real.exp (D.a k * (τ - t)) * (D.p τ k * D.psi τ) := by
  intro t ht
  have hf := variation_of_constants_forward A k t ht
  have hmul : Real.exp (D.a k * (D.tf - t)) * D.lam D.tf k =
      D.lam t k + Real.exp (D.a k * (D.tf - t)) *
        ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ) := by
    rw [hf]
    rw [mul_add]
    have he : Real.exp (D.a k * (D.tf - t)) * Real.exp (-D.a k * (D.tf - t)) = 1 := by
      rw [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    rw [← mul_assoc, he, one_mul]
  have hint_id :
      Real.exp (D.a k * (D.tf - t)) *
        ∫ τ in t..D.tf, Real.exp (-D.a k * (D.tf - τ)) * (D.p τ k * D.psi τ)
      = ∫ τ in t..D.tf, Real.exp (D.a k * (τ - t)) * (D.p τ k * D.psi τ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext τ
    have hexp : Real.exp (D.a k * (D.tf - t)) * Real.exp (-D.a k * (D.tf - τ))
        = Real.exp (D.a k * (τ - t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hexp]
  rw [A.hlam_terminal] at hmul
  rw [hmul, hint_id]
  ring

end Data
end BangRide
