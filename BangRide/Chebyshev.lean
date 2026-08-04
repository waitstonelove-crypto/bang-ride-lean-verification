/-
Copyright (c) 2026 waitstonelove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: waitstonelove
-/
import Mathlib

/-!
# Chebyshev 求和不等式

同向排序序列 `a, b : Fin n → ℝ` 的 Chebyshev 求和不等式（论文附录 E 中
`(1/n)Σaᵢλᵢ ≥ (1/n)Σaᵢ·(1/n)Σλᵢ` 的通用形式），含严格版与零和推论。
本模块不依赖 `BangRide.Core`，可独立复用。

核心恒等式：`∑ᵢ∑ⱼ (aᵢ-aⱼ)(bᵢ-bⱼ) = 2n·Σaᵢbᵢ - 2(Σaᵢ)(Σbᵢ)`。

注意：对未使用绑定变量的求和必须显式标注类型（`∑ j : Fin n, a i * b i`），
否则 Fintype 实例无法解析。
-/

noncomputable section
open scoped BigOperators

namespace BangRide

/-- 二重和恒等式：`∑ᵢ∑ⱼ (aᵢ-aⱼ)(bᵢ-bⱼ) = 2n·Σaᵢbᵢ - 2(Σaᵢ)(Σbᵢ)` -/
lemma double_sum_identity {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, (a i - a j) * (b i - b j))
      = 2 * (n : ℝ) * (∑ i : Fin n, a i * b i) - 2 * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, (a i - a j) * (b i - b j))
        = ∑ i : Fin n, ∑ j : Fin n, (a i * b i - a i * b j - a j * b i + a j * b j) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
    _ = (∑ i : Fin n, ∑ j : Fin n, a i * b i) - (∑ i : Fin n, ∑ j : Fin n, a i * b j)
          - (∑ i : Fin n, ∑ j : Fin n, a j * b i) + (∑ i : Fin n, ∑ j : Fin n, a j * b j) := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = 2 * (n : ℝ) * (∑ i : Fin n, a i * b i) - 2 * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
            have h1 : (∑ i : Fin n, ∑ j : Fin n, a i * b i) = (n : ℝ) * (∑ i : Fin n, a i * b i) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, a i * b i)
                    = ∑ i : Fin n, ((Finset.univ : Finset (Fin n)).card • (a i * b i)) := by
                        apply Finset.sum_congr rfl
                        intro i _
                        rw [Finset.sum_const]
                _ = ∑ i : Fin n, ((Fintype.card (Fin n) : ℕ) • (a i * b i)) := by
                        simp [Finset.card_univ]
                _ = (Fintype.card (Fin n) : ℝ) * (∑ i : Fin n, a i * b i) := by
                        rw [Finset.sum_nsmul, nsmul_eq_mul]
                _ = (n : ℝ) * (∑ i : Fin n, a i * b i) := by
                        rw [Fintype.card_fin]
            have h2 :
                (∑ i : Fin n, ∑ j : Fin n, a i * b j)
                  = (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, a i * b j) = ∑ i : Fin n, (a i * (∑ j : Fin n, b j)) := by
                        apply Finset.sum_congr rfl
                        intro i _
                        rw [Finset.mul_sum]
                _ = (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
                        rw [← Finset.sum_mul]
            have h3 :
                (∑ i : Fin n, ∑ j : Fin n, a j * b i)
                  = (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, a j * b i) = ∑ i : Fin n, ((∑ j : Fin n, a j) * b i) := by
                        apply Finset.sum_congr rfl
                        intro i _
                        rw [Finset.sum_mul]
                _ = (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
                        rw [← Finset.mul_sum]
            have h4 : (∑ i : Fin n, ∑ j : Fin n, a j * b j) = (n : ℝ) * (∑ i : Fin n, a i * b i) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, a j * b j)
                    = ((Finset.univ : Finset (Fin n)).card • (∑ j : Fin n, a j * b j)) := by
                        rw [Finset.sum_const]
                _ = ((Fintype.card (Fin n) : ℕ) • (∑ j : Fin n, a j * b j)) := by
                        simp [Finset.card_univ]
                _ = (Fintype.card (Fin n) : ℝ) * (∑ j : Fin n, a j * b j) := by
                        rw [nsmul_eq_mul]
                _ = (n : ℝ) * (∑ i : Fin n, a i * b i) := by
                        rw [Fintype.card_fin]
            rw [h1, h2, h3, h4]
            ring

/-- 同向排序序列的 Chebyshev 求和不等式：`n·Σaᵢbᵢ ≥ (Σaᵢ)(Σbᵢ)` -/
theorem chebyshev_sum {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0) :
    (n : ℝ) * (∑ i : Fin n, a i * b i) ≥ (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
  have hnonneg : (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, (a i - a j) * (b i - b j) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hsame i j))
  rw [double_sum_identity] at hnonneg
  nlinarith

/-- 严格版：存在严格同向对 ⟹ 严格不等式 -/
theorem chebyshev_sum_strict {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0)
    (hstrict : ∃ i j : Fin n, (a i - a j) * (b i - b j) > 0) :
    (n : ℝ) * (∑ i : Fin n, a i * b i) > (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
  have hpos : (0 : ℝ) < ∑ i : Fin n, ∑ j : Fin n, (a i - a j) * (b i - b j) := by
    obtain ⟨i, j, hij⟩ := hstrict
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => hsame i j)) ?_
    exact ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ => hsame i j)
      ⟨j, Finset.mem_univ _, hij⟩⟩
  rw [double_sum_identity] at hpos
  nlinarith

/-- 推论：`Σbᵢ = 0` 时（主定理用法），`Σaᵢbᵢ > 0` -/
theorem chebyshev_zero_sum {n : ℕ} (a b : Fin n → ℝ)
    (hsame : ∀ i j : Fin n, (a i - a j) * (b i - b j) ≥ 0)
    (hzero : (∑ i : Fin n, b i) = 0)
    (hstrict : ∃ i j : Fin n, (a i - a j) * (b i - b j) > 0) :
    0 < ∑ i : Fin n, a i * b i := by
  have hstrict' : ∃ i j : Fin n, (a i - a j) * (b i - b j) > 0 := hstrict
  rcases hstrict with ⟨i, _, _⟩
  have hnz : n ≠ 0 := by
    intro hn
    exact Fin.elim0 (by simpa [hn] using i)
  have hcard : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hnz
  have hlt := chebyshev_sum_strict a b hsame hstrict'
  have hT : (0 : ℝ) < (n : ℝ) * (∑ i : Fin n, a i * b i) := by
    simpa [hzero] using hlt
  exact (mul_pos_iff_of_pos_left hcard).mp hT

end BangRide
