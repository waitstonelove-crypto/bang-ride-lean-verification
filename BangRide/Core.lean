/-
Copyright (c) 2026 waitstonelove. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: waitstonelove
-/
import Mathlib

/-!
# BangRide — Theorem 5.1 核心形式化

Shi, Sass, Wu, Kim, Ma, Shin, Findeisen, Braatz,
*Bang-Ride Optimal Control: Monotonicity, External Positivity, and Fast Battery Charging*,
arXiv:2508.09010v3.

本模块定义 Theorem 5.1 的数据结构与 Assumption 5.1 假设束。
-/

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
