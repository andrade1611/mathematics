/-
Copyright (c) 2026 Carlos Flores Andrade.
SPDX-License-Identifier: MIT
Repositorio: https://github.com/andrade1611/mathematics
-/

import Lema1
import Lema2

/-!
 Sea $a\in\mathbb{R}$ con $a>0$ entonces
\rpar{\dfrac{a}{\lceil a\rceil}}^2\leq a\leq
 \rpar{a\left\lceil\dfrac{1}{a}\right\rceil}^2
-/

theorem raiz_cuadrada_cotas (a : ℝ) (ha : 0 < a) :
    (a / (⌈a⌉₊ : ℝ))^2 ≤ a ∧
      a ≤ (a * (⌈1 / a⌉₊ : ℝ))^2 := by
    have ceil_le_sq (x : ℝ) (hx : 0 < x) :
        x ≤ (⌈x⌉₊ : ℝ)^2 := by
        have hceil : (1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by
            exact_mod_cast (Nat.one_le_ceil_iff.mpr hx)
        have hsq : (⌈x⌉₊ : ℝ) ≤ (⌈x⌉₊ : ℝ)^2 := by
            calc
                (⌈x⌉₊ : ℝ) = (⌈x⌉₊ : ℝ) * 1 := by ring
                _ ≤ (⌈x⌉₊ : ℝ) * (⌈x⌉₊ : ℝ) :=
                    mul_le_mul_of_nonneg_left hceil (by positivity)
                _ = (⌈x⌉₊ : ℝ)^2 := by ring
        exact (Nat.le_ceil x).trans hsq
    have hn₁ : ⌈a⌉₊ ≠ 0 := by
        have h := Nat.one_le_ceil_iff.mpr ha
        omega
    have hrecip : 0 < 1 / a := by positivity
    have hn₂ : ⌈1 / a⌉₊ ≠ 0 := by
        have h := Nat.one_le_ceil_iff.mpr hrecip
        omega
    constructor
    · exact (lemma_01 a ⌈a⌉₊ ha hn₁).mpr (ceil_le_sq a ha)
    · exact (lemma_02 a ⌈1 / a⌉₊ ha hn₂).mpr
        (ceil_le_sq (1 / a) hrecip)
