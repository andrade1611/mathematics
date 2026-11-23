/-
Copyright (c) 2026 Carlos Flores Andrade.
SPDX-License-Identifier: MIT
Repositorio: https://github.com/andrade1611/mathematics
-/

import Mathlib

/-!
Sea $a\in\mathbb{R}$ con $a>0$ y $n\in
\mathbb{N}\setminus\rllav{0}$, entonces
$\rpar{\frac{a}{n}}^2\leq a$ si y s\'olo
si $a\leq n^2$
-/

theorem lemma_01
    (a : ℝ) (n : ℕ)
    (ha : 0 < a)
    (hn : n ≠ 0) :
    (a / (n : ℝ))^2 ≤ a ↔ a ≤ (n : ℝ)^2 := by
    have hnR : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
    have hn2 : 0 < (n : ℝ)^2 := by
        positivity
    calc
        (a / (n : ℝ))^2 ≤ a ↔ a^2 ≤ a * (n : ℝ)^2 := by
            rw [div_pow]
            exact div_le_iff₀ hn2
        _ ↔ a * a ≤ a * (n : ℝ)^2 := by rw [pow_two]
        _ ↔ a ≤ (n : ℝ)^2 := mul_le_mul_iff_of_pos_left ha
