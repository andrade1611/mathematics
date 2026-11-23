import Mathlib
/-!
Sea $a\in\mathbb{R}$ con $a>0$ y
$n\in\mathbb{N}\setminus\rllav{0}$
entonces $a\leq(an)^2$ si y s\'olo si
 $\frac{1}{a}\leq n^2$
-/

theorem lemma_02
    (a : ℝ) (n : ℕ)
    (ha : 0 < a)
    (_hn : n ≠ 0) :
    a ≤ (a * (n : ℝ))^2 ↔ 1 / a ≤ (n : ℝ)^2 := by
    calc
        a ≤ (a * (n : ℝ))^2 ↔ a ≤ a^2 * (n : ℝ)^2 := by
            rw [mul_pow]
        _ ↔ 1 ≤ a * (n : ℝ)^2 := by
            simpa only [mul_one, pow_two, mul_assoc] using
              (mul_le_mul_iff_of_pos_left ha :
                a * 1 ≤ a * (a * (n : ℝ)^2) ↔
                1 ≤ a * (n : ℝ)^2)
        _ ↔ 1 / a ≤ (n : ℝ)^2 := by
            simpa only [mul_comm] using
                (div_le_iff₀ ha : 1 / a ≤ (n : ℝ)^2 ↔
                    1 ≤ (n : ℝ)^2 * a).symm
