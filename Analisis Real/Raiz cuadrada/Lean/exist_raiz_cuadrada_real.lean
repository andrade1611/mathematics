import AlgebraFormalizada.RaizCuadrada.Teorema

/-! 
Sea $a\in\mathbb{R}$ con $a>0$. Entonces existe un \'unico $x>0$ tal que $x^2=a$.
-/

theorem exist_raiz_cuadrada_real (a : ℝ) (ha : 0 < a) :
    ∃! x : ℝ, 0 < x ∧ x^2 = a := by
    let A : Set ℝ := {x | 0 < x ∧ x^2 ≤ a}
    obtain ⟨hleft, hright⟩ := raiz_cuadrada_cotas a ha
    have hn : (0 : ℝ) < (⌈a⌉₊ : ℝ) := by
        exact_mod_cast (Nat.one_le_ceil_iff.mpr ha)
    have hA : a / (⌈a⌉₊ : ℝ) ∈ A := by
        exact ⟨div_pos ha hn, hleft⟩
    have hne : A.Nonempty := ⟨_, hA⟩
    have hBpos : 0 < a * (⌈1 / a⌉₊ : ℝ) := by
        have hrecip : 0 < 1 / a := by positivity
        have hceil : (0 : ℝ) < (⌈1 / a⌉₊ : ℝ) := by
            exact_mod_cast (Nat.one_le_ceil_iff.mpr hrecip)
        exact mul_pos ha hceil
    have hbdd : BddAbove A := by
        refine ⟨a * (⌈1 / a⌉₊ : ℝ), ?_⟩
        intro z hz
        by_contra h
        have hlt : a * (⌈1 / a⌉₊ : ℝ) < z := lt_of_not_ge h
        have hsq := (sq_lt_sq₀ hBpos.le hz.1.le).mpr hlt
        exact (not_lt_of_ge hright) (lt_of_lt_of_le hsq hz.2)
    let α := sSup A
    have hαpos : 0 < α := lt_of_lt_of_le hA.1 (le_csSup hbdd hA)
    have hcont : ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - α| < δ → |x^2 - α^2| < ε := by
        intro ε hε
        obtain ⟨δ, hδ, hd⟩ :=
            (Metric.continuousAt_iff.mp
                ((continuousAt_id : ContinuousAt (fun x : ℝ => x) α).pow 2)) ε hε
        refine ⟨δ, hδ, ?_⟩
        intro x hx
        simpa [Real.dist_eq] using (hd (x := x) (by simpa [Real.dist_eq] using hx))
    have hαle : α^2 ≤ a := by
        by_contra h
        have hlt : a < α^2 := lt_of_not_ge h
        obtain ⟨δ, hδ, hd⟩ := hcont (α^2 - a) (by linarith)
        obtain ⟨y, hy, hylow⟩ :=
            exists_lt_of_lt_csSup hne (sub_lt_self α hδ)
        have hyup : y ≤ α := le_csSup hbdd hy
        have hdist : |y - α| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
        have hsqdist := hd y hdist
        have hsqbound := (abs_lt.mp hsqdist).1
        have hyA : y^2 ≤ a := hy.2
        linarith
    have hαge : a ≤ α^2 := by
        by_contra h
        have hlt : α^2 < a := lt_of_not_ge h
        obtain ⟨δ, hδ, hd⟩ := hcont (a - α^2) (by linarith)
        let w := α + δ / 2
        have hwpos : 0 < w := by dsimp [w]; linarith
        have hwdist : |w - α| < δ := by
            dsimp [w]
            rw [add_sub_cancel_left, abs_of_pos (by linarith : 0 < δ / 2)]
            linarith
        have hsqdist := hd w hwdist
        have hwsq : w^2 ≤ a := by
            have hupper := (abs_lt.mp hsqdist).2
            linarith
        have hwA : w ∈ A := ⟨hwpos, hwsq⟩
        have hwle : w ≤ α := le_csSup hbdd hwA
        dsimp [w] at hwle
        linarith
    have hαsq : α^2 = a := le_antisymm hαle hαge
    refine ⟨α, ⟨hαpos, hαsq⟩, ?_⟩
    intro β hβ
    have hβA : β ∈ A := ⟨hβ.1, le_of_eq hβ.2⟩
    have hβle : β ≤ α := le_csSup hbdd hβA
    rcases lt_or_eq_of_le hβle with hβlt | hβα
    · obtain ⟨xβ, hxβA, hβxβ⟩ := exists_lt_of_lt_csSup hne hβlt
      have hsq : β^2 < xβ^2 :=
          (sq_lt_sq₀ hβ.1.le hxβA.1.le).mpr hβxβ
      have hcontra : a < xβ^2 := by rw [← hβ.2]; exact hsq
      exact False.elim ((not_lt_of_ge hxβA.2) hcontra)
    · exact hβα
