module

public import DedekindZetaZeroFree.Moments.Reflected.PowerfulSquarefreeTailBounds

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.RMParameterAbsorption
noncomputable section
open scoped NumberField BigOperators Classical

variable {F : Type} [Field F] [NumberField F]

private theorem rowDyad_finite (A : SArithmeticData F) (h : A.Exterior) (D : ℝ) :
    (RMTailCutoff.rowDyad A h D).Finite := by
  let f : ExteriorSquarefreeIdeal A.cS → NonzeroIdeal F :=
    fun d => ⟨d.val.val, d.val.property.1⟩
  apply Set.Finite.of_injOn (f := f) (t := normBoundedIdeals F (2 * D))
  · intro d hd
    exact hd.2.1.le
  · intro d _ e _ he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : NonzeroIdeal F => x.val) he
  · exact normBoundedIdeals_finite F (2 * D)

private theorem rowDyad_count (A : SArithmeticData F) (h : A.Exterior) (D C : ℝ)
    (hc : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ C * X)
    (hD : 1 ≤ D) : ((RMTailCutoff.rowDyad A h D).ncard : ℝ) ≤ 2 * C * D := by
  let f : ExteriorSquarefreeIdeal A.cS → NonzeroIdeal F :=
    fun d => ⟨d.val.val, d.val.property.1⟩
  have hn : (RMTailCutoff.rowDyad A h D).ncard ≤ (normBoundedIdeals F (2 * D)).ncard := by
    apply Set.ncard_le_ncard_of_injOn f (ht := normBoundedIdeals_finite F (2 * D))
    · intro d hd
      exact hd.2.1.le
    · intro d _ e _ he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : NonzeroIdeal F => x.val) he
  calc
    _ ≤ ((normBoundedIdeals F (2 * D)).ncard : ℝ) := by exact_mod_cast hn
    _ ≤ C * (2 * D) := hc _ (by linarith)
    _ = _ := by ring

theorem bounded_dyad_square_sum (A : SArithmeticData F) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P D : ℝ), 1 ≤ P → 1 ≤ D →
      ∀ (b : (h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P}) →
          {d : ExteriorSquarefreeIdeal A.cS //
            d ∈ RMTailCutoff.rowDyad A h.val D} → ℂ)
        (B : ℝ), 0 ≤ B → (∀ h d, ‖b h d‖ ≤ B) →
        (∑' h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P},
          ∑' d : {d : ExteriorSquarefreeIdeal A.cS //
            d ∈ RMTailCutoff.rowDyad A h.val D}, ‖b h d‖ ^ 2) ≤
          (K * B ^ 2) * Real.sqrt P * D := by
  obtain ⟨Cp, hCp, hp⟩ := exterior_powerful_dyad_count_bound F
  obtain ⟨Cd, _, hCd, _, hc⟩ := ideal_counting_harmonic_bounds F
  have hc' : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ Cd * X := by
    simpa using (hc Set.univ).1
  refine ⟨Cp * (2 * Cd), by positivity, ?_⟩
  intro P D hP hD b B hB hb
  have hV : 0 ≤ B ^ 2 := sq_nonneg B
  have hterm : ∀ h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P},
      ∀ d : {d : ExteriorSquarefreeIdeal A.cS // d ∈ RMTailCutoff.rowDyad A h.val D},
      ‖b h d‖ ^ 2 ≤ B ^ 2 := by
    intro h d
    exact pow_le_pow_left₀ (norm_nonneg _) (hb h d) 2
  letI := (exteriorPowerfulDyad_finite A.cS P).fintype
  have hrow : ∀ h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P},
      (∑' d : {d : ExteriorSquarefreeIdeal A.cS // d ∈ RMTailCutoff.rowDyad A h.val D},
        ‖b h d‖ ^ 2) ≤ (2 * Cd * D) * B ^ 2 := by
    intro h
    letI := (rowDyad_finite A h.val D).fintype
    calc
      _ ≤ ∑' d : {d : ExteriorSquarefreeIdeal A.cS //
            d ∈ RMTailCutoff.rowDyad A h.val D}, B ^ 2 :=
        Summable.tsum_le_tsum (hterm h) (Summable.of_finite) (Summable.of_finite)
      _ = ((RMTailCutoff.rowDyad A h.val D).ncard : ℝ) * B ^ 2 := by
        rw [tsum_const, nsmul_eq_mul, Nat.card_coe_set_eq]
      _ ≤ _ := mul_le_mul_of_nonneg_right (rowDyad_count A h.val D Cd hc' hD) hV
  calc
    _ ≤ ∑' h : {h : A.Exterior // h ∈ exteriorPowerfulDyad A.cS P},
        (2 * Cd * D) * B ^ 2 :=
      Summable.tsum_le_tsum hrow (Summable.of_finite) (Summable.of_finite)
    _ = ((exteriorPowerfulDyad A.cS P).ncard : ℝ) * ((2 * Cd * D) * B ^ 2) := by
      rw [tsum_const, nsmul_eq_mul, Nat.card_coe_set_eq]
    _ ≤ (Cp * Real.sqrt P) * ((2 * Cd * D) * B ^ 2) :=
      mul_le_mul_of_nonneg_right (hp A.cS A.cS_ne_zero P hP)
        (mul_nonneg (by positivity) hV)
    _ = _ := by ring

end
end DedekindZetaZeroFree.RepresentationTheory.RMParameterAbsorption
