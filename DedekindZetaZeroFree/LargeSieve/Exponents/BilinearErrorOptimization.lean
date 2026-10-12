module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SmallCutoffComparison
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Errors.DyadicSummation

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical BigOperators

open DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms

theorem bilinear_error_optimization
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : AllIndexNormalizedFamilyData Q) (hcore : D.bad = c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    {α : ℝ} (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ ε : ℝ, 0 < ε → ∃ δ A : ℝ,
      0 < δ ∧ δ < ε / (8 * (α + 1)) ∧ 0 ≤ A ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N →
        max 1 (N ^ 2 / M * Real.rpow (M * N) ε) ≤ K →
        K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) (hd : Squarefree d)
        (hdc : d ⊔ c = ⊤), (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
      let ctx : Context Q :=
        { D := D, core := hcore, hF := hF,
          M := M, N := N, K := K, δ := δ, W := W, hW := hW,
          d := d, hd0 := hd0, hd := hd, hdc := hdc, g := g, lam := lam }
      let errorMass : ℝ → Bool → ℝ := fun B unit =>
        ‖E1 ctx B unit‖ + ‖E2 ctx B unit‖ + ‖E3 ctx B unit‖ +
          ‖E4 ctx B unit‖ + ‖E5 ctx B unit‖
      errorMass 1 true + (∑ B ∈ dyadicScales ctx, errorMass B false) ≤
        A * (Ideal.absNorm d : ℝ) ^ 4 * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N) * energy F c N lam := by
  obtain ⟨C0, hC0, hsum⟩ :=
    bilinear_error_dyadic_sum F c Q D hcore hF W hW
  intro ε hε
  let ε' := ε / (α + 2)
  have hα2 : 0 < α + 2 := by linarith
  have hε' : 0 < ε' := div_pos hε hα2
  have hε'le : ε' ≤ ε := by
    dsimp [ε']
    exact (div_le_self hε.le (by linarith))
  obtain ⟨A, hA, hbound⟩ := hsum α ⟨hα₁, hα₂⟩ hExponent ε' hε'
  refine ⟨ε' / (8 * (C0 + 2)), A, by positivity, ?_, hA, ?_⟩
  · have hden : 8 * (α + 1) < (α + 2) * (8 * (C0 + 2)) := by
      nlinarith
    dsimp [ε']
    rw [div_div]
    exact div_lt_div_of_pos_left hε (by positivity) hden
  · intro M N K hM hN hKlow hKhigh d hd0 hd hdc hnN g lam
    have hM0 : 0 ≤ M := by linarith
    have hMN : 1 ≤ M * N := by nlinarith
    have hK : 1 ≤ K := (le_max_left _ _).trans hKlow
    have hK0 : 0 ≤ K := by linarith
    have hN0 : 0 ≤ N := by linarith
    have hpow : Real.rpow (M * N) (-ε) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hMN (show -ε ≤ 0 by linarith))
    have hKM : K ≤ M := hKhigh.trans (by nlinarith)
    have hn : 1 ≤ (Ideal.absNorm d : ℝ) := by
      have hn' : 1 ≤ Ideal.absNorm d := Nat.one_le_iff_ne_zero.mpr
        (fun hz => hd0 (Ideal.absNorm_eq_zero_iff.mp hz))
      exact_mod_cast hn'
    have hs := hbound M N K hM hN hK hKM d hd0 hd hdc hn hnN g lam
    have hpow' : Real.rpow (M * N) ε' ≤ Real.rpow (M * N) ε :=
      Real.rpow_le_rpow_of_exponent_le hMN hε'le
    have hE : 0 ≤ energy F c N lam := by unfold energy; positivity
    have hRp : 0 ≤ Real.rpow K (α - 1 / 2) := Real.rpow_nonneg hK0 _
    have hRε : 0 ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (by nlinarith) _
    have hbase : 0 ≤ M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) := by
      positivity
    have hextra : 0 ≤ Real.sqrt (M / K) * N := by positivity
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul
        (mul_le_mul_of_nonneg_left hpow' (by positivity))
        (le_add_of_nonneg_right hextra) hbase (by positivity)) hE)

end DedekindZetaZeroFree.LargeSieve.Sieve
