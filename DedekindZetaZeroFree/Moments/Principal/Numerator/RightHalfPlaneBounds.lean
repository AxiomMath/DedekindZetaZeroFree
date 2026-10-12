module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.EulerLogarithm
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalIncompleteEulerNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalNumerator
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem rightHalfPlane_bound (R : PrincipalMellin.ActualRecipe S η)
    (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖R.L s‖ ≤ B := by
  let C := idealAbsoluteSum F a
  have hC : 0 ≤ C := by
    unfold C idealAbsoluteSum
    exact tsum_nonneg (fun I => by unfold idealAbsoluteWeight; split_ifs <;> positivity)
  refine ⟨(C + 1) * 2 ^ R.A.Sf.card, by positivity, ?_⟩
  intro s hs
  have hfull : ‖R.continuation.L s‖ ≤ C :=
    heckeDirichlet_hasSum_norm_le F a ha R.A.modulus R.A.modulus_ne_zero
      R.target s hs _ (R.continuation.series s (ha.trans_le hs))
  have hlocal : ∀ v ∈ R.A.Sf,
      ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 2 := by
    intro v hv
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hpow : ‖R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 1 := by
      rw [norm_mul]
      have hn := RayUnitary.ray_character_norm_le_one F R.A.modulus R.A.modulus_ne_zero
        R.target v.asIdeal
      have hp : ‖comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 1 := by
        rw [MellinZeroFree.norm_comparisonRealPower, Complex.neg_re, Real.exp_le_one_iff]
        have hl := Real.log_pos hQ
        have hr : 0 < s.re := lt_trans zero_lt_one (ha.trans_le hs)
        nlinarith
      exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa using hp)
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  change ‖R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤ _
  rw [norm_mul, norm_prod]
  have hmask : (∏ v ∈ R.A.Sf,
      ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖) ≤
      2 ^ R.A.Sf.card := by
    simpa using Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) hlocal
  exact mul_le_mul (hfull.trans (by dsimp [C]; linarith)) hmask
    (Finset.prod_nonneg (fun v hv => norm_nonneg _)) (by positivity)

theorem rightHalfPlane_reciprocal_bound
    (R : PrincipalMellin.ActualRecipe S η) (a : ℝ) (ha : 1 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → ‖(R.L s)⁻¹‖ ≤ B := by
  let coeff : ExteriorIdeal (⊤ : Ideal (NumberField.RingOfIntegers F)) → ℂ :=
    fun I => R.target I.val
  let M : ℝ := Real.exp ((3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal F, (idealNorm I.val) ^ (-a))
  have hM : 0 < M := Real.exp_pos _
  have hfull : ∀ s : ℂ, a ≤ s.re → ‖(R.continuation.L s)⁻¹‖ ≤ M := by
    intro s hs
    have hexp : Complex.exp (HeckeLogProof.eulerLog coeff s) = R.continuation.L s := by
      rw [HeckeLogProof.exp_eulerLog _
        (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
        s (ha.trans_le hs)]
      have hsupport : Function.support (fun I : Ideal (NumberField.RingOfIntegers F) =>
          R.target I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (NumberField.RingOfIntegers F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
        intro I hI
        simp only [Function.mem_support] at hI
        refine ⟨?_, by simp⟩
        intro hzero
        have hη : R.target I = 0 := (R.target.eq_zero_iff' I).mpr (Or.inl hzero)
        exact hI (by simpa only [hη, zero_mul])
      exact ((hasSum_subtype_iff_of_support_subset hsupport).mpr
        (R.continuation.series s (ha.trans_le hs))).tsum_eq
    rw [← hexp, ← Complex.exp_neg, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := HeckeLogProof.eulerLog_norm_le coeff
      (HeckeLogProof.ray_isCoefficient R.A.modulus R.A.modulus_ne_zero R.target)
      a ha s hs
    rw [Complex.neg_re]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans h
  let u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℝ :=
    fun v => (1 - Real.exp (-a * Real.log (idealNorm v.asIdeal)))⁻¹
  have hupos : ∀ v, 0 < u v := by
    intro v
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hlog := Real.log_pos hQ
    dsimp [u]
    apply inv_pos.mpr
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    nlinarith
  refine ⟨M * ∏ v ∈ R.A.Sf, u v,
    mul_pos hM (Finset.prod_pos (fun v hv => hupos v)), ?_⟩
  intro s hs
  have hlocal : ∀ v, ‖(1 - R.target v.asIdeal *
      comparisonRealPower (idealNorm v.asIdeal) (-s))⁻¹‖ ≤ u v := by
    intro v
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hlog := Real.log_pos hQ
    have hpow : ‖R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤
        Real.exp (-a * Real.log (idealNorm v.asIdeal)) := by
      rw [norm_mul]
      have hn := RayUnitary.ray_character_norm_le_one F R.A.modulus
        R.A.modulus_ne_zero R.target v.asIdeal
      calc
        _ ≤ 1 * ‖comparisonRealPower (idealNorm v.asIdeal) (-s)‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        _ = Real.exp (-s.re * Real.log (idealNorm v.asIdeal)) := by
          rw [one_mul, MellinZeroFree.norm_comparisonRealPower, Complex.neg_re]
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    rw [norm_inv]
    apply inv_anti₀ (inv_pos.mp (hupos v))
    have ht := norm_sub_norm_le (1 : ℂ)
      (R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
    rw [norm_one] at ht
    dsimp [u] at *
    linarith
  change ‖(R.continuation.L s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)))⁻¹‖ ≤ _
  rw [mul_inv_rev, norm_mul]
  calc
    _ ≤ (∏ v ∈ R.A.Sf, u v) * M := by
      apply mul_le_mul
      · rw [← Finset.prod_inv_distrib, norm_prod]
        exact Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) (fun v hv => hlocal v)
      · exact hfull s hs
      · exact norm_nonneg _
      · exact (Finset.prod_pos (fun v hv => hupos v)).le
    _ = _ := mul_comm _ _

end
end DedekindZetaZeroFree.PrincipalNumerator
