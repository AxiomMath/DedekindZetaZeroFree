module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.OmittedEulerProductBounds
public import DedekindZetaZeroFree.ZeroDetection.Conductors.HolomorphicLogarithmControl
public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.IdealMoebiusInverse
public import DedekindZetaZeroFree.Analysis.ExponentialMellinInversion

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory
open scoped NumberField Classical

namespace Detector

noncomputable def canonicalRayHeckeL
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (hω : ω.IsPrimitive) : ℂ → ℂ :=
  if hp : ω.IsPrincipal then
    (principalRayHeckeData F htc m hm ω hω hp).L
  else
    (nonprincipalRayHeckeData F htc m hm ω hω hp).L

noncomputable def smoothedDetectorSummand
    (F : Type) [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (U : ℝ) (s : ℂ)
    (n : Ideal (𝓞 F)) : ℂ :=
  if n ≠ ⊥ then
    (truncatedIdealMoebius F U n : ℂ) * ω n * (Ideal.absNorm n : ℂ) ^ (-s) *
      (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ (10 : ℕ)) : ℂ)
  else 0

noncomputable def smoothedDetector
    (F : Type) [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (U : ℝ) (s : ℂ) : ℂ :=
  ∑' n : Ideal (𝓞 F), smoothedDetectorSummand F ω U s n

noncomputable def initialMellinIntegrand
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (hω : ω.IsPrimitive)
    (U : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  let z : ℂ := 2 + Complex.I * (t : ℂ)
  Complex.Gamma z * ((U ^ (10 : ℕ) : ℝ) : ℂ) ^ z *
    canonicalRayHeckeL F htc m hm ω hω (s + z) *
    truncatedIdealInverse F ω U (s + z)

end Detector

private theorem mellin_ideals_countable (F : Type) [Field F] [NumberField F] :
    Countable (Ideal (𝓞 F)) := by
  apply Set.countable_univ_iff.mp
  have h : (⋃ N : ℕ, {n : Ideal (𝓞 F) | Ideal.absNorm n ≤ N}).Countable :=
    Set.countable_iUnion fun N => (Ideal.finite_setOfPred_absNorm_le N).countable
  have he : (⋃ N : ℕ, {n : Ideal (𝓞 F) | Ideal.absNorm n ≤ N}) = Set.univ := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨Ideal.absNorm n, le_rfl⟩
  rwa [he] at h

private theorem mellin_canonical_series
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (hω : ω.IsPrimitive) (w : ℂ) (hw : 1 < w.re) :
    Detector.canonicalRayHeckeL F htc m hm ω hω w = Detector.idealLSeries F ω w := by
  classical
  have hz : ω ⊥ = 0 := (ω.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  have he : (fun n : Ideal (𝓞 F) => if n ≠ ⊥ then ω n * (Ideal.absNorm n : ℂ) ^ (-w) else 0) =
      (fun n : Ideal (𝓞 F) => ω n * (Ideal.absNorm n : ℂ) ^ (-w)) := by
    funext n
    by_cases hn : n = ⊥ <;> simp [hn, hz]
  unfold Detector.canonicalRayHeckeL Detector.idealLSeries
  rw [he]
  split_ifs with hp
  · exact ((principalRayHeckeData F htc m hm ω hω hp).series w hw).tsum_eq.symm
  · exact ((nonprincipalRayHeckeData F htc m hm ω hω hp).series w hw).tsum_eq.symm

private theorem mellin_power (q X : ℝ) (hq : 0 < q) (hX : 0 < X) (s z : ℂ) :
    (q : ℂ) ^ (-s) * ((q / X : ℝ) : ℂ) ^ (-z) =
      (X : ℂ) ^ z * (q : ℂ) ^ (-(s + z)) := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq.le hX.le,
    Complex.cpow_neg (X : ℂ), div_inv_eq_mul,
    neg_add, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq.ne')]
  ring

 def mellin_coefficient
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) (w : ℂ) (n : Ideal (𝓞 F)) : ℂ :=
  if n ≠ ⊥ then (Detector.truncatedIdealMoebius F U n : ℂ) *
    ω n * (Ideal.absNorm n : ℂ) ^ (-w) else 0

 def mellin_profile
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) (s : ℂ) (n : Ideal (𝓞 F)) (t : ℝ) : ℂ :=
  let z : ℂ := 2 + Complex.I * (t : ℂ)
  Complex.Gamma z * ((U ^ (10 : ℕ) : ℝ) : ℂ) ^ z *
    mellin_coefficient F ω U (s + z) n

private theorem mellin_profile_norm
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) (hU : 2 ≤ U) (s : ℂ)
    (n : Ideal (𝓞 F)) (t : ℝ) :
    ‖mellin_profile F ω U s n t‖ =
      ‖Complex.Gamma (2 + Complex.I * (t : ℂ))‖ * U ^ (20 : ℕ) *
        ‖mellin_coefficient F ω U (s + 2) n‖ := by
  have hX : 0 < U ^ (10 : ℕ) := by positivity
  dsimp only [mellin_profile, mellin_coefficient]
  by_cases hn : n ≠ ⊥
  · have hq : (0 : ℝ) < Ideal.absNorm n := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
    simp only [ite_true, if_pos hn, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX,
      show (2 + Complex.I * (t : ℂ)).re = 2 by simp,
      Real.rpow_two, ← pow_mul]
    norm_num only [Nat.reduceMul]
    have he : ‖(Ideal.absNorm n : ℂ) ^ (-(s + (2 + Complex.I * (t : ℂ))))‖ =
        ‖(Ideal.absNorm n : ℂ) ^ (-(s + 2))‖ := by
      simp only [← Complex.ofReal_natCast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.norm_cpow_eq_rpow_re_of_pos hq]
      simp
    simp only [if_pos hn, norm_mul, he]
  · simp [hn]

private theorem mellin_profile_integrable
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) (hU : 2 ≤ U) (s : ℂ)
    (n : Ideal (𝓞 F)) : Integrable (mellin_profile F ω U s n) := by
  classical
  by_cases hn : n ≠ ⊥
  · have hq : (0 : ℝ) < Ideal.absNorm n := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
    have hX : 0 < U ^ (10 : ℕ) := by positivity
    have hi := (detector_sz_exp_inversion_integrable
      ((Ideal.absNorm n : ℝ) / U ^ (10 : ℕ)) (div_pos hq hX)).const_mul
      ((Detector.truncatedIdealMoebius F U n : ℂ) * ω n * (Ideal.absNorm n : ℂ) ^ (-s))
    apply hi.congr
    filter_upwards [] with t
    dsimp only [mellin_profile, mellin_coefficient]
    rw [if_pos hn, mul_comm (t : ℂ) Complex.I]
    have hp := mellin_power (Ideal.absNorm n) (U ^ (10 : ℕ)) hq hX s
      (2 + Complex.I * (t : ℂ))
    linear_combination ((Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
      Complex.Gamma (2 + Complex.I * (t : ℂ))) * hp
  · have he : mellin_profile F ω U s n = 0 := by
      funext t
      simp [mellin_profile, mellin_coefficient, hn]
    rw [he]
    exact integrable_zero ℝ ℂ volume

private theorem mellin_profile_inversion
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) (hU : 2 ≤ U) (s : ℂ)
    (n : Ideal (𝓞 F)) :
    Detector.smoothedDetectorSummand F ω U s n =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, mellin_profile F ω U s n t := by
  classical
  by_cases hn : n ≠ ⊥
  · have hq : (0 : ℝ) < Ideal.absNorm n := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
    have hX : 0 < U ^ (10 : ℕ) := by positivity
    have hp : mellin_profile F ω U s n = fun t : ℝ =>
        ((Detector.truncatedIdealMoebius F U n : ℂ) * ω n * (Ideal.absNorm n : ℂ) ^ (-s)) *
        (Complex.Gamma (2 + (t : ℂ) * Complex.I) *
          (((Ideal.absNorm n : ℝ) / U ^ (10 : ℕ) : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * Complex.I))) := by
      funext t
      dsimp only [mellin_profile, mellin_coefficient]
      rw [if_pos hn, mul_comm (t : ℂ) Complex.I]
      have he := mellin_power (Ideal.absNorm n) (U ^ (10 : ℕ)) hq hX s
        (2 + Complex.I * (t : ℂ))
      linear_combination -((Detector.truncatedIdealMoebius F U n : ℂ) * ω n *
        Complex.Gamma (2 + Complex.I * (t : ℂ))) * he
    rw [hp, integral_const_mul]
    unfold Detector.smoothedDetectorSummand
    rw [if_pos hn]
    have hi := detector_sz_exp_inversion ((Ideal.absNorm n : ℝ) / U ^ (10 : ℕ)) (div_pos hq hX)
    rw [← neg_div] at hi
    rw [hi]
    ring
  · simp [Detector.smoothedDetectorSummand, mellin_profile, mellin_coefficient, hn]

theorem detector_sz_mellin_identity
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F)
    (U : ℝ) (hU : 2 ≤ U) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ω : RayClassCharacter F m) (hω : ω.IsPrimitive)
    (s : ℂ) (hsLower : (249 / 250 : ℝ) ≤ s.re) (hsUpper : s.re ≤ 1) :
    Summable (fun n : Ideal (𝓞 F) => ‖Detector.smoothedDetectorSummand F ω U s n‖) ∧
      Integrable (Detector.initialMellinIntegrand F htc m hm ω hω U s) volume ∧
      Detector.smoothedDetector F ω U s =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Detector.initialMellinIntegrand F htc m hm ω hω U s t := by
  classical
  letI := mellin_ideals_countable F
  have hs2 : 1 < (s + 2).re := by simp only [Complex.add_re, Complex.natCast_re]; norm_num at *; linarith
  have hc : Summable (mellin_coefficient F ω U (s + 2)) :=
    (Detector.idealLSeries_mul_truncatedInverse F m hm ω hω U hU (s + 2) hs2).1
  have hcn := hc.norm
  have hg : Integrable (fun t : ℝ => ‖Complex.Gamma (2 + Complex.I * (t : ℂ))‖) := by
    simpa [mul_comm] using (detector_sz_exp_inversion_integrable 1 (by norm_num)).norm
  have hp := mellin_profile_integrable F ω U hU s
  have hn : Summable (fun n : Ideal (𝓞 F) => ∫ t : ℝ, ‖mellin_profile F ω U s n t‖) := by
    have he (n : Ideal (𝓞 F)) :
        (∫ t : ℝ, ‖mellin_profile F ω U s n t‖) =
        ((∫ t : ℝ, ‖Complex.Gamma (2 + Complex.I * (t : ℂ))‖) * U ^ (20 : ℕ)) *
          ‖mellin_coefficient F ω U (s + 2) n‖ := by
      simp_rw [mellin_profile_norm F ω U hU s n]
      rw [integral_mul_const, integral_mul_const]
    simp_rw [he]
    exact hcn.mul_left _
  have ha : Summable (fun n : Ideal (𝓞 F) => ‖Detector.smoothedDetectorSummand F ω U s n‖) := by
    apply (hn.mul_left ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖).of_nonneg_of_le
      (fun n => norm_nonneg _)
    intro n
    rw [mellin_profile_inversion F ω U hU s n, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
  have hpoint (t : ℝ) : (∑' n : Ideal (𝓞 F), mellin_profile F ω U s n t) =
      Detector.initialMellinIntegrand F htc m hm ω hω U s t := by
    let z : ℂ := 2 + Complex.I * (t : ℂ)
    have hw : 1 < (s + z).re := by dsimp [z]; simp only [Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.natCast_re, mul_zero,
      zero_mul, sub_zero, add_zero]; linarith
    have hsum := (Detector.idealLSeries_mul_truncatedInverse F m hm ω hω U hU (s + z) hw).2
    have he := (hsum.mul_left (Complex.Gamma z * ((U ^ (10 : ℕ) : ℝ) : ℂ) ^ z)).tsum_eq
    change (∑' n : Ideal (𝓞 F),
      (Complex.Gamma z * ((U ^ (10 : ℕ) : ℝ) : ℂ) ^ z) * mellin_coefficient F ω U (s + z) n) = _
    unfold mellin_coefficient
    rw [he]
    dsimp only [Detector.initialMellinIntegrand]
    rw [mellin_canonical_series F htc m hm ω hω (s + z) hw]
    ring
  have hint : Integrable (fun t : ℝ => ∑' n : Ideal (𝓞 F), mellin_profile F ω U s n t) := by
    apply (hg.mul_const (U ^ (20 : ℕ) * ∑' n : Ideal (𝓞 F),
      ‖mellin_coefficient F ω U (s + 2) n‖)).mono'
      (AEStronglyMeasurable.tsum fun n => (hp n).aestronglyMeasurable)
    filter_upwards [] with t
    have hnorm : Summable (fun n : Ideal (𝓞 F) => ‖mellin_profile F ω U s n t‖) := by
      simp_rw [mellin_profile_norm F ω U hU s]
      exact hcn.mul_left _
    calc
      _ ≤ ∑' n : Ideal (𝓞 F), ‖mellin_profile F ω U s n t‖ := norm_tsum_le_tsum_norm hnorm
      _ = _ := by simp_rw [mellin_profile_norm F ω U hU s]; rw [tsum_mul_left]; ring
  refine ⟨ha, ?_, ?_⟩
  · simpa only [hpoint] using hint
  · unfold Detector.smoothedDetector
    simp_rw [mellin_profile_inversion F ω U hU s]
    rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hp hn]
    simp only [hpoint]

end
end DedekindZetaZeroFree
