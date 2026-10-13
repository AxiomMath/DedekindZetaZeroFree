module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorInverseBound

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

theorem qExp_mul_one_sub_c : DetectorDef.qExp * (1 - DetectorDef.c) = 891 / 500 := by
  unfold DetectorDef.qExp DetectorDef.c
  norm_num

theorem detector_inverse_bound (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 2 ≤ U → ∀ (t : ℝ)
      (ω : Detector.PrimitiveFrequencyCharacter F),
      ‖DetectorDef.D F U ω.character ((DetectorDef.c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * U ^ (DetectorDef.qExp * (1 - DetectorDef.c)) := by
  obtain ⟨C, hC, hbound⟩ := Detector.ideal_norm_summation_bounds F
  refine ⟨C, hC, ?_⟩
  intro U hU t ω
  have hU0 : 0 ≤ U := by linarith
  have hq : (0 : ℝ) < DetectorDef.qExp := by unfold DetectorDef.qExp; norm_num
  have hc0 : (0 : ℝ) < DetectorDef.c := by unfold DetectorDef.c; norm_num
  have hc1 : DetectorDef.c ≤ 1 / 2 := by unfold DetectorDef.c; norm_num
  have hX1 : (1 : ℝ) ≤ U ^ DetectorDef.qExp :=
    Real.one_le_rpow (by linarith) hq.le
  have hX0 : (0 : ℝ) ≤ U ^ DetectorDef.qExp := by linarith
  obtain ⟨_, hsum⟩ := hbound (U ^ DetectorDef.qExp) hX1
  unfold DetectorDef.D
  set X : ℝ := U ^ DetectorDef.qExp with hXdef
  set e : ℝ := 1 / 2 - DetectorDef.c with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  let T := (Detector.ideals_bounded_norm_finite F X).toFinset
  let f : Ideal (𝓞 F) → ℂ := fun d =>
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
      (Detector.idealMoebius F d : ℂ) * ω.character d *
        (Ideal.absNorm d : ℂ) ^ (-((DetectorDef.c : ℂ) + (t : ℂ) * Complex.I)) else 0
  let h : Ideal (𝓞 F) → ℝ := fun d =>
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
      (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) else 0
  have hf : Function.support f ⊆ (T : Set (Ideal (𝓞 F))) := by
    intro d hd
    have hdn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X := by
      by_contra h'
      exact hd (by simp only [f]; exact if_neg h')
    simp only [T, Finset.mem_coe]
    exact (Detector.ideals_bounded_norm_finite F X).mem_toFinset.mpr hdn
  have hh : Function.support h ⊆ (T : Set (Ideal (𝓞 F))) := by
    intro d hd
    have hdn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X := by
      by_contra h'
      exact hd (by simp only [h]; exact if_neg h')
    simp only [T, Finset.mem_coe]
    exact (Detector.ideals_bounded_norm_finite F X).mem_toFinset.mpr hdn
  have hterm (d : Ideal (𝓞 F)) : ‖f d‖ ≤ X ^ e * h d := by
    by_cases hd : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X
    · have hn : 0 < Ideal.absNorm d :=
        Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.1)
      have hn1 : 1 ≤ (Ideal.absNorm d : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (Ideal.absNorm d : ℝ) := by linarith
      have hμ : ‖(Detector.idealMoebius F d : ℂ)‖ ≤ 1 := by
        unfold Detector.idealMoebius UniqueFactorizationMonoid.moebius
        split <;> simp [Int.cast_pow]
      have hωnorm := RayUnitary.ray_character_norm_le_one F _ ω.conductor_ne_zero ω.character d
      have hprod : ‖(Detector.idealMoebius F d : ℂ)‖ * ‖ω.character d‖ ≤ 1 := by
        nlinarith [norm_nonneg (Detector.idealMoebius F d : ℂ), norm_nonneg (ω.character d)]
      have hpow : ‖(Ideal.absNorm d : ℂ) ^ (-((DetectorDef.c : ℂ) + (t : ℂ) * Complex.I))‖
          = (Ideal.absNorm d : ℝ) ^ (-DetectorDef.c) := by
        rw [Complex.norm_natCast_cpow_of_pos hn]
        simp [DetectorDef.c]
      have hsplit : (Ideal.absNorm d : ℝ) ^ (-DetectorDef.c) =
          (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm d : ℝ) ^ e := by
        rw [← Real.rpow_add hn0]
        congr 1
        rw [he]; ring
      have hle : (Ideal.absNorm d : ℝ) ^ e ≤ X ^ e :=
        Real.rpow_le_rpow hn0.le hd.2 he0
      have hnn : (0 : ℝ) ≤ (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg hn0.le _
      simp only [f, h, if_pos hd]
      rw [norm_mul, norm_mul, hpow, hsplit]
      calc ‖(Detector.idealMoebius F d : ℂ)‖ * ‖ω.character d‖ *
            ((Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm d : ℝ) ^ e)
          ≤ 1 * ((Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) * X ^ e) := by
            apply mul_le_mul hprod _ (by positivity) zero_le_one
            exact mul_le_mul_of_nonneg_left hle hnn
        _ = X ^ e * (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    · have h1 : f d = 0 := if_neg hd
      have h2 : h d = 0 := if_neg hd
      rw [h1, h2]
      simp
  have hXe : X ^ (1 / 2 : ℝ) * X ^ e = X ^ (1 - DetectorDef.c) := by
    rw [← Real.rpow_add (by linarith)]
    congr 1
    rw [he]; ring
  have hfin : ∑ᶠ d, f d = ∑ d ∈ T, f d := finsum_eq_sum_of_support_subset f hf
  have hhfin : ∑ᶠ d, h d = ∑ d ∈ T, h d := finsum_eq_sum_of_support_subset h hh
  have hXpow : (U ^ DetectorDef.qExp) ^ (1 - DetectorDef.c) =
      U ^ (DetectorDef.qExp * (1 - DetectorDef.c)) := by
    rw [Real.rpow_mul hU0]
  calc ‖∑ᶠ d, f d‖ = ‖∑ d ∈ T, f d‖ := by rw [hfin]
    _ ≤ ∑ d ∈ T, ‖f d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ T, X ^ e * h d := Finset.sum_le_sum (fun d _ => hterm d)
    _ = X ^ e * ∑ d ∈ T, h d := by rw [Finset.mul_sum]
    _ = X ^ e * ∑ᶠ d, h d := by rw [hhfin]
    _ ≤ X ^ e * (C * X ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hX0 _)
    _ = C * X ^ (1 - DetectorDef.c) := by rw [← hXe]; ring
    _ = C * U ^ (DetectorDef.qExp * (1 - DetectorDef.c)) := by rw [hXdef, hXpow]

end

end DedekindZetaZeroFree.Quantitative.DetectorInverseBound
