module

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaFunctionalEquationPair

@[expose] public section

noncomputable section
open Classical MeasureTheory NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

open DedekindZetaZeroFree.AbelianQuotient.Theta

theorem mixedThetaPair_tailExponent_pos (F : Type) [Field F] [NumberField F] :
    0 < 2 / (Module.finrank ℚ F : ℝ) := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := F)))

private theorem centered_integral_tail (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (q : Angular F → Angular F)
    (hq : Continuous q) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∫ u in angularCube F, (mixedRadialTheta F I t (q u) - 1)‖ ≤
        A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ F : ℝ))) := by
  let box : Set (Angular F) := Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1)
  have hc : IsCompact box := isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hsub : angularCube F ⊆ box := by
    intro u hu i hi
    exact ⟨(hu i hi).1, (hu i hi).2.le⟩
  have hv : volume (angularCube F) = 1 := by
    simp [angularCube, Real.volume_pi_Ico]
  obtain ⟨A, B, hA, hB, htail⟩ := mixedRadialTheta_uniform_exponential_tail F I
    (q '' box) (hc.image hq)
  refine ⟨A, B, hA, hB, ?_⟩
  intro t ht
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp [hv])
    (fun u hu ↦ htail t ht (q u) (Set.mem_image_of_mem q (hsub hu)))
  simpa [Measure.real, hv] using h

private theorem decay_rate_mono (a b p t : ℝ) (hab : a ≤ b) (ht : 0 ≤ t) :
    Real.exp (-b * t ^ p) ≤ Real.exp (-a * t ^ p) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hab) (Real.rpow_nonneg ht p)

private theorem finite_sum_tail {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (p : ℝ)
    (h : ∀ i ∈ s, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f i t‖ ≤ A * Real.exp (-B * t ^ p)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖∑ i ∈ s, f i t‖ ≤ A * Real.exp (-B * t ^ p) := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, 1, one_pos, one_pos, ?_⟩
      intro t ht
      simpa using (Real.exp_pos (-1 * t ^ p)).le
  | @insert i s hi ih =>
      obtain ⟨A, B, hA, hB, hb⟩ := h i (Finset.mem_insert_self i s)
      obtain ⟨C, D, hC, hD, hd⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
      refine ⟨A + C, min B D, add_pos hA hC, lt_min hB hD, ?_⟩
      intro t ht
      rw [Finset.sum_insert hi]
      have ht0 : 0 ≤ t := le_trans zero_le_one ht
      calc
        ‖f i t + ∑ j ∈ s, f j t‖ ≤ ‖f i t‖ + ‖∑ j ∈ s, f j t‖ := norm_add_le _ _
        _ ≤ A * Real.exp (-B * t ^ p) + C * Real.exp (-D * t ^ p) :=
          add_le_add (hb t ht) (hd t ht)
        _ ≤ A * Real.exp (-(min B D) * t ^ p) + C * Real.exp (-(min B D) * t ^ p) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (decay_rate_mono _ _ _ _ (min_le_left _ _) ht0) hA.le)
            (mul_le_mul_of_nonneg_left (decay_rate_mono _ _ _ _ (min_le_right _ _) ht0) hC.le)
        _ = (A + C) * Real.exp (-(min B D) * t ^ p) := (add_mul _ _ _).symm

private theorem scaled_sum_tail {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (p : ℝ) (c : ℂ)
    (h : ∀ i, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f i t - 1‖ ≤ A * Real.exp (-B * t ^ p)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖c * ∑ i, f i t - c * (Fintype.card ι : ℂ)‖ ≤
        A * Real.exp (-B * t ^ p) := by
  obtain ⟨A, B, hA, hB, hb⟩ := finite_sum_tail Finset.univ
    (fun i t ↦ f i t - 1) p (fun i _ ↦ h i)
  refine ⟨(‖c‖ + 1) * A, B, mul_pos (by positivity) hA, hB, ?_⟩
  intro t ht
  have heq : c * ∑ i, f i t - c * (Fintype.card ι : ℂ) = c * ∑ i, (f i t - 1) := by
    simp [Finset.sum_sub_distrib, mul_sub]
  rw [heq, norm_mul]
  calc
    ‖c‖ * ‖∑ i, (f i t - 1)‖ ≤ ‖c‖ * (A * Real.exp (-B * t ^ p)) :=
      mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
    _ ≤ (‖c‖ + 1) * (A * Real.exp (-B * t ^ p)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((‖c‖ + 1) * A) * Real.exp (-B * t ^ p) := (mul_assoc _ _ _).symm

theorem mixedThetaPair_exponential_tail (F : Type) [Field F] [NumberField F] :
    let P := DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F
    let p := 2 / (Module.finrank ℚ F : ℝ)
    0 < p ∧ ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      (‖P.f t - P.f₀‖ ≤ A * Real.exp (-B * t ^ p) ∧
       ‖P.g t - P.g₀‖ ≤ A * Real.exp (-B * t ^ p)) := by
  dsimp only
  refine ⟨mixedThetaPair_tailExponent_pos F, ?_⟩
  have hf : ∀ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
        ‖mixedAngularAverage F I t - 1‖ ≤
          A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ F : ℝ))) := by
    intro I
    obtain ⟨A, B, hA, hB, hb⟩ := centered_integral_tail F I id continuous_id
    refine ⟨A, B, hA, hB, ?_⟩
    intro t ht
    rw [mixedAngularAverage_sub_one F I t (lt_of_lt_of_le zero_lt_one ht)]
    exact hb t ht
  have hg : ∀ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
        ‖mixedNegAngularAverage F I t - 1‖ ≤
          A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ F : ℝ))) := by
    intro I
    obtain ⟨A, B, hA, hB, hb⟩ := centered_integral_tail F I (fun u ↦ -u) continuous_neg
    refine ⟨A, B, hA, hB, ?_⟩
    intro t ht
    rw [mixedNegAngularAverage_sub_one F I t (lt_of_lt_of_le zero_lt_one ht)]
    exact hb t ht
  obtain ⟨A, B, hA, hB, hb⟩ := scaled_sum_tail
    (fun C : ClassGroup (𝓞 F) ↦ mixedAngularAverage F
      (FractionalIdeal.mk0 F (inverseClassIdealRepresentative F C)))
    (2 / (Module.finrank ℚ F : ℝ)) (alpha F : ℂ) (fun C ↦ hf _)
  obtain ⟨C, D, hC, hD, hd⟩ := scaled_sum_tail
    (fun C : ClassGroup (𝓞 F) ↦ mixedNegAngularAverage F
      (traceDualIdealUnit F (FractionalIdeal.mk0 F (inverseClassIdealRepresentative F C))))
    (2 / (Module.finrank ℚ F : ℝ)) (alpha F : ℂ) (fun C ↦ hg _)
  refine ⟨A + C, min B D, add_pos hA hC, lt_min hB hD, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  constructor
  · change ‖(alpha F : ℂ) * ∑ C, mixedAngularAverage F
        (FractionalIdeal.mk0 F (inverseClassIdealRepresentative F C)) t -
        (alpha F : ℂ) * (Fintype.card (ClassGroup (𝓞 F)) : ℂ)‖ ≤ _
    calc
      _ ≤ A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ F : ℝ))) := hb t ht
      _ ≤ A * Real.exp (-(min B D) * t ^ (2 / (Module.finrank ℚ F : ℝ))) :=
        mul_le_mul_of_nonneg_left (decay_rate_mono _ _ _ _ (min_le_left _ _) ht0) hA.le
      _ ≤ (A + C) * Real.exp (-(min B D) * t ^ (2 / (Module.finrank ℚ F : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC.le) (Real.exp_pos _).le
  · change ‖(alpha F : ℂ) * ∑ C, mixedNegAngularAverage F
        (traceDualIdealUnit F (FractionalIdeal.mk0 F (inverseClassIdealRepresentative F C))) t -
        (alpha F : ℂ) * (Fintype.card (ClassGroup (𝓞 F)) : ℂ)‖ ≤ _
    calc
      _ ≤ C * Real.exp (-D * t ^ (2 / (Module.finrank ℚ F : ℝ))) := hd t ht
      _ ≤ C * Real.exp (-(min B D) * t ^ (2 / (Module.finrank ℚ F : ℝ))) :=
        mul_le_mul_of_nonneg_left (decay_rate_mono _ _ _ _ (min_le_right _ _) ht0) hC.le
      _ ≤ (A + C) * Real.exp (-(min B D) * t ^ (2 / (Module.finrank ℚ F : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (Real.exp_pos _).le

end DedekindZetaZeroFree.Hecke

end
