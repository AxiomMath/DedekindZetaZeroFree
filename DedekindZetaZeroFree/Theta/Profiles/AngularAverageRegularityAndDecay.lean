module

public import DedekindZetaZeroFree.Theta.Profiles.UniformMixedThetaTail

@[expose] public section

noncomputable section

open Classical MeasureTheory NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

def angularBox : Set (Angular K) :=
  Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1)

private theorem compact_angularBox : IsCompact (angularBox K) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

private theorem cube_subset_box : angularCube K ⊆ angularBox K := by
  intro u hu i hi
  exact ⟨(hu i hi).1, (hu i hi).2.le⟩

private theorem measurable_cube : MeasurableSet (angularCube K) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ico)

private theorem volume_cube : volume (angularCube K) = 1 := by
  simp [angularCube, Real.volume_pi_Ico]

private theorem continuous_slice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) : Continuous (mixedRadialTheta K I t) := by
  change Continuous ((fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2) ∘
    (fun u : Angular K ↦ (t, u)))
  exact (continuousOn_mixedRadialTheta K I).comp_continuous
    (show Continuous (fun u : Angular K ↦ (t, u)) from
      continuous_const.prodMk continuous_id) (fun _ ↦ ⟨ht, Set.mem_univ _⟩)

theorem integrableOn_mixedRadialTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u ↦ mixedRadialTheta K I t u) (angularCube K) := by
  exact ((continuous_slice K I t ht).continuousOn.integrableOn_compact
    (compact_angularBox K)).mono_set (cube_subset_box K)

theorem integrableOn_mixedRadialTheta_neg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u ↦ mixedRadialTheta K I t (-u)) (angularCube K) := by
  exact (((continuous_slice K I t ht).comp continuous_neg).continuousOn.integrableOn_compact
    (compact_angularBox K)).mono_set (cube_subset_box K)

theorem integral_one_angularCube :
    (∫ _u in angularCube K, (1 : ℂ)) = 1 := by
  simp [setIntegral_const, volume_cube K, Measure.real]

theorem mixedAngularAverage_sub_one
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage K I t - 1 =
      ∫ u in angularCube K, (mixedRadialTheta K I t u - 1) := by
  rw [integral_sub (integrableOn_mixedRadialTheta K I t ht)
    (integrableOn_const (by simp [volume_cube K])), integral_one_angularCube]
  rfl

theorem mixedNegAngularAverage_sub_one
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) (ht : 0 < t) :
    mixedNegAngularAverage K I t - 1 =
      ∫ u in angularCube K, (mixedRadialTheta K I t (-u) - 1) := by
  rw [integral_sub (integrableOn_mixedRadialTheta_neg K I t ht)
    (integrableOn_const (by simp [volume_cube K])), integral_one_angularCube]
  rfl

private theorem continuousOn_average
    (f : ℝ × Angular K → ℂ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun t ↦ ∫ u in angularCube K, f (t, u)) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  have hslice : ∀ x : ℝ, 0 < x → Continuous (fun u : Angular K ↦ f (x, u)) := by
    intro x hx
    change Continuous (f ∘ (fun u : Angular K ↦ (x, u)))
    exact hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hx, Set.mem_univ _⟩)
  have hcp := (isCompact_Icc : IsCompact (Set.Icc (t / 2) (t + 1))).prod
    (compact_angularBox K)
  have hsub : Set.Icc (t / 2) (t + 1) ×ˢ angularBox K ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by linarith) hp.1.1, Set.mem_univ _⟩
  obtain ⟨M, hM⟩ := hcp.bddAbove_image (hf.mono hsub).norm
  have hnb : Set.Ioo (t / 2) (t + 1) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc : ContinuousAt (fun x ↦ ∫ u in angularCube K, f (x, u)) t := by
    apply continuousAt_of_dominated (bound := fun _ ↦ M)
    · filter_upwards [hnb] with x hx
      exact (hslice x (by have := hx.1; linarith)).aestronglyMeasurable
    · filter_upwards [hnb] with x hx
      filter_upwards [ae_restrict_mem (measurable_cube K)] with u hu
      exact hM (Set.mem_image_of_mem _ ⟨⟨hx.1.le, hx.2.le⟩, cube_subset_box K hu⟩)
    · exact integrableOn_const (by simp [volume_cube K])
    · filter_upwards with u
      have hrad : ContinuousOn (fun x ↦ f (x, u)) (Set.Ioi (0 : ℝ)) := by
        change ContinuousOn (f ∘ (fun x : ℝ ↦ (x, u))) _
        exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun x hx ↦ ⟨hx, Set.mem_univ _⟩)
      exact hrad.continuousAt (isOpen_Ioi.mem_nhds ht)
  exact hc.continuousWithinAt

theorem locallyIntegrableOn_mixedAngularAverage
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LocallyIntegrableOn (mixedAngularAverage K I) (Set.Ioi (0 : ℝ)) := by
  exact (continuousOn_average K _ (continuousOn_mixedRadialTheta K I)).locallyIntegrableOn
    measurableSet_Ioi

theorem locallyIntegrableOn_mixedNegAngularAverage
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LocallyIntegrableOn (mixedNegAngularAverage K I) (Set.Ioi (0 : ℝ)) := by
  have hf : ContinuousOn (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 (-p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    change ContinuousOn ((fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2) ∘
      (fun p : ℝ × Angular K ↦ (p.1, -p.2))) _
    exact (continuousOn_mixedRadialTheta K I).comp
      (continuous_fst.prodMk continuous_snd.neg).continuousOn (fun p hp ↦ ⟨hp.1, trivial⟩)
  exact (continuousOn_average K _ hf).locallyIntegrableOn measurableSet_Ioi

private theorem exp_rpow_isBigO (b p r : ℝ) (hb : 0 < b) (hp : 0 < p) :
    Asymptotics.IsBigO Filter.atTop (fun t : ℝ ↦ Real.exp (-b * t ^ p))
      (fun t : ℝ ↦ t ^ r) := by
  have h := ((isLittleO_exp_neg_mul_rpow_atTop hb (r / p)).comp_tendsto
    (tendsto_rpow_atTop hp)).isBigO
  apply h.congr' (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  change (t ^ p) ^ (r / p) = t ^ r
  rw [← Real.rpow_mul ht, mul_div_cancel₀ r hp.ne']

private theorem integral_centered_isBigO
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (q : Angular K → Angular K)
    (hq : Continuous q) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ ∫ u in angularCube K, (mixedRadialTheta K I t (q u) - 1))
      (fun t : ℝ ↦ t ^ r) := by
  obtain ⟨B, b, hB, hb, htail⟩ := mixedRadialTheta_uniform_exponential_tail K I
    (q '' angularBox K) ((compact_angularBox K).image hq)
  have hbound : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ ∫ u in angularCube K, (mixedRadialTheta K I t (q u) - 1))
      (fun t : ℝ ↦ Real.exp (-b * t ^ (2 / (Module.finrank ℚ K : ℝ)))) := by
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp [volume_cube K])
      (fun u hu ↦ htail t ht (q u) (Set.mem_image_of_mem q (cube_subset_box K hu)))
    simpa [Measure.real, volume_cube K, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h
  exact hbound.trans (exp_rpow_isBigO b _ r hb
    (div_pos (by norm_num) (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))))

theorem mixedAngularAverage_isBigO_rpow
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ mixedAngularAverage K I t - 1)
      (fun t : ℝ ↦ t ^ r) := by
  apply (integral_centered_isBigO K I id continuous_id r).congr'
    _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (mixedAngularAverage_sub_one K I t ht).symm

theorem mixedNegAngularAverage_isBigO_rpow
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ ↦ mixedNegAngularAverage K I t - 1)
      (fun t : ℝ ↦ t ^ r) := by
  apply (integral_centered_isBigO K I (fun u ↦ -u) continuous_neg r).congr'
    _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (mixedNegAngularAverage_sub_one K I t ht).symm

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
