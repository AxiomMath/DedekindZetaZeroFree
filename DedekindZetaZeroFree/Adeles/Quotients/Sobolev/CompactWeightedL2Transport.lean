module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CompactMetricBounds

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory TopologicalSpace Filter
open scoped ContDiff ENNReal Topology

private lemma transport_restrict_density {n : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) :
    (KPChartL2.weightedMeasure n (Ω : Set (E n)) w).restrict C =
      (volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x)) := by
  rw [KPChartL2.weightedMeasure, restrict_withDensity hC.measurableSet,
    Measure.restrict_restrict_of_subset hCΩ]

private lemma transport_support_norm {n r : ℕ} (C : Set (E n))
    (hC : MeasurableSet C) (μ : Measure (E n)) (f : E n → V r)
    (hsupp : ∀ᵐ x ∂μ, x ∉ C → f x = 0) :
    eLpNorm f 2 (μ.restrict C) = eLpNorm f 2 μ := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hC.nullMeasurableSet]
  apply eLpNorm_congr_ae
  filter_upwards [hsupp] with x hx
  by_cases h : x ∈ C
  · simp [h]
  · simp [h, hx h]

private lemma transport_support_memLp {n r : ℕ} (C : Set (E n))
    (hC : MeasurableSet C) (μ : Measure (E n)) (f : E n → V r)
    (hsupp : ∀ᵐ x ∂μ, x ∉ C → f x = 0) (hf : MemLp f 2 (μ.restrict C)) :
    MemLp f 2 μ := by
  have heq : C.indicator f =ᵐ[μ] f := by
    filter_upwards [hsupp] with x hx
    by_cases h : x ∈ C
    · simp [h]
    · simp [h, hx h]
  exact ((memLp_indicator_iff_restrict hC.nullMeasurableSet).mpr hf).ae_eq heq

private lemma transport_weighted_support {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (w : E n → ℝ) (f : E n → V r)
    (hsupp : ∀ᵐ x ∂volume, x ∉ C → f x = 0) :
    ∀ᵐ x ∂KPChartL2.weightedMeasure n (Ω : Set (E n)) w, x ∉ C → f x = 0 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_of_ae hsupp)

private lemma transport_sqrt_factor (b : ℝ) (hb : 0 ≤ b) :
    (ENNReal.ofReal b) ^ ((2 : ENNReal).toReal⁻¹) = ENNReal.ofReal (Real.sqrt b) := by
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg hb (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.sqrt_eq_rpow]

private lemma transport_norm_bridge {n r : ℕ} (μ : Measure (E n))
    (f : E n → V r) (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (l2Norm μ f hf) := by
  have hint : Integrable (fun x => ‖f x‖ ^ (2 : ℕ)) μ :=
    hf.integrable_norm_pow (by norm_num)
  have hnn : 0 ≤ᵐ[μ] fun x => ‖f x‖ ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun x => by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  have heq : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [l2Norm, Real.sqrt_eq_rpow]

private lemma transport_real_bound {n r : ℕ} (μ ν : Measure (E n))
    (f : E n → V r) (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν)
    (b : ℝ) (hb : 0 ≤ b)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal b * eLpNorm f 2 ν) :
    l2Norm μ f hμ ≤ b * l2Norm ν f hν := by
  rw [transport_norm_bridge μ f hμ, transport_norm_bridge ν f hν,
    ← ENNReal.ofReal_mul hb] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by unfold l2Norm; positivity)).mp h

theorem compact_weighted_l2_upper {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (Cw : ℝ) (hCw : 0 < Cw)
    (hbound : ∀ x ∈ C, w x ≤ Cw)
    (f : E n → V r) (hsupp : ∀ᵐ x ∂volume, x ∉ C → f x = 0)
    (hf : MemLp f 2 volume) :
    ∃ hfW : MemLp f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w),
      eLpNorm f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) ≤
        ENNReal.ofReal (Real.sqrt Cw) * eLpNorm f 2 volume ∧
      l2Norm (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) f hfW ≤
        Real.sqrt Cw * l2Norm volume f hf := by
  let μ := KPChartL2.weightedMeasure n (Ω : Set (E n)) w
  have hmeasure : μ.restrict C ≤ ENNReal.ofReal Cw • volume.restrict C := by
    rw [transport_restrict_density Ω C hC hCΩ w, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (hbound x hx)
  have hsW := transport_weighted_support Ω C w f hsupp
  have hfW := transport_support_memLp C hC.measurableSet μ f hsW
    ((hf.restrict C).of_measure_le_smul ENNReal.ofReal_ne_top hmeasure)
  have hnorm : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt Cw) * eLpNorm f 2 volume := by
    rw [← transport_support_norm C hC.measurableSet μ f hsW,
      ← transport_support_norm C hC.measurableSet volume f hsupp]
    simpa only [one_div, ENNReal.toReal_inv, smul_eq_mul,
      transport_sqrt_factor Cw hCw.le] using
      (eLpNorm_le_of_measure_le_smul (p := 2) (f := f) hmeasure)
  exact ⟨hfW, hnorm, transport_real_bound μ volume f hfW hf _
    (Real.sqrt_nonneg _) hnorm⟩

theorem compact_weighted_l2_lower {n r : ℕ} (Ω : Opens (E n))
    (C : Set (E n)) (hC : IsCompact C) (hCΩ : C ⊆ (Ω : Set (E n)))
    (w : E n → ℝ) (hw : ContDiffOn ℝ ∞ w (Ω : Set (E n)))
    (cw : ℝ) (hcw : 0 < cw) (hbound : ∀ x ∈ C, cw ≤ w x)
    (f : E n → V r) (hsupp : ∀ᵐ x ∂volume, x ∉ C → f x = 0)
    (hfW : MemLp f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w)) :
    ∃ hf : MemLp f 2 volume,
      eLpNorm f 2 volume ≤ ENNReal.ofReal ((Real.sqrt cw)⁻¹) *
        eLpNorm f 2 (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) ∧
      l2Norm volume f hf ≤ (Real.sqrt cw)⁻¹ *
        l2Norm (KPChartL2.weightedMeasure n (Ω : Set (E n)) w) f hfW := by
  let μ := KPChartL2.weightedMeasure n (Ω : Set (E n)) w
  have hd : AEMeasurable (fun x => ENNReal.ofReal (w x)) (volume.restrict C) :=
    ((hw.continuousOn.mono hCΩ).aemeasurable hC.measurableSet).ennreal_ofReal
  have hn : ∀ᵐ x ∂volume.restrict C, ENNReal.ofReal (w x) ≠ 0 := by
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hcw.trans_le (hbound x hx)))
  have hi := withDensity_inv_same₀ hd hn
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have hmeasure : volume.restrict C ≤ (ENNReal.ofReal cw)⁻¹ • μ.restrict C := by
    rw [transport_restrict_density Ω C hC hCΩ w]
    calc
      volume.restrict C = ((volume.restrict C).withDensity
          (fun x => ENNReal.ofReal (w x))).withDensity
          (fun x => (ENNReal.ofReal (w x))⁻¹) := hi.symm
      _ ≤ ((volume.restrict C).withDensity (fun x => ENNReal.ofReal (w x))).withDensity
          (fun _ => (ENNReal.ofReal cw)⁻¹) := by
        apply withDensity_mono
        apply (withDensity_absolutelyContinuous _ _).ae_le
        filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
        exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (hbound x hx))
      _ = _ := withDensity_const _
  have hf := transport_support_memLp C hC.measurableSet volume f hsupp
    ((hfW.restrict C).of_measure_le_smul
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hcw))) hmeasure)
  have hsW := transport_weighted_support Ω C w f hsupp
  have hfactor : ((ENNReal.ofReal cw)⁻¹) ^ ((2 : ENNReal).toReal⁻¹) =
      ENNReal.ofReal ((Real.sqrt cw)⁻¹) := by
    rw [ENNReal.inv_rpow, transport_sqrt_factor cw hcw.le,
      ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hcw)]
  have hnorm : eLpNorm f 2 volume ≤ ENNReal.ofReal ((Real.sqrt cw)⁻¹) * eLpNorm f 2 μ := by
    rw [← transport_support_norm C hC.measurableSet volume f hsupp,
      ← transport_support_norm C hC.measurableSet μ f hsW]
    simpa only [one_div, ENNReal.toReal_inv, smul_eq_mul, hfactor] using
      (eLpNorm_le_of_measure_le_smul (p := 2) (f := f) hmeasure)
  exact ⟨hf, hnorm, transport_real_bound volume μ f hf hfW _ (by positivity) hnorm⟩

end DedekindZetaZeroFree.KPCompactInteriorH1

end
