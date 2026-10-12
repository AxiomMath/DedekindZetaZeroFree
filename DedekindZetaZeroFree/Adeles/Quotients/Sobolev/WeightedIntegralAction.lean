module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CompactMetricBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPCompactInteriorH1
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

private lemma weight_integral {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (g : E n → ℝ) :
    (∫ x, g x ∂KPChartL2.weightedMeasure n D.chart D.weight) =
      ∫ x in D.chart, D.weight x * g x := by
  rw [KPChartL2.weightedMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (D.smooth_weight.continuousOn.aemeasurable D.open_chart.measurableSet).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem D.open_chart.measurableSet] with x hx
  simp [ENNReal.toReal_ofReal (D.positive_weight x hx).le, smul_eq_mul]

private lemma weight_integrable {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (g : E n → ℝ)
    (hg : Integrable (fun x => D.weight x * g x) (volume.restrict D.chart)) :
    Integrable g (KPChartL2.weightedMeasure n D.chart D.weight) := by
  rw [KPChartL2.weightedMeasure, integrable_withDensity_iff_integrable_smul₀'
    (D.smooth_weight.continuousOn.aemeasurable D.open_chart.measurableSet).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hg.congr
  filter_upwards [ae_restrict_mem D.open_chart.measurableSet] with x hx
  simp [ENNReal.toReal_ofReal (D.positive_weight x hx).le, smul_eq_mul]

theorem integral_action_le_compact_weight {n r : ℕ} {Γ : Type*} [Group Γ]
    (D : KPChartL2.Data n r Γ) (C : Set (E n)) (hC : IsCompact C)
    (hCchart : C ⊆ D.chart) :
    ∃ L : ℝ, 0 < L ∧ ∀ (γ : Γ) (f : E n → ℝ), Continuous f →
      (∀ x, 0 ≤ f x) → Function.support f ⊆ C →
      (∫ x in C, f (D.act γ x)) ≤ L * (∫ x, f x) := by
  have hwC := D.smooth_weight.continuousOn.mono hCchart
  obtain ⟨cw, hcw, hlow⟩ := hC.exists_forall_le' hwC
    (fun x hx => D.positive_weight x (hCchart hx))
  obtain ⟨b, hb⟩ := hC.bddAbove_image hwC
  let Cw := max b 1
  have hCw : 0 < Cw := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hupp : ∀ x ∈ C, D.weight x ≤ Cw := fun x hx =>
    (hb (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨Cw / cw, div_pos hCw hcw, ?_⟩
  intro γ f hf hnn hsupp
  have hzero : ∀ x ∉ C, f x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hsupp hn)
  have hfC : Integrable f (volume.restrict C) := hf.continuousOn.integrableOn_compact hC
  have hwfC : Integrable (fun x => D.weight x * f x) (volume.restrict C) :=
    (hwC.mul hf.continuousOn).integrableOn_compact hC
  have hwf : Integrable (fun x => D.weight x * f x) (volume.restrict D.chart) := by
    have hi := (integrable_indicator_iff hC.measurableSet).mpr hwfC
    have heq : C.indicator (fun x => D.weight x * f x) =
        (fun x => D.weight x * f x) := by
      ext x
      by_cases hx : x ∈ C
      · simp [hx]
      · simp [hx, hzero x hx]
    rw [heq] at hi
    exact hi.restrict
  have hfw := weight_integrable D f hwf
  have hcompw := (D.invariant_measure γ).integrable_comp_of_integrable hfw
  have hcompC : Integrable (fun x => f (D.act γ x)) (volume.restrict C) :=
    ((hf.comp_continuousOn ((D.smooth_action γ).continuousOn.mono hCchart))).integrableOn_compact hC
  have hwcompC : Integrable (fun x => D.weight x * f (D.act γ x)) (volume.restrict C) :=
    (hwC.mul (hf.comp_continuousOn ((D.smooth_action γ).continuousOn.mono hCchart))).integrableOn_compact hC
  have hlowint : cw * (∫ x in C, f (D.act γ x)) ≤
      ∫ x in C, D.weight x * f (D.act γ x) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hcompC.const_mul cw) hwcompC
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact mul_le_mul_of_nonneg_right (hlow x hx) (hnn _)
  have hmiddle : (∫ x in C, D.weight x * f (D.act γ x)) ≤
      ∫ x, f x ∂KPChartL2.weightedMeasure n D.chart D.weight := by
    have heq : (KPChartL2.weightedMeasure n D.chart D.weight).restrict C =
        (volume.restrict C).withDensity (fun x => ENNReal.ofReal (D.weight x)) := by
      rw [KPChartL2.weightedMeasure, restrict_withDensity hC.measurableSet,
        Measure.restrict_restrict_of_subset hCchart]
    have hwint : (∫ x, f (D.act γ x) ∂(KPChartL2.weightedMeasure n D.chart D.weight).restrict C) =
        ∫ x in C, D.weight x * f (D.act γ x) := by
      rw [heq, integral_withDensity_eq_integral_toReal_smul₀
        (hwC.aemeasurable hC.measurableSet).ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
        simp [ENNReal.toReal_ofReal (D.positive_weight x (hCchart hx)).le, smul_eq_mul]
    rw [← hwint]
    calc
      _ ≤ ∫ x, f (D.act γ x) ∂KPChartL2.weightedMeasure n D.chart D.weight :=
        integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun x => hnn _) hcompw
      _ = _ := by
        have hm := integral_map (D.invariant_measure γ).measurable.aemeasurable
          (show AEStronglyMeasurable f (Measure.map (D.act γ)
            (KPChartL2.weightedMeasure n D.chart D.weight)) by
            rw [(D.invariant_measure γ).map_eq]; exact hfw.aestronglyMeasurable)
        simpa only [(D.invariant_measure γ).map_eq] using hm.symm
  have huppint : (∫ x, f x ∂KPChartL2.weightedMeasure n D.chart D.weight) ≤
      Cw * (∫ x, f x) := by
    rw [weight_integral D f]
    have heq : (∫ x in D.chart, D.weight x * f x) = ∫ x in C, D.weight x * f x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzero x (fun h => hx (hCchart h)), mul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx, mul_zero])]
    rw [heq, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_const_mul]
    apply integral_mono_ae hwfC (hfC.const_mul Cw)
    filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
    exact mul_le_mul_of_nonneg_right (hupp x hx) (hnn x)
  have hh := hlowint.trans (hmiddle.trans huppint)
  have hfinal := (le_div_iff₀ hcw).mpr (show
    (∫ x in C, f (D.act γ x)) * cw ≤ Cw * (∫ x, f x) by
    simpa only [mul_comm] using hh)
  simpa only [div_mul_eq_mul_div] using hfinal

end DedekindZetaZeroFree.KPCompactInteriorH1

end
