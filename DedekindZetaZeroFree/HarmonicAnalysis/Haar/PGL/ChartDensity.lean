module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLComplex.AffineLieDensity

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Manifold ContDiff

namespace DedekindZetaZeroFree.PGLExponential
open PGLComplex

theorem coordinate_change_density
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (e : OpenPartialHomeomorph V V)
    (he : DifferentiableOn ℝ e e.source) (w : V → ENNReal) :
    Measure.map e.symm ((ν.withDensity w).restrict e.target) =
      (ν.withDensity (fun x => ENNReal.ofReal |(fderiv ℝ e x).det| * w (e x))).restrict e.source := by
  have hm : AEMeasurable e.symm ((ν.withDensity w).restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hm hs]
  have hd : ∀ x ∈ e.source, HasFDerivAt e (fderiv ℝ e x) x := fun x hx =>
    ((he x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt
  have himage : e.symm ⁻¹' s ∩ e.target = e '' (s ∩ e.source) := by
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      exact ⟨e.symm y, ⟨hy, e.map_target hyt⟩, e.right_inv hyt⟩
    · rintro ⟨x, ⟨hxs, hxe⟩, rfl⟩
      exact ⟨by simpa only [Set.mem_preimage, e.left_inv hxe] using hxs, e.map_source hxe⟩
  have hpre : MeasurableSet (e.symm ⁻¹' s ∩ e.target) := by
    rw [himage]
    exact measurable_image_of_fderivWithin (hs.inter e.open_source.measurableSet)
      (fun x hx => (hd x hx.2).hasFDerivWithinAt)
      (e.injOn.mono Set.inter_subset_right)
  rw [Measure.restrict_apply₀ (hm.nullMeasurableSet_preimage hs),
    withDensity_apply w hpre, Measure.restrict_apply hs,
    withDensity_apply _ (hs.inter e.open_source.measurableSet), himage]
  apply lintegral_image_eq_lintegral_abs_det_fderiv_mul ν
      (hs.inter e.open_source.measurableSet)
      (fun x hx => ((he x hx.2).differentiableAt (e.open_source.mem_nhds hx.2)).hasFDerivAt.hasFDerivWithinAt)
      (e.injOn.mono Set.inter_subset_right)

theorem translated_chart_haar_density (μ : Measure Group) [μ.IsHaarMeasure]
    (g : Group) (c : ℝ)
    (haffine : Measure.map affineChart.symm (μ.restrict affineTarget) =
      (volume.withDensity (fun x : Coordinates =>
        ENNReal.ofReal (c / ‖delta x‖ ^ 4))).restrict affineSource) :
    Measure.map (affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm
        (μ.restrict (affineChart.trans
          (Homeomorph.mulLeft g).toOpenPartialHomeomorph).target) =
      (volume.withDensity (fun x : Coordinates =>
        ENNReal.ofReal (c / ‖delta x‖ ^ 4))).restrict affineSource := by
  rw [← haffine]
  set Tg := affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph with hTg
  set φ : Group → Group := fun h => g⁻¹ * h with hφ
  have hAT : MeasurableSet affineTarget := by
    rw [← affineChart_target]; exact affineChart.open_target.measurableSet
  have hmeas : Measurable φ := by rw [hφ]; fun_prop
  have hsource : Tg.target = φ ⁻¹' affineTarget := by
    have h1 := translatedAffineChart_source g
    rw [translatedAffineChart] at h1
    rw [OpenPartialHomeomorph.symm_source] at h1
    rw [hTg, hφ]
    exact h1
  have hB : Measure.map φ (μ.restrict (φ ⁻¹' affineTarget)) = μ.restrict affineTarget := by
    rw [← Measure.restrict_map hmeas hAT]
    rw [hφ, map_mul_left_eq_self μ g⁻¹]
  have hae : Tg.symm =ᵐ[μ.restrict (φ ⁻¹' affineTarget)] (affineChart.symm ∘ φ) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (hAT.preimage hmeas)]
    filter_upwards with h hh
    rw [Function.comp_apply]
    change translatedAffineChart g h = affineChart.symm (g⁻¹ * h)
    rw [translatedAffineChart_apply g h hh, affineChart_symm_apply _ hh]
  rw [hsource, Measure.map_congr hae, ← AEMeasurable.map_map_of_aemeasurable]
  · rw [hB]
  · rw [hB, ← affineChart_target]
    exact affineChart.continuousOn_symm.aemeasurable affineChart.open_target.measurableSet
  · exact hmeas.aemeasurable

theorem coordinate_pullback_trans {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] [BorelSpace Z]
    (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z) (μ : Measure Z) :
    Measure.map (e.trans f).symm (μ.restrict (e.trans f).target) =
      Measure.map e.symm ((Measure.map f.symm (μ.restrict f.target)).restrict e.target) := by
  have hf : AEMeasurable f.symm (μ.restrict f.target) :=
    f.continuousOn_symm.aemeasurable f.open_target.measurableSet
  rw [Measure.restrict_map_of_aemeasurable hf e.open_target.measurableSet,
    Measure.restrict_restrict₀ (hf.nullMeasurableSet_preimage e.open_target.measurableSet)]
  have ht : f.symm ⁻¹' e.target ∩ f.target = (e.trans f).target := by
    rw [OpenPartialHomeomorph.trans_target]
    exact Set.inter_comm _ _
  rw [ht]
  have hf' : AEMeasurable f.symm (μ.restrict (e.trans f).target) :=
    hf.mono_measure (Measure.restrict_mono (by rw [OpenPartialHomeomorph.trans_target]; exact Set.inter_subset_left) le_rfl)
  have he : AEMeasurable e.symm (Measure.map f.symm (μ.restrict (e.trans f).target)) := by
    rw [← ht, ← Measure.restrict_restrict₀ (hf.nullMeasurableSet_preimage e.open_target.measurableSet),
      ← Measure.restrict_map_of_aemeasurable hf e.open_target.measurableSet]
    exact e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  rw [AEMeasurable.map_map_of_aemeasurable he hf']
  rfl
theorem coordinate_pullback_restrict {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure Y)
    (s : Set X) (hs : MeasurableSet s) (hss : s ⊆ e.source) :
    (Measure.map e.symm (μ.restrict e.target)).restrict s =
      Measure.map e.symm (μ.restrict (e '' s)) := by
  have he : AEMeasurable e.symm (μ.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  rw [Measure.restrict_map_of_aemeasurable he hs,
    Measure.restrict_restrict₀ (he.nullMeasurableSet_preimage hs)]
  congr 1
  exact congrArg μ.restrict (by rw [Set.inter_comm, ← e.image_eq_target_inter_inv_preimage hss])

theorem coordinate_pullback_support {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure Y) :
    (Measure.map e.symm (μ.restrict e.target)).restrict e.source =
      Measure.map e.symm (μ.restrict e.target) := by
  rw [coordinate_pullback_restrict e μ e.source e.open_source.measurableSet Set.Subset.rfl,
    e.image_source_eq_target]

theorem coordinate_pullback_inverse {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) (μ : Measure Y) :
    Measure.map e (Measure.map e.symm (μ.restrict e.target)) = μ.restrict e.target := by
  have he : AEMeasurable e.symm (μ.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have hf : AEMeasurable e (Measure.map e.symm (μ.restrict e.target)) := by
    rw [← coordinate_pullback_support e μ]
    exact e.continuousOn.aemeasurable e.open_source.measurableSet
  rw [AEMeasurable.map_map_of_aemeasurable hf he]
  have hh : (e ∘ e.symm) =ᵐ[μ.restrict e.target] id := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact e.right_inv hy
  rw [Measure.map_congr hh, Measure.map_id]

theorem coordinate_overlap_pullback {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] [BorelSpace Z]
    (E : OpenPartialHomeomorph X Z) (P : OpenPartialHomeomorph Y Z) (μ : Measure Z) :
    Measure.map (E.trans P.symm).symm
        ((Measure.map P.symm (μ.restrict P.target)).restrict (E.trans P.symm).target) =
      (Measure.map E.symm (μ.restrict E.target)).restrict (E.trans P.symm).source := by
  rw [coordinate_pullback_trans]
  change Measure.map E.symm ((Measure.map P ((Measure.map P.symm (μ.restrict P.target)).restrict P.source)).restrict E.target) = _
  rw [coordinate_pullback_support, coordinate_pullback_inverse,
    Measure.restrict_restrict E.open_target.measurableSet]
  rw [coordinate_pullback_restrict E μ _ (E.trans P.symm).open_source.measurableSet
    (by rw [OpenPartialHomeomorph.trans_source]; exact Set.inter_subset_left)]
  congr 1
  congr 1
  rw [OpenPartialHomeomorph.trans_source]
  ext z
  constructor
  · rintro ⟨hzE, hzP⟩
    exact ⟨E.symm z, ⟨E.map_target hzE, by simpa only [Set.mem_preimage, E.right_inv hzE, OpenPartialHomeomorph.symm_source] using hzP⟩, E.right_inv hzE⟩
  · rintro ⟨x, ⟨hxE, hxP⟩, rfl⟩
    exact ⟨E.map_source hxE, hxP⟩

end DedekindZetaZeroFree.PGLExponential

end
