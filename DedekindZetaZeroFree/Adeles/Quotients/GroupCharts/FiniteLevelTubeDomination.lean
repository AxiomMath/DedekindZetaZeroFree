module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RationalQuotients.CompactMultiplicity
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.GroupCharts.CompatibleProductDensity

@[expose] public section

noncomputable section
open MeasureTheory Topology
open scoped Classical NumberField ENNReal Manifold ContDiff
namespace DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2
open KPContActualSphericalRightFieldIdentification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem actual_original_chart_tube_domination
    (chart : GroupChart F ζ hζ U R P H)
    (A : Set (KPContLocalNorm.Space (groupDimension F)))
    (hA : IsCompact A) (hAT : A ⊆ chart.T.carrier) :
    ∃ (μArch : Measure (KPSmoothLocalQuotientCharts.ArchGroup F))
      (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) (C : ℝ),
      μArch.IsHaarMeasure ∧ ν.IsHaarMeasure ∧
      Measure.map (fun p : KPSmoothLocalQuotientCharts.ArchGroup F ×
          KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2)
          (μArch.prod ν) = R.adelicHaar ∧
      0 < ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) ∧
      ν (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) < ⊤ ∧
      0 < C ∧
      Measure.map (fun p => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (chart.groupLift p.1 * p.2))
        ((volume.restrict A).prod
          (ν.restrict (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)))) ≤
        ENNReal.ofReal C • R.quotientHaar := by
  obtain ⟨μArch, ν, ρ, c, hμArch, hν, hprod, hmass, hmassT, hρ, hpos, hc, hb, hi⟩ :=
    exists_compatible_original_chart_density chart A hA hAT
  letI := actualLieChartedSpace F
  letI := actualLieGroup F
  letI : IsTopologicalGroup (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI : T2Space (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := ⟨rfl⟩
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ArchGroup F) := ⟨rfl⟩
  letI : BorelSpace (KPSmoothLocalQuotientCharts.X F ζ hζ) := ⟨rfl⟩
  letI := hμArch
  letI := hν
  letI := R.adelic_isHaar
  obtain ⟨e, he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  letI : SecondCountableTopology (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : SecondCountableTopology (KPSmoothLocalQuotientCharts.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPSmoothLocalQuotientCharts.ArchGroup F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothLocalQuotientCharts.ArchGroup F)).secondCountableTopology
  letI : BorelSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ArchGroup F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := KPFiniteCuspAtlas.FiniteCover F ζ hζ)).locallyCompactSpace
  letI : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isOpenQuotientMap_snd (X := KPSmoothLocalQuotientCharts.ArchGroup F)).locallyCompactSpace
  haveI : SigmaFinite μArch := inferInstance
  haveI : SigmaFinite ν := inferInstance
  let a : KPContLocalNorm.Space (groupDimension F) → KPSmoothLocalQuotientCharts.ArchGroup F :=
    fun x => chart.groupCenter * (actualLieData F).exponential (groupCoordinates F x)
  have hac : Continuous a :=
    (contMDiff_const.mul (actualLieData F).exponential_smooth).continuous.comp
      (groupCoordinates F).continuous
  have haeq : ∀ x ∈ chart.T.carrier, a x = (fun x => chart.exponential.chart (groupCoordinates F x)) x := by
    intro x hx
    change a x = chart.exponential.chart (groupCoordinates F x)
    rw [chart.exponential.exponential_formula _
      (chart.closure_source ⟨x, subset_closure hx, rfl⟩)]
    exact congrArg (chart.groupCenter * ·) (congrFun (actualLieData_exponential F) _)
  let W := a '' A
  let K : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ) := U.toOpenSubgroup
  let k : ℝ≥0∞ := (ENNReal.ofReal c)⁻¹
  have himg : ∀ S, S ⊆ A → a '' S = (fun x => chart.exponential.chart (groupCoordinates F x)) '' S := by
    intro S hS
    apply Set.image_congr
    intro x hx
    exact haeq x (hAT (hS hx))
  have harch : Measure.map a (volume.restrict A) ≤ k • μArch.restrict W := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.map_apply hac.measurable hS, Measure.restrict_apply (hac.measurable hS),
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS]
    have hT : MeasurableSet (a ⁻¹' S ∩ A) := (hac.measurable hS).inter hA.measurableSet
    have hsub : a ⁻¹' S ∩ A ⊆ A := Set.inter_subset_right
    have hd : ENNReal.ofReal c * volume (a ⁻¹' S ∩ A) ≤
        μArch (a '' (a ⁻¹' S ∩ A)) := by
      rw [himg _ hsub]
      change _ ≤ μArch ((fun x => chart.exponential.chart (groupCoordinates F x)) '' _)
      rw [hi _ hT (hsub.trans hAT)]
      calc
        _ = ∫⁻ x in a ⁻¹' S ∩ A, ENNReal.ofReal c := by simp
        _ ≤ _ := by
          apply setLIntegral_mono' hT
          intro x hx
          exact ENNReal.ofReal_le_ofReal (hb x hx.2)
    have him : a '' (a ⁻¹' S ∩ A) ⊆ S ∩ W := by
      rintro y ⟨x, ⟨hxS, hxA⟩, rfl⟩
      exact ⟨hxS, ⟨x, hxA, rfl⟩⟩
    have hh := mul_le_mul_right (hd.trans (measure_mono him)) k
    rwa [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top] at hh
  let ψ := Homeomorph.prodCongr
    (Homeomorph.refl (KPSmoothLocalQuotientCharts.ArchGroup F))
    (Homeomorph.mulLeft chart.finiteRepresentative)
  let φ := ψ.trans e.toHomeomorph
  have hφ : ∀ p, φ p = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 *
      chart.finiteRepresentative * p.2 := by
    intro p
    change e (p.1, chart.finiteRepresentative * p.2) = _
    rw [he]
    simp only [Subgroup.coe_mul, mul_assoc]
  have hmapφ : Measure.map φ (μArch.prod ν) = R.adelicHaar := by
    have hψ : (ψ : _ → _) = Prod.map id (fun v => chart.finiteRepresentative * v) := rfl
    have heprod : Measure.map e (μArch.prod ν) = R.adelicHaar := by
      convert hprod using 1
      congr 1
      funext p
      exact he p.1 p.2
    change Measure.map (e.toHomeomorph ∘ ψ) (μArch.prod ν) = _
    have hmprod : Measure.map (Prod.map id (fun v => chart.finiteRepresentative * v)) (μArch.prod ν) =
        μArch.prod ν := by
      have hv : Measurable (fun v : KPFiniteCuspAtlas.FiniteCover F ζ hζ => chart.finiteRepresentative * v) :=
        (continuous_const.mul continuous_id).measurable
      rw [← Measure.map_prod_map _ _ measurable_id hv, Measure.map_id, map_mul_left_eq_self]
    rw [← Measure.map_map e.continuous.measurable ψ.continuous.measurable, hψ, hmprod]
    exact heprod
  let C := chart.piece A
  have hC : IsCompact C := chart.piece_compact A hA hAT
  have himgC : φ '' (W ×ˢ K) ⊆ C := by
    rintro g ⟨⟨y, v⟩, ⟨⟨x, hx, rfl⟩, hv⟩, rfl⟩
    refine ⟨x, hx, ⟨v, hv⟩, ?_⟩
    rw [hφ, haeq x (hAT hx)]
    rfl
  have hrestrict : Measure.map φ ((μArch.restrict W).prod (ν.restrict K)) ≤
      R.adelicHaar.restrict C := by
    rw [Measure.prod_restrict,
      ← φ.injective.preimage_image (W ×ˢ K), ← φ.measurableEmbedding.restrict_map,
      hmapφ]
    exact Measure.restrict_mono himgC le_rfl
  have hprodle : (Measure.map a (volume.restrict A)).prod (ν.restrict K) ≤
      k • ((μArch.restrict W).prod (ν.restrict K)) := by
    simpa only [Measure.prod_smul_left] using Measure.prod_mono harch (le_rfl : ν.restrict K ≤ ν.restrict K)
  let q := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
  have hq : Measurable q := continuous_quotient_mk'.measurable
  obtain ⟨N, hN⟩ := compact_haar_recipe_pushforward_bound F ζ hζ R C hC
  have hfull : Measure.map (fun p => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (chart.groupLift p.1 * p.2)) ((volume.restrict A).prod (ν.restrict K)) =
      Measure.map (q ∘ φ ∘ Prod.map a id) ((volume.restrict A).prod (ν.restrict K)) := by
    apply Measure.map_congr
    have hae : ∀ᵐ p ∂(volume.restrict A).prod (ν.restrict K), p.1 ∈ A :=
      (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem hA.measurableSet)
    filter_upwards [hae] with p hp
    change q (chart.groupLift p.1 * p.2) = q (φ (a p.1, p.2))
    rw [hφ, haeq p.1 (hAT hp)]
    rfl
  have hbound : Measure.map (fun p => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (chart.groupLift p.1 * p.2)) ((volume.restrict A).prod (ν.restrict K)) ≤
      (k * (N : ℝ≥0∞)) • R.quotientHaar := by
    rw [hfull, ← Measure.map_map hq (φ.continuous.measurable.comp (hac.measurable.prodMap measurable_id)),
      ← Measure.map_map φ.continuous.measurable (hac.measurable.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hac.measurable measurable_id, Measure.map_id]
    calc
      _ ≤ Measure.map q (Measure.map φ (k • ((μArch.restrict W).prod (ν.restrict K)))) :=
        Measure.map_mono (Measure.map_mono hprodle φ.continuous.measurable) hq
      _ = k • Measure.map q (Measure.map φ ((μArch.restrict W).prod (ν.restrict K))) := by
        rw [Measure.map_smul k φ.continuous.measurable.aemeasurable,
          Measure.map_smul k hq.aemeasurable]
      _ ≤ k • ((N : ℝ≥0∞) • R.quotientHaar) := by
        apply smul_le_smul_left
        exact (Measure.map_mono hrestrict hq).trans hN
      _ = _ := by rw [smul_smul]
  refine ⟨μArch, ν, (N : ℝ) / c + 1, hμArch, hν, hprod, hmass, hmassT,
    by positivity, hbound.trans ?_⟩
  apply Measure.le_iff.mpr
  intro S hS
  simp only [Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul_left
  change (ENNReal.ofReal c)⁻¹ * (N : ℝ≥0∞) ≤ ENNReal.ofReal ((N : ℝ) / c + 1)
  rw [mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_div_of_pos hc]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end DedekindZetaZeroFree.KPGroupChartFullTubeHaarL2

end
