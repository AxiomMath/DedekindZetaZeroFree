module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineNormDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology Set

namespace DedekindZetaZeroFree.KPContSectorFixedMeasureLocalFiniteness

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport
open KPContSectorQuotientRelationsComparison

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private lemma measure_saturation_inter_domain_le
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (D : Set G) (hD : IsFundamentalDomain Γ D μ) (C : Set G) :
    μ ((Quotient.mk (QuotientGroup.rightRel Γ)) ⁻¹'
      ((Quotient.mk (QuotientGroup.rightRel Γ)) '' C) ∩ D) ≤ μ C := by
  classical
  rw [hD.measure_eq_tsum C]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro x hx
  obtain ⟨y, hy, he⟩ := hx.1
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
  exact Set.mem_iUnion.mpr ⟨g⁻¹, ⟨⟨y, hy, by
    simpa using (congrArg (fun z => g⁻¹ • z) hg).symm⟩, hx.2⟩⟩

theorem quotientHaar_finiteOnCompacts
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) :
    IsFiniteMeasureOnCompacts R.quotientHaar := by
  letI := R.adelic_isHaar
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (KubotaRankTwo.GL2 F) := Units.val_injective.countable
  letI : Countable (KPRationalAdelicSplitting.RationalPGL2 F) :=
    (Quotient.mk'_surjective (s := QuotientGroup.leftRel
      (KPRationalAdelicSplitting.rationalScalars F))).countable
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    Set.Countable.to_subtype (Set.countable_range
      (KPSmoothLocalQuotientCharts.rationalSplit F ζ hζ))
  have hp : IsOpenQuotientMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    MulAction.isOpenQuotientMap_quotientMk
  have hpm : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := hp.continuous.measurable
  letI : IsLocallyFiniteMeasure R.quotientHaar := ⟨fun x => by
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨V, hVo, hgV, hVc⟩ := exists_isOpen_mem_isCompact_closure g
    have hopen := hp.isOpenMap V hVo
    refine ⟨KPSmoothLocalQuotientCharts.quotientMap F ζ hζ '' V,
      hopen.mem_nhds (Set.mem_image_of_mem _ hgV), ?_⟩
    rw [← R.quotient_normalization, Measure.map_apply hpm hopen.measurableSet,
      Measure.restrict_apply (hpm hopen.measurableSet)]
    exact (measure_saturation_inter_domain_le _ _ _ R.domain_fundamental V).trans_lt
      ((measure_mono subset_closure).trans_lt hVc.measure_lt_top)⟩
  infer_instance

private theorem K_U_compact (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    IsCompact (K_U F ζ hζ U : Set (ActualCover F ζ hζ)) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  obtain ⟨e, he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  let L := (KPContSectorArchSphericalFibers.KInfinity F).prod U.toOpenSubgroup.toSubgroup
  let M := L.map e.toMonoidHom
  have hcompact : IsCompact (M : Set (ActualCover F ζ hζ)) :=
    ((KPContSectorArchSphericalFibers.KInfinity_compact F ζ hζ).prod U.isCompact).image e.continuous
  have hcontain : ((KPSmoothActualFlowData.archimedeanInsertion F ζ hζ) ''
      (KPContSectorArchSphericalFibers.KInfinity F : Set (KPSmoothActualFlowData.GInfinity F)) ∪
      (fun c : FiniteCover F ζ hζ => (c : ActualCover F ζ hζ)) ''
        (U.toOpenSubgroup : Set (FiniteCover F ζ hζ))) ⊆ M := by
    rintro x (⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩)
    · refine ⟨(a, 1), ⟨ha, Subgroup.one_mem _⟩, ?_⟩
      change e (a, 1) = _
      rw [he]; simp
    · refine ⟨(1, c), ⟨Subgroup.one_mem _, hc⟩, ?_⟩
      change e (1, c) = _
      rw [he, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
  have hle : K_U F ζ hζ U ≤ M := (Subgroup.closure_le M).mpr hcontain
  have heq : K_U F ζ hζ U = M := by
    apply le_antisymm hle
    rintro x ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩
    change e (a, c) ∈ K_U F ζ hζ U
    rw [he]
    exact (K_U F ζ hζ U).mul_mem
      (Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩))
      (Subgroup.subset_closure (Or.inr ⟨c, hc, rfl⟩))
  rw [heq]
  exact hcompact

private theorem piTilde_compact_preimage (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (hKU : IsCompact (K_U F ζ hζ U : Set (ActualCover F ζ hζ)))
    (K : Set (CoveredSpherical F ζ hζ U)) (hK : IsCompact K) :
    IsCompact ((piTilde F ζ hζ U) ⁻¹' K) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let p := piTilde F ζ hζ U ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
  have hp : IsOpenMap p := (piTilde_isOpenMap F ζ hζ U).comp
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hps : Function.Surjective p := (piTilde_surjective F ζ hζ U).comp Quotient.mk_surjective
  choose V hVo hgV hVc using fun g : ActualCover F ζ hζ => exists_isOpen_mem_isCompact_closure g
  have hcover : K ⊆ ⋃ g : ActualCover F ζ hζ, p '' V g := by
    intro x hx
    obtain ⟨g, rfl⟩ := hps x
    exact mem_iUnion.mpr ⟨g, mem_image_of_mem p (hgV g)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun g => p '' V g)
    (fun g => hp _ (hVo g)) hcover
  let C := ⋃ g ∈ s, closure (V g)
  have hC : IsCompact C := s.finite_toSet.isCompact_biUnion (fun g hg => hVc g)
  have hsub : K ⊆ p '' C := by
    intro x hx
    obtain ⟨g, hg, y, hy, rfl⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_image_of_mem p (mem_iUnion₂.mpr ⟨g, hg, subset_closure hy⟩)
  apply (hC.mul hKU).image continuous_quot_mk |>.of_isClosed_subset
    (hK.isClosed.preimage (piTilde_continuous F ζ hζ U))
  intro x hx
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨c, hc, he⟩ := hsub hx
  have he' : coveredActualMap F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ c) =
      coveredActualMap F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) :=
    (e F ζ hζ U).injective he
  change DoubleCoset.mk _ _ c = DoubleCoset.mk _ _ g at he'
  obtain ⟨a, ha, b, hb, hg⟩ := DoubleCoset.rel_iff.mp (Quotient.exact he')
  refine ⟨c * b, ⟨c, hc, b, hb, rfl⟩, ?_⟩
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [hg, mul_assoc] using ha

theorem coveredMeasure_finiteOnCompacts
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    IsFiniteMeasureOnCompacts (coveredMeasure F ζ hζ R U) := by
  letI := quotientHaar_finiteOnCompacts F ζ hζ R
  refine ⟨fun K hK => ?_⟩
  rw [coveredMeasure, Measure.map_apply (piTilde_continuous F ζ hζ U).measurable
    hK.measurableSet]
  exact (piTilde_compact_preimage F ζ hζ U (K_U_compact F ζ hζ U) K hK).measure_lt_top

theorem sphericalMeasure_finiteOnCompacts
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    IsFiniteMeasureOnCompacts
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
  letI := coveredMeasure_finiteOnCompacts F ζ hζ R U
  rw [← map_q_coveredMeasure F ζ hζ R P U]
  refine ⟨fun K hK => ?_⟩
  rw [Measure.map_apply
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
    hK.measurableSet]
  exact (KPContSectorSmoothFramesSupport.q_closed_and_proper F ζ hζ U).2 K hK |>.measure_lt_top

theorem coveredMeasure_regular
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    (coveredMeasure F ζ hζ R U).Regular := by
  letI := coveredMeasure_finiteOnCompacts F ζ hζ R U
  letI := KPContSectorQuotientRelationsComparison.instPolishSpaceCoveredSpherical F ζ hζ U
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (CoveredSpherical F ζ hζ U)
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem sphericalMeasure_regular
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).Regular := by
  letI := sphericalMeasure_finiteOnCompacts F ζ hζ R P U
  letI := KPContSectorQuotientRelationsComparison.instPolishSpaceRawXU F ζ hζ U
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable
    (KPMsFixedHaarDisintegration.Spherical F ζ hζ U)
  exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem coveredMeasure_sigmaFinite
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    SigmaFinite (coveredMeasure F ζ hζ R U) := by
  letI := coveredMeasure_finiteOnCompacts F ζ hζ R U
  letI := KPContSectorQuotientRelationsComparison.instPolishSpaceCoveredSpherical F ζ hζ U
  infer_instance

theorem sphericalMeasure_sigmaFinite
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    SigmaFinite (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
  letI := sphericalMeasure_finiteOnCompacts F ζ hζ R P U
  letI := KPContSectorQuotientRelationsComparison.instPolishSpaceRawXU F ζ hζ U
  infer_instance

theorem compactSupport_memLp
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (f : CoveredSpherical F ζ hζ U → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp f 2 (coveredMeasure F ζ hζ R U) := by
  letI := coveredMeasure_finiteOnCompacts F ζ hζ R U
  exact hf.memLp_of_hasCompactSupport hfc

def sectionSquaredNormIntegral
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (f : CoveredSpherical F ζ hζ U → ℂ) : ℝ≥0∞ :=
  ∑ i : Fin (H.atlas U).componentCount,
    (H.disintegration U).componentWeight i *
      ∫⁻ x in ((H.atlas U).cuspAtlas i).fundamentalDomain,
        ENNReal.ofReal (‖f (Quotient.mk (coveredRelation F ζ hζ U)
          (x, (H.atlas U).representative i))‖ ^ 2)
        ∂(KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))

theorem compactSupport_sectionSquaredNormIntegral_lt_top
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (f : CoveredSpherical F ζ hζ U → ℂ)
    (hfg : ∀ (ε : rootsOfUnity 3 F) v,
      f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    sectionSquaredNormIntegral F ζ hζ R P H U f < ⊤ := by
  let g : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U := ⟨f, hfg⟩
  have N := kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H g hf.measurable
  have hLp := compactSupport_memLp F ζ hζ R U f hf hfc
  have hfinite : (∫⁻ v, ENNReal.ofReal (‖f v‖ ^ 2)
      ∂coveredMeasure F ζ hζ R U) < ⊤ := by
    have ht := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hLp.eLpNorm_lt_top
    simpa [ENNReal.ofReal_pow, ofReal_norm, ENNReal.rpow_two] using ht
  have heq : sectionSquaredNormIntegral F ζ hζ R P H U f =
      ∫⁻ b, KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H g b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
    have hc := N.component_integral Set.univ MeasurableSet.univ
    simp only [Set.preimage_univ, Measure.restrict_univ] at hc
    rw [hc]
    unfold sectionSquaredNormIntegral
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hm : Measurable (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :=
      measurable_quotient_mk''
    rw [KPFiniteCuspAtlas.quotientVolume, lintegral_map (N.component_borel i) hm]
    apply lintegral_congr
    intro x
    change ENNReal.ofReal (‖f (Quotient.mk _ (x, _))‖ ^ 2) =
      ENNReal.ofReal (‖(KPContSectorScalarLineAlgebra.S F ζ hζ U R P H g i).val x‖ ^ 2)
    rw [KPContSectorScalarLineAlgebra.S_apply]
  rw [heq]
  have hp := N.restricted_pushforward Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Measure.restrict_univ] at hp
  rw [← hp]
  exact hfinite

structure LevelLocalFiniteness
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) : Prop where
  quotient_finite : IsFiniteMeasureOnCompacts R.quotientHaar
  covered_finite : IsFiniteMeasureOnCompacts (coveredMeasure F ζ hζ R U)
  spherical_finite : IsFiniteMeasureOnCompacts
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)
  covered_regular : (coveredMeasure F ζ hζ R U).Regular
  spherical_regular :
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).Regular
  covered_sigmaFinite : SigmaFinite (coveredMeasure F ζ hζ R U)
  spherical_sigmaFinite :
    SigmaFinite (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U)
  compactSupport_memLp : ∀ f : CoveredSpherical F ζ hζ U → ℂ,
    Continuous f → HasCompactSupport f → MemLp f 2 (coveredMeasure F ζ hζ R U)
  compactSupport_sectionIntegral : ∀ f : CoveredSpherical F ζ hζ U → ℂ,
    (∀ (ε : rootsOfUnity 3 F) v,
      f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v) →
    Continuous f → HasCompactSupport f →
      sectionSquaredNormIntegral F ζ hζ R P H U f < ⊤

theorem levelLocalFiniteness
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    LevelLocalFiniteness F ζ hζ R P H U := by
  exact ⟨quotientHaar_finiteOnCompacts F ζ hζ R,
    coveredMeasure_finiteOnCompacts F ζ hζ R U,
    sphericalMeasure_finiteOnCompacts F ζ hζ R P U,
    coveredMeasure_regular F ζ hζ R U,
    sphericalMeasure_regular F ζ hζ R P U,
    coveredMeasure_sigmaFinite F ζ hζ R U,
    sphericalMeasure_sigmaFinite F ζ hζ R P U,
    compactSupport_memLp F ζ hζ R U,
    compactSupport_sectionSquaredNormIntegral_lt_top F ζ hζ R P H U⟩

end DedekindZetaZeroFree.KPContSectorFixedMeasureLocalFiniteness

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
