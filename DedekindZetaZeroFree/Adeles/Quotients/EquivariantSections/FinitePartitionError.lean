module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.FinitePartitionsOfUnity
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal BigOperators NNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFinitePartitionError

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies KPContActualCotangentChartRestriction
open KPContActualCotangentPieceHilbertSum
open KPContActualSectorFiniteSupportPartition
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings

open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

section Helpers
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem continuous_labeledA_placeEquiv :
    Continuous (labeledA (placeEquiv F ζ hζ)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

 theorem measurable_q (a : Chart (U := U) (H := H)) :
    Measurable (KPContCotangentOverlapRationalBranches.q a) := by
  have hcm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext x; exact ((H.atlas U).components_formula a.component x).symm
    rw [he]
    exact ((H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk).continuous
  have hproj : Measurable (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    measurable_quotient_mk''
  have hcomp : KPContCotangentOverlapRationalBranches.q a =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F
          (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.measurable.comp (hproj.comp continuous_labeledA_placeEquiv.measurable)

 theorem q_isotropyArrow (a : Chart (U := U) (H := H)) (γ : Gamma a) (x : M F)
    (hx : x ∈ omega a) :
    KPContCotangentOverlapRationalBranches.q a ((isotropyArrow a γ).psi x) =
      KPContCotangentOverlapRationalBranches.q a x := by
  simp only [KPContCotangentOverlapRationalBranches.q]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative a.component))
  simp only [Arrow.psi, coordinateMap, isotropyArrow, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have hh (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    funext k; simp [labeledA, labeledAInv]
  rw [hh]
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨γ.val.1.val, rfl⟩

 theorem q_actualBranch {a b : Chart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) :
    KPContCotangentOverlapRationalBranches.q b (e.arrow.psi x) =
      KPContCotangentOverlapRationalBranches.q a x := by
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  rcases e with ⟨h, e, hs, ht, hl⟩
  dsimp at h
  subst j
  simp only [KPContCotangentOverlapRationalBranches.q]
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U
    ((H.atlas U).representative i))
  simp only [Arrow.psi, coordinateMap, targetChart, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have ha (v : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    funext k; simp [labeledA, labeledAInv]
  rw [ha]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private theorem q_coordinates (a : Chart (U := U) (H := H)) (y : a.domain) :
    KPContCotangentOverlapRationalBranches.q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]

 def tensorMultiply (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (r : Family (U := U) (H := H)) : Family (U := U) (H := H) :=
  ⟨fun a x => (η (KPContCotangentOverlapRationalBranches.q a x.val) : ℂ) • coefficient r a x, by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ((Complex.measurable_ofReal.comp hη).comp
        ((measurable_q a).comp measurable_subtype_coe)).smul (r.property.1 a)
    · intro a γ x hx
      simp only [q_isotropyArrow a γ x hx, coefficient]
      rw [r.property.2.1 a γ x hx, map_smul]
    · intro a b e x hx
      simp only [q_actualBranch e x, coefficient]
      rw [r.property.2.2 a b e x hx, map_smul]⟩

 theorem tensorMultiply_norm (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (r : Family (U := U) (H := H)) :
    ∀ b, (normSquare (tensorMultiply η hη r) b : ℝ) = η b ^ 2 * (normSquare r b : ℝ) := by
  have huniq := (Classical.choose_spec (normSquare_descends (tensorMultiply η hη r))).2
  let v : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0 := fun b =>
    ⟨η b ^ 2 * (normSquare r b : ℝ), by positivity⟩
  have hv : normSquare (tensorMultiply η hη r) = v := (huniq v (by
    refine ⟨?_, ?_⟩
    · exact ((hη.pow_const 2).mul ((measurable_normSquare r).coe_nnreal_real)).subtype_mk
    · intro a x
      apply NNReal.eq
      change η (KPContCotangentOverlapRationalBranches.q a x.val) ^ 2 *
        (normSquare r (KPContCotangentOverlapRationalBranches.q a x.val) : ℝ) =
        (‖coefficient (tensorMultiply η hη r) a x‖₊ ^ 2 : ℝ)
      rw [normSquare_chart]
      simp only [NNReal.coe_pow, coe_nnnorm]
      change _ = ‖(η _ : ℂ) • coefficient r a x‖ ^ 2
      rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs])).symm
  intro b
  rw [hv]
  rfl

 def tensorMultiplySquare (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (hη0 : ∀ b, 0 ≤ η b) (hη1 : ∀ b, η b ≤ 1)
    (r : SquareFiniteFamily (U := U) (H := H)) : SquareFiniteFamily (U := U) (H := H) :=
  ⟨tensorMultiply η hη r.val, by
    refine lt_of_le_of_lt (lintegral_mono (fun b => ?_)) r.property
    apply ENNReal.ofReal_le_ofReal
    rw [tensorMultiply_norm]
    have hsq : η b ^ 2 ≤ 1 := by nlinarith [hη0 b, hη1 b]
    nlinarith [show (0 : ℝ) ≤ normSquare r.val b from NNReal.coe_nonneg _]⟩

private theorem lp_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {g : α → E} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have hi := L2.inner_def (𝕜 := ℝ) (hg.toLp g) (hg.toLp g)
  rw [inner_self_eq_norm_sq_to_K] at hi
  refine hi.trans (integral_congr_ae ?_)
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [hx, inner_self_eq_norm_sq_to_K]

private theorem tensor_enorm (r : SquareFiniteFamily (U := U) (H := H)) :
    ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ₑ =
      eLpNorm (fun b => Real.sqrt (normSquare r.val b : ℝ)) 2
        (baseMeasure (U := U) (R := R) (P := P)) := by
  have hm : Measurable (fun b => Real.sqrt (normSquare r.val b : ℝ)) :=
    (measurable_normSquare r.val).coe_nnreal_real.sqrt
  have hsq : (fun b => ‖Real.sqrt (normSquare r.val b : ℝ)‖ ^ 2) =
      (fun b => (normSquare r.val b : ℝ)) := by
    funext b
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (NNReal.coe_nonneg _)]
  have hlp : MemLp (fun b => Real.sqrt (normSquare r.val b : ℝ)) 2
      (baseMeasure (U := U) (R := R) (P := P)) := by
    rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable, hsq]
    exact KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare r
  have hn := KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral
    (KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H)
    (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r) r rfl
  have he : ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ =
      ‖hlp.toLp (fun b => Real.sqrt (normSquare r.val b : ℝ))‖ := by
    have hs := lp_norm_sq hlp
    rw [hsq] at hs
    nlinarith [norm_nonneg (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r),
      norm_nonneg (hlp.toLp (fun b => Real.sqrt (normSquare r.val b : ℝ)))]
  rw [← ofReal_norm_eq_enorm, he, ofReal_norm_eq_enorm, Lp.enorm_toLp]

private theorem exists_chart_point (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : Chart (U := U) (H := H)) (x : omega a),
      KPContCotangentOverlapRationalBranches.q a x.val = b := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hb : b ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, y, hy⟩ := Set.mem_iUnion.mp hb
  exact ⟨cover.chart n, coordinates (cover.chart n) y, (q_coordinates _ _).trans hy⟩

private theorem tensor_local_enorm (a : Chart (U := U) (H := H))
    (r : SquareFiniteFamily (U := U) (H := H))
    (hz : ∀ b, b ∉ a.baseDomain → normSquare r.val b = 0) :
    ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r‖ₑ =
      eLpNorm (localCoefficient a r.val) 2 a.liftedMeasure := by
  rw [tensor_enorm]
  have ha := every_shrunkChart_properties F ζ hζ U R P H a
  let v := fun b => Real.sqrt (normSquare r.val b : ℝ)
  have hv : Measurable v := (measurable_normSquare r.val).coe_nnreal_real.sqrt
  have he : v = a.baseDomain.indicator v := by
    funext b
    by_cases hb : b ∈ a.baseDomain
    · exact (Set.indicator_of_mem hb _).symm
    · simp [v, hz b hb, Set.indicator_of_notMem hb]
  rw [show eLpNorm v 2 baseMeasure = eLpNorm v 2 (baseMeasure.restrict a.baseDomain) from by
    conv_lhs => rw [he]
    exact eLpNorm_indicator_eq_eLpNorm_restrict ha.base_measurable.nullMeasurableSet]
  rw [← ha.exact_pushforward, eLpNorm_map_measure
    (by rw [ha.exact_pushforward]; exact hv.aestronglyMeasurable)
    ha.measurable.aemeasurable]
  apply eLpNorm_congr_norm_ae
  · exact (hv.comp ha.measurable).aestronglyMeasurable
  · exact (localCoefficient_memLp a r).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro y
    change ‖Real.sqrt (normSquare r.val (a.toBase y) : ℝ)‖ = ‖localCoefficient a r.val y‖
    rw [← q_coordinates a y, normSquare_chart, NNReal.coe_pow, coe_nnnorm,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
    rfl

private theorem scalar_chart_norm (a : Chart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionNorm F ζ hζ U R P H s (a.toBase y) = ‖(a.coefficient s y : ℂ)‖ := by
  change sectionNorm F ζ hζ U R P H s
    (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (Quotient.mk _ y.val)) = ‖(s a.component).val y.val‖
  rw [← (H.atlas U).components_formula]
  exact sectionNorm_component F ζ hζ U R P H s a.component y.val

private theorem scalar_section_memLp (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (sectionNorm F ζ hζ U R P H s.val) 2
      (baseMeasure (R := R) (P := P) (U := U)) := by
  have hme : Measurable (sectionNorm F ζ hζ U R P H s.val) := by
    let f := scalarRepresentative F ζ hζ U R P H s.val
    have hnorm := (kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f
      ((borel_iff F ζ hζ U R P H s.val).mp s.property.1)).borel
    have hh : sectionNorm F ζ hζ U R P H s.val =
        fun b => Real.sqrt (KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f b).toReal := by
      funext b
      change _ = Real.sqrt (ENNReal.ofReal
        (sectionNorm F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f) b ^ 2)).toReal
      rw [show KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f = s.val from
        (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s.val]
      rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq_eq_abs]
      exact (abs_of_nonneg (by
        obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
        obtain ⟨x,rfl⟩ := Quotient.exists_rep q
        rw [sectionNorm_component]; exact norm_nonneg _)).symm
    rw [hh]
    exact hnorm.ennreal_toReal.sqrt
  have hn : ∀ b, 0 ≤ sectionNorm F ζ hζ U R P H s.val b := by
    intro b
    obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
    obtain ⟨x,rfl⟩ := Quotient.exists_rep q
    rw [sectionNorm_component]; exact norm_nonneg _
  rw [memLp_two_iff_integrable_sq_norm hme.aestronglyMeasurable]
  refine ⟨hme.norm.pow_const 2 |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [Real.norm_eq_abs, sq_abs, Real.enorm_eq_ofReal_abs, abs_pow,
    sq_abs, normIntegral, squaredNorm] using s.property.2

private theorem scalar_enorm (s : BorelL2Sections F ζ hζ U R P H) :
    ‖toSector F ζ hζ U R P H s‖ₑ =
      eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2
      (baseMeasure (R := R) (P := P) (U := U)) := by
  have hm := scalar_section_memLp s
  have hh := lp_norm_sq hm
  have hreal : ∫ b, ‖sectionNorm F ζ hζ U R P H s.val b‖ ^ 2
      ∂(baseMeasure (R := R) (P := P) (U := U)) =
      (normIntegral F ζ hζ U R P H s.val).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun b => sq_nonneg _))
      ((hm.aestronglyMeasurable.norm.aemeasurable.pow_const 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro b
    simp only [Real.norm_eq_abs, sq_abs, squaredNorm, normIntegral]
  have hn : ‖toSector F ζ hζ U R P H s‖ ^ 2 =
      (normIntegral F ζ hζ U R P H s.val).toReal := by
    rw [← KPContSectorLineL2Isometry.norm_sq F ζ hζ U R P H s]
    rfl
  have he : ‖toSector F ζ hζ U R P H s‖ =
      ‖hm.toLp (sectionNorm F ζ hζ U R P H s.val)‖ := by
    nlinarith [norm_nonneg (toSector F ζ hζ U R P H s),
      norm_nonneg (hm.toLp (sectionNorm F ζ hζ U R P H s.val))]
  rw [← ofReal_norm_eq_enorm, he, ofReal_norm_eq_enorm, Lp.enorm_toLp]

 def scalarMultiplyBorel (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (hη0 : ∀ b, 0 ≤ η b) (hη1 : ∀ b, η b ≤ 1)
    (s : BorelL2Sections F ζ hζ U R P H) : BorelL2Sections F ζ hζ U R P H := by
  let v := scalarRepresentative F ζ hζ U R P H s.val
  let f : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U :=
    ⟨fun x => (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) * v.val x, by
      intro ε x
      simp only [KPContSectorCoveredQuotientVocabulary.q_z, v.property ε x]
      ring⟩
  have hq : Measurable (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hf : Measurable f.val :=
    ((Complex.measurable_ofReal.comp hη).comp hq).mul
      ((borel_iff F ζ hζ U R P H s.val).mp s.property.1)
  have hlp : MemLp f.val 2 (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
    apply (representative_memLp F ζ hζ U R P H s).of_le hf.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖(η _ : ℂ) * v.val x‖ ≤ ‖v.val x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hη1 _)
  exact KPContSectorLineL2Isometry.borelS F ζ hζ U R P H ⟨f, hf, hlp⟩

private theorem scalarMultiplyBorel_coefficient
    (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (hη0 : ∀ b, 0 ≤ η b) (hη1 : ∀ b, η b ≤ 1)
    (s : BorelL2Sections F ζ hζ U R P H) (a : Chart (U := U) (H := H)) (y : a.domain) :
    (a.coefficient (scalarMultiplyBorel η hη hη0 hη1 s).val y : ℂ) =
      (η (a.toBase y) : ℂ) * (a.coefficient s.val y : ℂ) := by
  change (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
    ⟨_,_⟩ a.component).val y.val = _
  rw [KPContSectorScalarLineAlgebra.S_apply]
  change (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
    (Quotient.mk _ (y.val, (H.atlas U).representative a.component))) : ℂ) *
    (scalarRepresentative F ζ hζ U R P H s.val).val
      (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _
  rw [KPContSectorCoveredQuotientVocabulary.q_mk]
  have he := congrArg (fun t : Sections F ζ hζ U R P H => (t a.component).val y.val)
    ((KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s.val)
  rw [KPContSectorScalarLineAlgebra.S_apply] at he
  change (scalarRepresentative F ζ hζ U R P H s.val).val
    (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _ at he
  rw [he]
  congr 2

private theorem scalar_local_enorm (a : Chart (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H)
    (hz : ∀ b, b ∉ a.baseDomain → sectionNorm F ζ hζ U R P H s.val b = 0) :
    ‖toSector F ζ hζ U R P H s‖ₑ =
      eLpNorm (fun y : a.domain => (a.coefficient s.val y : ℂ)) 2 a.liftedMeasure := by
  rw [scalar_enorm]
  have ha := every_shrunkChart_properties F ζ hζ U R P H a
  have hm := scalar_section_memLp s
  have he : sectionNorm F ζ hζ U R P H s.val =
      a.baseDomain.indicator (sectionNorm F ζ hζ U R P H s.val) := by
    funext b
    by_cases hb : b ∈ a.baseDomain
    · exact (Set.indicator_of_mem hb _).symm
    · rw [Set.indicator_of_notMem hb, hz b hb]
  rw [show eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 baseMeasure =
      eLpNorm (sectionNorm F ζ hζ U R P H s.val) 2 (baseMeasure.restrict a.baseDomain) from by
    conv_lhs => rw [he]
    exact eLpNorm_indicator_eq_eLpNorm_restrict ha.base_measurable.nullMeasurableSet]
  rw [← ha.exact_pushforward, eLpNorm_map_measure
    (by rw [ha.exact_pushforward]; exact hm.aestronglyMeasurable.restrict)
    ha.measurable.aemeasurable]
  have hc : Measurable (fun y : a.domain => (a.coefficient s.val y : ℂ)) :=
    (s.property.1 a.component).comp measurable_subtype_coe
  apply eLpNorm_congr_norm_ae
  · have hp : MeasurePreserving a.toBase a.liftedMeasure
        (baseMeasure.restrict a.baseDomain) := ⟨ha.measurable, ha.exact_pushforward⟩
    exact (hm.aestronglyMeasurable.restrict.comp_measurePreserving hp)
  · exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro y
    change ‖sectionNorm F ζ hζ U R P H s.val (a.toBase y)‖ = _
    rw [scalar_chart_norm, Real.norm_of_nonneg (norm_nonneg _)]

private theorem scalar_field_coefficient (a : Chart (U := U) (H := H))
    (s : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionFields s a (coordinates a y) = (a.coefficient s y : ℂ) := by
  have hi : ∀ v : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    intro v; funext k; simp [labeledA, labeledAInv]
  simp only [sectionFields, KPContCotangentActualOverlap.LiftedChart.coefficient,
    isotropyChart, coordinates]
  simp [hi, ChartKind.representative, ShrunkChart.coefficient, liftCoefficient]

end Helpers

set_option maxHeartbeats 800000 in

theorem scalar
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (n : ℕ) (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (partition : FinitePartition F ζ hζ U R P H C K O)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : ∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → sectionNorm F ζ hζ U R P H s.val b = 0)
    (f : ∀ i : Fin n, localScalarTests (C i)) :
    ‖toSector F ζ hζ U R P H s -
      iota (∑ i, scalarZeroExtension (C i) (f i))‖ₑ ≤
      ∑ i, eLpNorm (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) *
          ((C i).coefficient s.val y : ℂ) -
            (f i).val (coordinates (C i) y)) 2 (C i).liftedMeasure := by
  let realization := actual_levelRealization_of_recipe F ζ hζ U R P H
  let S := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar R.adelic_isHaar
    U R rfl P H realization
  let z : Fin n → BorelL2Sections F ζ hζ U R P H := fun i =>
    scalarMultiplyBorel (partition.multiplier i) (partition.continuous i).measurable
      (partition.nonnegative i) (partition.at_most_one i) s
  let t : Fin n → BorelL2Sections F ζ hζ U R P H := fun i =>
    KPContSectorLineL2Isometry.borelS F ζ hζ U R P H
      ⟨scalarCovered (scalarZeroExtension (C i) (f i)),
        ((borel_iff F ζ hζ U R P H _).mp (by
          intro k
          exact (S.scalar_smooth (scalarZeroExtension (C i) (f i)) k).continuous.measurable)),
        scalar_memLp (scalarZeroExtension (C i) (f i))⟩
  have ht : ∀ i, (t i).val = scalarSections (scalarZeroExtension (C i) (f i)) := by
    intro i
    exact S.covered_realization _
  have hcoef : ∀ i y, ((C i).coefficient (t i).val y : ℂ) =
      (f i).val (coordinates (C i) y) := by
    intro i y
    rw [ht, ← scalar_field_coefficient, S.scalar_represented]
    exact congrFun (S.scalar_restriction_extension (C i) (f i)) (coordinates (C i) y)
  have hemb : ∀ i, toSector F ζ hζ U R P H (t i) = iota (scalarZeroExtension (C i) (f i)) := by
    intro i
    apply Subtype.ext
    exact scalarEmbedding_coe F ζ hζ U R P H _
  let d := fun i => z i - t i
  have hrec : toSector F ζ hζ U R P H s = toSector F ζ hζ U R P H (∑ i, z i) := by
    change lineToSector F ζ hζ U R P H (mk F ζ hζ U R P H s) =
      lineToSector F ζ hζ U R P H (mk F ζ hζ U R P H (∑ i,z i))
    apply congrArg (lineToSector F ζ hζ U R P H)
    apply ((kp_cont_sector_line_l2_isometry F ζ hζ U R P H).null_relation s (∑ i,z i)).mpr
    filter_upwards [hs] with b hb
    obtain ⟨a,x,hx⟩ := exists_chart_point (R := R) (P := P) (H := H) b
    let y := KPContActualCotangentPieceReconstruction.originalPoint a x
    have hy : a.toBase y = b := hx
    rw [← hy]
    change ENNReal.ofReal (sectionNorm F ζ hζ U R P H (s.val - (∑ i,z i).val) (a.toBase y) ^ 2) = 0
    rw [scalar_chart_norm]
    have he : (a.coefficient (s.val - (∑ i,z i).val) y : ℂ) = 0 := by
      change (s.val a.component).val y.val - ((∑ i,z i).val a.component).val y.val = 0
      simp only [Submodule.coe_sum, Finset.sum_apply]
      change (a.coefficient s.val y : ℂ) - ∑ i, (a.coefficient (z i).val y : ℂ) = 0
      simp only [z, scalarMultiplyBorel_coefficient]
      rw [← Finset.sum_mul]
      by_cases hk : b ∈ K
      · have hp := partition.partition b (partition.contains_compact hk)
        have hp' : ∑ i, (partition.multiplier i (a.toBase y) : ℂ) = 1 := by rw [hy]; norm_cast
        rw [hp', one_mul, sub_self]
      · have hz : (a.coefficient s.val y : ℂ) = 0 := by
          have hh := hb hk
          rw [← hy, scalar_chart_norm, norm_eq_zero] at hh
          exact hh
        rw [hz, mul_zero, sub_self]
    simp only [he, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), ENNReal.ofReal_zero]
  have hlocal : ∀ i, ‖toSector F ζ hζ U R P H (d i)‖ₑ =
      eLpNorm (fun y : (C i).domain => (partition.multiplier i ((C i).toBase y):ℂ) *
        ((C i).coefficient s.val y:ℂ) - (f i).val (coordinates (C i) y)) 2 (C i).liftedMeasure := by
    intro i
    rw [scalar_local_enorm (C i) (d i) (by
      intro b hb
      obtain ⟨a,x,hx⟩ := exists_chart_point (R := R) (P := P) (H := H) b
      let y := KPContActualCotangentPieceReconstruction.originalPoint a x
      have hy : a.toBase y = b := hx
      rw [← hy, scalar_chart_norm]
      have hm : partition.multiplier i b = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hb (partition.support_subset i h).1)
      change ‖(a.coefficient (z i).val y:ℂ) - (a.coefficient (t i).val y:ℂ)‖ = 0
      dsimp only [z]
      rw [scalarMultiplyBorel_coefficient, hy, hm, Complex.ofReal_zero, zero_mul, ht,
        ← scalar_field_coefficient, S.scalar_represented]
      have hzero := S.scalar_extension_zero (C i) (f i) a (coordinates a y)
        (by rw [q_coordinates, hy]; exact hb)
      rw [hzero, sub_self, norm_zero])]
    apply eLpNorm_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    change ( (C i).coefficient (z i).val y : ℂ) - ((C i).coefficient (t i).val y : ℂ) = _
    dsimp only [z]
    rw [scalarMultiplyBorel_coefficient, hcoef]
  have he : toSector F ζ hζ U R P H s - iota (∑ i,scalarZeroExtension (C i) (f i)) =
      ∑ i, toSector F ζ hζ U R P H (d i) := by
    rw [hrec, map_sum, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hemb]
    exact (map_sub (toSector F ζ hζ U R P H) (z i) (t i)).symm
  rw [he]
  calc ‖∑ i, toSector F ζ hζ U R P H (d i)‖ₑ
      ≤ ∑ i, ‖toSector F ζ hζ U R P H (d i)‖ₑ := by
        simpa only [← ofReal_norm_eq_enorm,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg (toSector F ζ hζ U R P H (d i)))]
          using ENNReal.ofReal_le_ofReal (norm_sum_le Finset.univ
            (fun i => toSector F ζ hζ U R P H (d i)))
    _ = _ := Finset.sum_congr rfl (fun i _ => hlocal i)

theorem cotangent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (n : ℕ) (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (partition : FinitePartition F ζ hζ U R P H C K O)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : ∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → normSquare r.val b = 0)
    (w : ∀ i : Fin n, localCotangentTests (C i)) :
    ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
      j (∑ i, cotangentZeroExtension (C i) (w i))‖ₑ ≤
      ∑ i, eLpNorm (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) •
          localCoefficient (C i) r.val y -
            (w i).val (coordinates (C i) y)) 2 (C i).liftedMeasure := by
  let realization := actual_levelRealization_of_recipe F ζ hζ U R P H
  let S := kp_cont_actual_sector_smooth_test_modules F ζ hζ R.adelicHaar R.adelic_isHaar
    U R rfl P H realization
  let z : Fin n → SquareFiniteFamily (U := U) (H := H) := fun i =>
    tensorMultiplySquare (partition.multiplier i) (partition.continuous i).measurable
      (partition.nonnegative i) (partition.at_most_one i) r
  let d : Fin n → SquareFiniteFamily (U := U) (H := H) := fun i =>
    z i - cotangentSquareFamily (cotangentZeroExtension (C i) (w i))
  have hrec : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r =
      KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (∑ i, z i) := by
    apply (KPContActualSectorCotangentL2.ofFamily_eq_iff _ _ _ _ _ _ _ _ _).mpr
    filter_upwards [hr] with b hb
    obtain ⟨a, x, hx⟩ := exists_chart_point (R := R) (P := P) (H := H) b
    rw [← hx, normSquare_chart]
    have he : coefficient (r.val - (∑ i, z i).val) a x = 0 := by
      simp only [coefficient, Submodule.coe_sub, Submodule.coe_sum, Finset.sum_apply,
        Pi.sub_apply]
      change coefficient r.val a x - (∑ i, (partition.multiplier i
        (KPContCotangentOverlapRationalBranches.q a x.val) : ℂ) • coefficient r.val a x) = 0
      by_cases hbk : b ∈ K
      · have hp := partition.partition b (partition.contains_compact hbk)
        rw [hx, ← Finset.sum_smul]
        have hp' : (∑ i, (partition.multiplier i b : ℂ)) = 1 := by
          norm_cast
        rw [hp', one_smul, sub_self]
      · have hzero : coefficient r.val a x = 0 := by
          have hh := hb hbk
          rw [← hx, normSquare_chart, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0),
            nnnorm_eq_zero] at hh
          exact hh
        simp only [hzero, smul_zero, Finset.sum_const_zero, sub_self]
    simp only [he, nnnorm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hlocal : ∀ i, ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (d i)‖ₑ =
      eLpNorm (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) • localCoefficient (C i) r.val y -
          (w i).val (coordinates (C i) y)) 2 (C i).liftedMeasure := by
    intro i
    rw [tensor_local_enorm (C i) (d i) (by
      intro b hb
      obtain ⟨a, x, hx⟩ := exists_chart_point (R := R) (P := P) (H := H) b
      rw [← hx, normSquare_chart]
      have hm : partition.multiplier i b = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        hb (partition.support_subset i h).1)
      have hz := S.cotangent_extension_zero (C i) (w i) a x (hx ▸ hb)
      change ‖(partition.multiplier i (KPContCotangentOverlapRationalBranches.q a x.val) : ℂ) •
        coefficient r.val a x - coefficient (cotangentZeroExtension (C i) (w i)).val a x‖₊ ^ 2 = 0
      simp only [hx, hm, Complex.ofReal_zero, zero_smul, hz, sub_zero, nnnorm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0)])]
    apply eLpNorm_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    have he := congrFun (S.cotangent_restriction_extension (C i) (w i)) (coordinates (C i) y)
    change (partition.multiplier i (KPContCotangentOverlapRationalBranches.q (C i)
      (coordinates (C i) y).val) : ℂ) • localCoefficient (C i) r.val y -
      coefficient (cotangentZeroExtension (C i) (w i)).val (C i) (coordinates (C i) y) = _
    change coefficient (cotangentZeroExtension (C i) (w i)).val (C i)
      (coordinates (C i) y) = _ at he
    rw [q_coordinates, he]
  have he : KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
      j (∑ i, cotangentZeroExtension (C i) (w i)) =
      ∑ i, KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (d i) := by
    rw [hrec, map_sum, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change _ = (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H)
      (z i - cotangentSquareFamily (cotangentZeroExtension (C i) (w i)))
    have hsub : z i - cotangentSquareFamily (cotangentZeroExtension (C i) (w i)) =
        z i + (-1 : ℂ) • cotangentSquareFamily (cotangentZeroExtension (C i) (w i)) := by
      apply Subtype.ext
      apply Subtype.ext
      funext a x
      simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, neg_one_smul, sub_eq_add_neg]
    rw [hsub, map_add, map_smul]
    simp only [neg_one_smul, sub_eq_add_neg]
    rfl
  rw [he]
  calc ‖∑ i, KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (d i)‖ₑ
      ≤ ∑ i, ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (d i)‖ₑ := enorm_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => hlocal i)

end DedekindZetaZeroFree.KPContActualFinitePartitionError

end
