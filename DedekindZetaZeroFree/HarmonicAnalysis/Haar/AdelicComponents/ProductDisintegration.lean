module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArchimedeanFundamentalDomain
public import DedekindZetaZeroFree.Adeles.Quotients.ComponentProductTiling
public import DedekindZetaZeroFree.MeasureTheory.Quotients.PartialFundamentalDomainPushforward

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Pointwise
open MeasureTheory Function

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem actual_archProjection_compare
    (g : KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ)
    (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
  open KPAdelicCoverRestrictedProduct in
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _ (projection F ζ hζ g)) =
    Matrix.ProjGenLinGroup.map _ (Matrix.ProjGenLinGroup.mk
      (matrixEval F (Sum.inl w) (projection F ζ hζ g)))
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.GeneralLinearGroup.map_comp]
  rfl

private theorem actual_finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  obtain ⟨e, he, hi, hs, hker, hrest⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← hker]
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    funext w
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have hw := congrFun hg w
    rw [actual_archProjection_compare] at hw
    have hw' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) hw
    simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at hw'
    simpa [e] using hw'
  · intro hg
    funext w
    rw [actual_archProjection_compare, hg]
    exact map_one _

 theorem archFiniteEquiv_for_productHaar :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ*
      KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ,
      ∀ a c, e (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, hrest⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have hf := actual_finiteSubgroup_eq F ζ hζ
  change ∃ e : (PGLComplex.AdelicSlicesRaw.ArchGroup F ×
    KPFiniteCuspAtlas.FiniteCover F ζ hζ) ≃ₜ* _, _
  rw [← hf]
  exact ⟨e, he⟩

private theorem actual_product_haar
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) :
    ∃ ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ), ν.IsHaarMeasure ∧
      Measure.map (m F ζ hζ) (R.archHaar.prod ν) = R.adelicHaar := by
  letI := R.adelic_isHaar
  letI := R.arch_isHaar
  have hf := actual_finiteSubgroup_eq F ζ hζ
  change ∃ ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ), ν.IsHaarMeasure ∧
    Measure.map (fun p : KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2.val)
        (R.archHaar.prod ν) = R.adelicHaar
  rw [← hf]
  exact PGLComplex.AdelicSlicesRaw.productHaarTransport F ζ hζ R.adelicHaar R.archHaar

private theorem actual_finiteOrbit_compact_open
    (U : Level F ζ hζ) (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    IsCompact (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) ∧
      IsOpen (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  have hs : KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g =
      ⋃ ε : rootsOfUnity 3 F,
        (fun u => KPCuspGenuineMonodromy.central F ζ hζ ε * g * u) ''
          (U.toOpenSubgroup : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) := by
    ext c
    simp only [KPCuspGenuineMonodromy.finiteOrbit, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨ε, u, rfl⟩
      exact ⟨ε, u, u.property, rfl⟩
    · rintro ⟨ε, u, hu, rfl⟩
      exact ⟨ε, ⟨u, hu⟩, rfl⟩
  rw [hs]
  constructor
  · exact isCompact_iUnion fun ε => U.isCompact.image (continuous_const.mul continuous_id)
  · exact isOpen_iUnion fun ε => (Homeomorph.mulLeft _).isOpenMap _ U.toOpenSubgroup.isOpen

 theorem actual_finiteOrbit_positive_finite
    (U : Level F ζ hζ) (g : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] :
    MeasurableSet (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) ∧
      0 < ν (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) ∧
      ν (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g) < ⊤ := by
  obtain ⟨hcompact, hopen⟩ := actual_finiteOrbit_compact_open F ζ hζ U g
  have hnonempty : (KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g).Nonempty := by
    refine ⟨KPCuspGenuineMonodromy.central F ζ hζ 1 * g * 1, 1, 1, rfl⟩
  exact ⟨hopen.measurableSet, hopen.measure_pos ν hnonempty, hcompact.measure_lt_top⟩

theorem actual_component_product_disintegration
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (i : Fin A.componentCount) :
    ∃ ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ), ν.IsHaarMeasure ∧
      Measure.map (m F ζ hζ) (R.archHaar.prod ν) = R.adelicHaar ∧
      ∃ D : Set (KPSmoothActualFlowData.GInfinity F),
        MeasurableSet D ∧
        IsFundamentalDomain (Ga F ζ hζ hF U A i) D R.archHaar ∧
        MeasurableSet (B F ζ hζ hF U A i) ∧
        0 < ν (B F ζ hζ hF U A i) ∧ ν (B F ζ hζ hF U A i) < ⊤ ∧
        R.quotientHaar.restrict (P.projection U ⁻¹' C F ζ hζ hF U A i) =
          Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘ m F ζ hζ)
            ((R.archHaar.restrict D).prod (ν.restrict (B F ζ hζ hF U A i))) := by
  obtain ⟨ν, hν, hproduct⟩ := actual_product_haar F ζ hζ R
  letI := hν
  obtain ⟨hBm, hBpositive, hBfinite⟩ :=
    actual_finiteOrbit_positive_finite F ζ hζ U (A.representative i) ν
  letI := R.arch_isHaar
  letI := R.adelic_isHaar
  obtain ⟨D, hDm, hD⟩ :=
    ProductDisintegration.primitive_arch_group_domain F ζ hζ hF U A i R.archHaar
  obtain ⟨hT, hSm, hSsub, hS⟩ :=
    ProductDisintegration.product_domain_partial_fundamental
      F ζ hζ hF U A R P i ν hproduct D hDm hD
  refine ⟨ν, hν, hproduct, D, hDm, hD, hBm, hBpositive, hBfinite, ?_⟩
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) := by
    have hΓ := ActualQuotient.actual_rational_closed_discrete F ζ hζ
    exact (IsLindelof.countable_of_isDiscrete hΓ.1.isLindelof hΓ.2).to_subtype
  have hq : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    (show Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) from
      continuous_quot_mk).measurable
  have hqi : ∀ (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) y,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (γ • y) =
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ y := by
    intro γ y
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa [Subgroup.smul_def, mul_assoc] using γ.property
  have hcompare := ProductDisintegration.quotient_restrict_of_partial_domain
    R.adelicHaar R.domain R.domain_measurable R.domain_fundamental
    (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) hq hqi
    (P.projection U ⁻¹' C F ζ hζ hF U A i) hT
    (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) hSm hSsub hS
  rw [R.quotient_normalization] at hcompare
  rw [hcompare]
  obtain ⟨e, he⟩ := archFiniteEquiv_for_productHaar F ζ hζ
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F ×
      KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isOpenQuotientMap_snd (X := KPSmoothActualFlowData.GInfinity F)).locallyCompactSpace
  letI : SFinite ν := inferInstance
  have hem : MeasurableEmbedding (m F ζ hζ) := by
    have heq : m F ζ hζ = e := by
      funext p
      exact (he p.1 p.2).symm
    rw [heq]
    exact e.toHomeomorph.measurableEmbedding
  have hrestrict : R.adelicHaar.restrict (m F ζ hζ '' (D ×ˢ B F ζ hζ hF U A i)) =
      Measure.map (m F ζ hζ)
        ((R.archHaar.restrict D).prod (ν.restrict (B F ζ hζ hF U A i))) := by
    rw [← hproduct, hem.restrict_map, hem.injective.preimage_image, Measure.prod_restrict]
  rw [hrestrict, Measure.map_map hq hem.measurable]

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
