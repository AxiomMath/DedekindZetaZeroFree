module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CoherentPinnedCuspGeometry

@[expose] public section

section

noncomputable section

open scoped Classical NumberField ENNReal NNReal

open MeasureTheory

namespace DedekindZetaZeroFree

namespace KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Level := CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)

abbrev Spherical (U : Level F ζ hζ) := KPFiniteCuspAtlas.rawXU F ζ hζ U

instance (U : Level F ζ hζ) : MeasurableSpace (Spherical F ζ hζ U) := borel _

instance (U : Level F ζ hζ) : BorelSpace (Spherical F ζ hζ U) := ⟨rfl⟩

end KPMsFixedHaarDisintegration

end DedekindZetaZeroFree

end

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem fixed_haar_recipe
    (μ : Measure (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ))
    (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure := by

  obtain ⟨e, he, hep, hip, hker, hcen, hlc⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI : LocallyCompactSpace
      (PGLComplex.AdelicSlicesRaw.ArchGroup F ×
        ↥(PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).locallyCompactSpace
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ArchGroup F) := ⟨rfl⟩
  let archHaar : Measure (KPSmoothLocalQuotientCharts.ArchGroup F) := MeasureTheory.Measure.haar
  have arch_isHaar : archHaar.IsHaarMeasure := inferInstance

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
  have hdisc : DiscreteTopology (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    SetLike.isDiscrete_iff_discreteTopology.mp
      (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2
  letI : SecondCountableTopology (Cover F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ

  haveI : ProperlyDiscontinuousSMul (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      (Cover F ζ hζ) := by
    have hH : IsCompact (MulAction.stabilizer (Cover F ζ hζ)
        (1 : Cover F ζ hζ) : Set (Cover F ζ hζ)) := by
      have h : MulAction.stabilizer (Cover F ζ hζ) (1 : Cover F ζ hζ) = ⊥ := by
        ext g; simp [MulAction.mem_stabilizer_iff]
      rw [h]; exact isCompact_singleton
    exact KPArithmeticAction.properlyDiscontinuous_of_section (1 : Cover F ζ hζ) id
      continuous_id (fun x => by simp) hH (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)

  have hfree : ∀ᵐ x ∂μ, ∀ g : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
      g • x = x → g = 1 := by
    refine Filter.Eventually.of_forall fun x g hg => ?_
    have h2 : (g : Cover F ζ hζ) * x = x := hg
    have : (g : Cover F ζ hζ) = 1 := by
      calc (g : Cover F ζ hζ) = (g : Cover F ζ hζ) * x * x⁻¹ := by simp
        _ = x * x⁻¹ := by rw [h2]
        _ = 1 := by simp
    exact Subtype.ext this
  obtain ⟨Ω, hΩmeas, hΩfund⟩ :=
    KPCuspChart.SectionConstruction.measurable_fundamental_domain_of_properly_discontinuous_ae_free
      (H := KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (X := Cover F ζ hζ) μ hfree
  let R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ := {
    adelicHaar := μ
    adelic_isHaar := hμ
    archHaar := archHaar
    arch_isHaar := arch_isHaar
    quotientHaar := Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) (μ.restrict Ω)
    domain := Ω
    domain_measurable := hΩmeas
    domain_fundamental := hΩfund
    quotient_normalization := rfl }
  exact ⟨R, rfl, (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1⟩

end DedekindZetaZeroFree.KPMsFixedHaar

end
end

section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsFixedHaar

private theorem affine_probability_haar
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [MeasurableSpace T] [BorelSpace T] [LocallyCompactSpace T]
    (e : T ≃ₜ T) (he : ∀ x y, e (x + y) = e x + e y - e 0)
    (ν : Measure T) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    Measure.map e ν = ν := by
  let h : T ≃ₜ T := e.trans (Homeomorph.subRight (e 0))
  let a : T ≃ₜ+ T := {
    toHomeomorph := h
    map_add' := fun x y => by
      change e (x + y) - e 0 = (e x - e 0) + (e y - e 0)
      rw [he]
      abel }
  haveI : (Measure.map a ν).IsAddHaarMeasure := a.isAddHaarMeasure_map ν
  haveI : IsProbabilityMeasure (Measure.map a ν) :=
    Measure.isProbabilityMeasure_map_iff a.continuous.measurable.aemeasurable |>.mpr inferInstance
  have ha : Measure.map a ν = ν := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hcomp : (fun x => e 0 + a x) = e := by
    funext x
    change e 0 + (e x - e 0) = e x
    abel
  rw [← hcomp]
  change Measure.map ((fun x => e 0 + x) ∘ a) ν = ν
  rw [← Measure.map_map (show Measurable (fun x : T => e 0 + x) from
    (continuous_const.add continuous_id).measurable)
    (show Measurable (a : T → T) from a.continuous.measurable), ha]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self _

theorem torusAction_probability_haar
    {F : Type*} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D)
    [MeasurableSpace (KPCuspCharts.Torus F D.L)]
    [BorelSpace (KPCuspCharts.Torus F D.L)]
    [LocallyCompactSpace (KPCuspCharts.Torus F D.L)]
    (ν : Measure (KPCuspCharts.Torus F D.L))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] (u : D.E) :
    Measure.map (G.torusAction u) ν = ν := by
  apply affine_probability_haar
  obtain ⟨g, rfl⟩ := D.surjective u
  obtain ⟨M, hM, hc⟩ := D.upper g g.property
  intro z w
  induction z using QuotientAddGroup.induction_on with | H x =>
    induction w using QuotientAddGroup.induction_on with | H y =>
      rw [← QuotientAddGroup.mk_add]
      change G.torusAction (D.ratio g) (QuotientAddGroup.mk (x + y)) =
        G.torusAction (D.ratio g) (QuotientAddGroup.mk x) +
          G.torusAction (D.ratio g) (QuotientAddGroup.mk y) -
            G.torusAction (D.ratio g) (QuotientAddGroup.mk 0)
      simp only [G.torusAction_formula g M _ hM hc]
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_sub]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
      ring

private theorem measurable_of_countable_open_cover
    {I X Y : Type*} [Countable I] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (s : I → Set X) (hs : ∀ i, IsOpen (s i)) (hc : (⋃ i, s i) = Set.univ)
    (f : X → Y) (hf : ∀ i, Measurable (fun x : s i => f x.val)) : Measurable f := by
  intro E hE
  have heq : f ⁻¹' E = ⋃ i, Subtype.val '' ((fun x : s i => f x.val) ⁻¹' E) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Subtype.exists,
      exists_and_right, exists_eq_right]
    constructor
    · intro hx
      have : x ∈ ⋃ i, s i := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
      exact ⟨i, hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      exact hx
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (hs i).isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr (hf i hE)

private theorem measurable_on_sigma
    {I Y : Type*} {X : I → Type*} [Countable I]
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [MeasurableSpace (Sigma X)] [BorelSpace (Sigma X)]
    [MeasurableSpace Y] (f : Sigma X → Y)
    (hf : ∀ i, Measurable (fun x : X i => f ⟨i,x⟩)) : Measurable f := by
  intro E hE
  have heq : f ⁻¹' E = ⋃ i, Sigma.mk i '' ((fun x : X i => f ⟨i,x⟩) ⁻¹' E) := by
    ext ⟨i,x⟩
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
    · intro hx
      obtain ⟨j, y, hy, he⟩ := Set.mem_iUnion.mp hx
      change f ⟨j,y⟩ ∈ E at hy
      change f ⟨i,x⟩ ∈ E
      rw [he] at hy
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (Topology.IsOpenEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image.mpr
      (hf i hE)

local instance torusMeasurable (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) :
    MeasurableSpace (KPCuspCharts.Torus F L) := Quotient.instMeasurableSpace
local instance torusBorel (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F)
    [IsClosed (KPCuspCharts.translationLattice F L : Set (KPCuspCharts.Horizontal F))] :
    BorelSpace (KPCuspCharts.Torus F L) := QuotientAddGroup.borelSpace
local instance baseMeasurable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    MeasurableSpace (KPCuspCharts.Base F hF E hE) := borel _
local instance baseBorel (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    BorelSpace (KPCuspCharts.Base F hF E hE) := ⟨rfl⟩

private theorem probability_torus_haar
    {F : Type*} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ ν : Measure (KPCuspCharts.Torus F D.L), ν.IsAddHaarMeasure ∧ IsProbabilityMeasure ν := by
  obtain ⟨hd, _⟩ := G.lattice
  haveI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  haveI : IsClosed (KPCuspCharts.translationLattice F D.L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI : CompactSpace (KPCuspCharts.Torus F D.L) := G.compact_torus
  let ν : Measure (KPCuspCharts.Torus F D.L) := Measure.addHaarMeasure ⊤
  refine ⟨ν, inferInstance, ⟨?_⟩⟩
  exact Measure.addHaarMeasure_self (K₀ := ⊤)

theorem probability_fiber_kernel
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Nonempty (FiberKernel A) := by
  classical
  let D := fun j : CuspIndex A => Parabolic A j
  let G := fun j : CuspIndex A => Geometry A j
  choose ν hν hp using fun j : CuspIndex A => probability_torus_haar (D j) (G j)
  haveI (j : CuspIndex A) : (ν j).IsAddHaarMeasure := hν j
  haveI (j : CuspIndex A) : IsProbabilityMeasure (ν j) := hp j
  haveI (j : CuspIndex A) : DiscreteTopology (KPCuspCharts.translationLattice F (D j).L) :=
    (G j).lattice.choose
  haveI (j : CuspIndex A) : IsClosed
      (KPCuspCharts.translationLattice F (D j).L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI (j : CuspIndex A) : LocallyCompactSpace (KPCuspCharts.Torus F (D j).L) :=
    QuotientAddGroup.instLocallyCompactSpace _
  let φ := fun (j : CuspIndex A) (b : KPCuspCharts.Shape F)
    (z : KPCuspCharts.Torus F (D j).L) =>
      (⟨j, (G j).atlas.lift (z,b)⟩ : CrossSection A)
  have hφ (j : CuspIndex A) (b : KPCuspCharts.Shape F) : Measurable (φ j b) := by
    apply Continuous.measurable
    exact (continuous_sigmaMk (σ := fun k : CuspIndex A =>
      KPCuspCharts.CrossQuotient F (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
        ((A.cuspAtlas k.1).cusp k.2) ((A.cuspAtlas k.1).representative k.2)))
      (i := j)).comp
      ((G j).atlas.continuous_lift.comp (continuous_id.prodMk continuous_const))
  have hmap (j : CuspIndex A) (b b' : KPCuspCharts.Shape F)
      (hb : (QuotientAddGroup.mk b : KPCuspCharts.Base F hF (D j).E
        (D j).integralUnits) = QuotientAddGroup.mk b') :
      Measure.map (φ j b) (ν j) = Measure.map (φ j b') (ν j) := by
    have hm := QuotientAddGroup.eq_iff_sub_mem.mp hb.symm
    change b' - b ∈ (KPCuspLogShape.logarithm F hF (D j).E (D j).integralUnits).range at hm
    obtain ⟨u, hu⟩ := AddMonoidHom.mem_range.mp hm
    have hb' : b' = b + KPCuspLogShape.logarithm F hF (D j).E
        (D j).integralUnits u := by rw [hu]; abel
    have heq : φ j b = φ j b' ∘ (G j).torusAction u.toMul := by
      funext z
      apply congrArg (Sigma.mk j)
      exact ((G j).atlas.orbit_equivalence z _ b b').mpr ⟨u.toMul, rfl, hb'⟩
    rw [heq, ← Measure.map_map (hφ j b') ((G j).torusAction u.toMul).measurable,
      torusAction_probability_haar (D j) (G j) (ν j) u.toMul]
  let K : Omega A → Measure (CrossSection A) := fun ω => Measure.map (φ ω.1 ω.2.out) (ν ω.1)
  have hformula (j : CuspIndex A) (b : KPCuspCharts.Shape F) :
      K ⟨j, QuotientAddGroup.mk b⟩ = Measure.map (φ j b) (ν j) := by
    apply hmap
    exact Quotient.out_eq _
  have hprob (ω : Omega A) : IsProbabilityMeasure (K ω) :=
    Measure.isProbabilityMeasure_map_iff (hφ ω.1 ω.2.out).aemeasurable |>.mpr inferInstance
  refine ⟨{ unipotent := K
            probability_unipotent := hprob
            fiber_support := ?_
            measurable_kernel := ?_
            fiber_formula := fun j b => ⟨ν j, hν j, hp j, hformula j b⟩ }⟩
  · intro ω
    haveI := hprob ω
    apply le_antisymm prob_le_one
    have hpφ (z : KPCuspCharts.Torus F (D ω.1).L) :
        angularProjection A (φ ω.1 ω.2.out z) = ω := by
      induction z using QuotientAddGroup.induction_on with | H x =>
        change (⟨ω.1, (G ω.1).atlas.projection
          ((G ω.1).atlas.lift (QuotientAddGroup.mk x, ω.2.out))⟩ : Omega A) = ω
        rw [(G ω.1).atlas.lift_formula, (G ω.1).atlas.projection_formula]
        exact congrArg (Sigma.mk ω.1) (Quotient.out_eq _)
    have heq : φ ω.1 ω.2.out ⁻¹' {x | angularProjection A x = ω} = Set.univ :=
      Set.eq_univ_of_forall hpφ
    have hm := Measure.le_map_apply (μ := ν ω.1) (hφ ω.1 ω.2.out).aemeasurable
      {x | angularProjection A x = ω}
    rw [heq, measure_univ] at hm
    exact hm
  · intro E hE
    apply measurable_on_sigma (X := fun j : CuspIndex A =>
      KPCuspCharts.Base F hF (D j).E (D j).integralUnits)
    intro j
    apply measurable_of_countable_open_cover (G j).atlas.baseOpen
      (G j).atlas.open_baseOpen (G j).atlas.cover
    intro i
    let b : (G j).atlas.baseOpen i → KPCuspCharts.Shape F :=
      fun q => ((G j).atlas.baseChart i).symm q |>.val
    have hb : Continuous b :=
      continuous_subtype_val.comp ((G j).atlas.baseChart i).symm.continuous
    have hbq (q : (G j).atlas.baseOpen i) :
        (QuotientAddGroup.mk (b q) : KPCuspCharts.Base F hF (D j).E
          (D j).integralUnits) = q.val := by
      rw [← (G j).atlas.baseChart_formula i (((G j).atlas.baseChart i).symm q)]
      simp
    let ψ : (G j).atlas.baseOpen i × KPCuspCharts.Torus F (D j).L → CrossSection A :=
      fun p => φ j (b p.1) p.2
    have hψ : Measurable ψ := by
      apply Continuous.measurable
      exact (continuous_sigmaMk (σ := fun k : CuspIndex A =>
        KPCuspCharts.CrossQuotient F (KPCuspArithmetic.conjugatedStabilizer F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
          ((A.cuspAtlas k.1).cusp k.2) ((A.cuspAtlas k.1).representative k.2)))
        (i := j)).comp ((G j).atlas.continuous_lift.comp
          (continuous_snd.prodMk (hb.comp continuous_fst)))
    have hlocal := measurable_measure_prodMk_left (ν := ν j) (hE.preimage hψ)
    convert hlocal using 1
    funext q
    change K ⟨j,q.val⟩ E = ν j ((fun z => ψ (q,z)) ⁻¹' E)
    rw [← hbq q, hformula, Measure.map_apply (hφ j (b q)) hE]

end DedekindZetaZeroFree.KPMsFixedHaar

end
end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ
abbrev X := KPSmoothLocalQuotientCharts.X F ζ hζ

def archBasepoint (g : KPSmoothActualFlowData.GInfinity F) :
    KPFiniteCuspAtlas.SymmetricSpace F := fun i =>
  KPArch.action (g (KPCusp.complexPlace F i)).out (0, 0)

structure SphericalTransport where
  projection : ∀ U : Level F ζ hζ, X F ζ hζ → Spherical F ζ hζ U
  continuous : ∀ U, Continuous (projection U)
  formula : ∀ U (g : KPSmoothActualFlowData.GInfinity F)
      (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
    projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c)) =
        Quotient.mk _ (archBasepoint F g, c)
  forget : ∀ (V U : Level F ζ hζ),
    V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup →
      Spherical F ζ hζ V → Spherical F ζ hζ U
  forget_formula : ∀ V U h x c,
    forget V U h (Quotient.mk _ (x,c)) = Quotient.mk _ (x,c)
  forget_continuous : ∀ V U h, Continuous (forget V U h)
  compatible : ∀ V U h x, forget V U h (projection V x) = projection U x

def sphericalMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ) :
    Measure (Spherical F ζ hζ U) := Measure.map (P.projection U) R.quotientHaar

private def fromRawTransport (P : KPMsFixedHaar.SphericalTransport F ζ hζ) :
    SphericalTransport F ζ hζ where
  projection := P.projection
  continuous := P.continuous
  formula := P.formula
  forget := P.forget
  forget_formula := P.forget_formula
  forget_continuous := P.forget_continuous
  compatible := P.compatible

 def toRawTransport (P : SphericalTransport F ζ hζ) :
    KPMsFixedHaar.SphericalTransport F ζ hζ where
  projection := P.projection
  continuous := P.continuous
  formula := P.formula
  forget := P.forget
  forget_formula := P.forget_formula
  forget_continuous := P.forget_continuous
  compatible := P.compatible

theorem actual_haar_normalization
    (μ : Measure (Cover F ζ hζ)) (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure ∧
      Nonempty (SphericalTransport F ζ hζ) := by
  obtain ⟨R, hR, hpos⟩ := KPMsFixedHaar.fixed_haar_recipe F ζ hζ μ hμ
  obtain ⟨P⟩ := KPMsFixedHaar.spherical_transport_exists F ζ hζ
  exact ⟨R, hR, hpos, ⟨fromRawTransport F ζ hζ P⟩⟩

abbrev Radius := {r : ℝ // 0 < r}

def positiveSlots (w : NumberField.InfinitePlace F) (r : Radius) :
    KPGlobalTorusFunctionData.TorusArch F := fun v =>
  if v = w then (Real.sqrt r.val : ℂ) else 1

def radialSection (w : NumberField.InfinitePlace F) (r : Radius) : Cover F ζ hζ :=
  KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (positiveSlots F w r)

structure RadialData where
  slot : NumberField.InfinitePlace F
  ell : Radius → KPGlobalTorusFunctionData.Ideles F
  continuous_ell : Continuous ell
  ell_one : ell ⟨1, by norm_num⟩ = 1
  ell_mul : ∀ r s : Radius,
    ell ⟨r.val * s.val, mul_pos r.property s.property⟩ = ell r * ell s
  ell_cube : ∀ r, ∃ u : KPGlobalTorusFunctionData.Ideles F, u ^ 3 = ell r
  ell_slots : ∀ r v,
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl v) (ell r : KPAdeles F) =
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ v)).symm (positiveSlots F slot r v)
  ell_finite : ∀ r q,
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr q) (ell r : KPAdeles F) = 1
  ell_norm : ∀ r, ((KPGlobalTorusFunctionData.ideleAbs F (ell r) : ℝ≥0) : ℝ) = r.val
  lift_ratio : ∀ r,
    KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (positiveSlots F slot r)) = ell r
  continuous_section : Continuous (radialSection F ζ hζ slot)
  section_one : radialSection F ζ hζ slot ⟨1, by norm_num⟩ = 1
  section_mul : ∀ r s : Radius,
    radialSection F ζ hζ slot ⟨r.val * s.val, mul_pos r.property s.property⟩ =
      radialSection F ζ hζ slot r * radialSection F ζ hζ slot s

def sectionShape (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) (r : Radius) : KPCuspCharts.Shape F :=
  ⟨fun i => (if KPCusp.complexPlace F i = w then Real.log r.val / 2 else 0) -
    Real.log r.val / (2 * (KPCuspLogShape.dimension F : ℝ)), by
    convert KPMsFixedHaar.single_slot_mean_zero F hF w (Real.log r.val / 2) using 1 <;>
      simp only [div_div, mul_comm]⟩

def radialMeasure : Measure ℝ :=
  volume.withDensity (fun r => ENNReal.ofReal (r ^ 2)⁻¹)

section Atlas
variable {F ζ hζ}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev CuspIndex := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount

abbrev Parabolic (j : CuspIndex A) := (A.cuspAtlas j.1).parabolic j.2
abbrev Geometry (j : CuspIndex A) := (A.cuspAtlas j.1).geometry j.2

abbrev Omega := Σ j : CuspIndex A,
  KPCuspCharts.Base F hF (Parabolic A j).E (Parabolic A j).integralUnits

abbrev CrossSection := Σ j : CuspIndex A,
  KPCuspCharts.CrossQuotient F
    (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))

instance : MeasurableSpace (Omega A) := borel _
instance : BorelSpace (Omega A) := ⟨rfl⟩
instance : MeasurableSpace (CrossSection A) := borel _
instance : BorelSpace (CrossSection A) := ⟨rfl⟩

def angularProjection (x : CrossSection A) : Omega A :=
  ⟨x.1, (Geometry A x.1).atlas.projection x.2⟩

def logHeight (r : ℝ) : ℝ := Real.log r / (2 * (KPCuspLogShape.dimension F : ℝ))

def AdmissibleCutoff (Y : ℝ) : Prop := 0 < Y ∧ A.threshold ≤ logHeight (F := F) Y

def cuspEnds (Y : ℝ) : Set (Spherical F ζ hζ U) :=
  ⋃ j : CuspIndex A,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y)

def probability (β : Measure (Omega A)) : Measure (Omega A) :=
  (β Set.univ)⁻¹ • β

structure Disintegration (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) where
  radial : RadialData F ζ hζ
  beta : Measure (Omega A)
  finite_beta : IsFiniteMeasure beta
  positive_beta : beta Set.univ ≠ 0
  probability_mass : IsProbabilityMeasure (probability A beta)
  unipotent : Omega A → Measure (CrossSection A)
  probability_unipotent : ∀ ω, IsProbabilityMeasure (unipotent ω)
  fiber_support : ∀ ω,
    unipotent ω {x | angularProjection A x = ω} = 1
  measurable_kernel : ∀ E, MeasurableSet E → Measurable (fun ω => unipotent ω E)

  fiber_formula : ∀ j (b : KPCuspCharts.Shape F),
    ∃ dn : Measure (KPCuspCharts.Torus F (Parabolic A j).L),
      dn.IsAddHaarMeasure ∧ IsProbabilityMeasure dn ∧
      unipotent ⟨j, QuotientAddGroup.mk b⟩ =
        Measure.map (fun z => (⟨j, (Geometry A j).atlas.lift (z,b)⟩ : CrossSection A)) dn

  componentWeight : Fin A.componentCount → ℝ≥0∞
  positive_componentWeight : ∀ i, 0 < componentWeight i
  finite_componentWeight : ∀ i, componentWeight i < ⊤
  component_measure : ∀ i,
    (sphericalMeasure F ζ hζ R P U).restrict
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
    componentWeight i • Measure.map
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        (A.cuspAtlas i).fundamentalDomain)
  induced_beta : ∀ E, MeasurableSet E →
    beta E = ∑ j : CuspIndex A,
      (componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (Geometry A j).sectionMeasure
        ((fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A)) ⁻¹' E)
  section_disintegration : ∀ f : CrossSection A → ℝ≥0∞, Measurable f →
    (∑ j : CuspIndex A,
      (componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
        ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂unipotent ω ∂beta
  modulus : Spherical F ζ hζ U → ℝ
  measurable_modulus : Measurable modulus
  chart : ∀ Y, AdmissibleCutoff A Y →
    CrossSection A × Set.Ioi Y → Spherical F ζ hζ U
  measurable_chart : ∀ Y hY, Measurable (chart Y hY)
  chart_range : ∀ Y hY, Set.range (chart Y hY) = cuspEnds A Y
  chart_embedding : ∀ Y hY, Topology.IsEmbedding (chart Y hY)
  chart_modulus : ∀ Y hY x r, modulus (chart Y hY (x,r)) = r.val

  chart_formula : ∀ Y hY j (p : KPCuspCharts.Cross F) (r : Set.Ioi Y),
    chart Y hY (⟨j, Quotient.mk _ p⟩,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) •
            KPCuspCharts.toArch F
              ((p.1, p.2 + sectionShape F hF radial.slot
                ⟨r.val, lt_trans hY.1 r.property⟩), logHeight (F := F) r.val)))

  cusp_integral : ∀ Y (hY : AdmissibleCutoff A Y)
      (φ : Spherical F ζ hζ U → ℝ≥0∞), Measurable φ →
    (∫⁻ x in cuspEnds A Y, φ x ∂sphericalMeasure F ζ hζ R P U) =
      beta Set.univ *
        ∫⁻ r : Set.Ioi Y, ∫⁻ ω, ∫⁻ x,
          φ (chart Y hY (x,r)) ∂unipotent ω ∂probability A beta
          ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

  shell_coefficient : ∀ Y, AdmissibleCutoff A Y →
    beta Set.univ = ENNReal.ofReal (2 * Y) *
      sphericalMeasure F ζ hζ R P U
        (cuspEnds A Y ∩ {x | Y < modulus x ∧ modulus x ≤ 2 * Y})
  open_positive : (sphericalMeasure F ζ hζ R P U).IsOpenPosMeasure

def kappa (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : Disintegration A R P) : ℝ :=
  (D.beta Set.univ).toReal

theorem kappa_positive (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : Disintegration A R P) :
    0 < kappa A R P D := by
  rw [kappa, ENNReal.toReal_pos_iff]
  exact ⟨bot_lt_iff_ne_bot.mpr D.positive_beta, D.finite_beta.measure_univ_lt_top⟩

theorem kappa_shell (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : Disintegration A R P)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    kappa A R P D = 2 * Y *
      (sphericalMeasure F ζ hζ R P U
        (cuspEnds A Y ∩ {x | Y < D.modulus x ∧ D.modulus x ≤ 2 * Y})).toReal := by
  rw [kappa, D.shell_coefficient Y hY, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [hY.1])]

end Atlas

theorem finite_level_measure_compatibility
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) :
    Measure.map (P.forget V U h) (sphericalMeasure F ζ hζ R P V) =
      sphericalMeasure F ζ hζ R P U := by
  letI : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  rw [sphericalMeasure, sphericalMeasure,
    Measure.map_map (P.forget_continuous V U h).measurable (P.continuous V).measurable,
    show (P.forget V U h) ∘ P.projection V = P.projection U from
      funext (P.compatible V U h)]

structure LevelCompatibility
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : Disintegration AV R P) (DU : Disintegration AU R P) where
  cuspForget : CuspIndex AV → CuspIndex AU
  radiusScale : CuspIndex AV → Radius
  angularForget : Omega AV → Omega AU
  measurable_angularForget : Measurable angularForget
  angular_label : ∀ ω, (angularForget ω).1 = cuspForget ω.1
  crossForget : CrossSection AV → CrossSection AU
  measurable_crossForget : Measurable crossForget
  cross_label : ∀ x, (crossForget x).1 = cuspForget x.1
  projection_commutes : ∀ x,
    angularProjection AU (crossForget x) = angularForget (angularProjection AV x)
  induced_angular : Measure.map angularForget
      (DV.beta.withDensity (fun ω => ENNReal.ofReal (radiusScale ω.1).val)) = DU.beta
  induced_probability : Measure.map angularForget
      (probability AV (DV.beta.withDensity
        (fun ω => ENNReal.ofReal (radiusScale ω.1).val))) = probability AU DU.beta
  coefficient : kappa AU R P DU =
    ((DV.beta.withDensity (fun ω => ENNReal.ofReal (radiusScale ω.1).val)) Set.univ).toReal
  common_slot : DV.radial.slot = DU.radial.slot
  chart_commutes : ∀ YV YU (hV : AdmissibleCutoff AV YV) (hU : AdmissibleCutoff AU YU)
      (x : CrossSection AV) (r : Set.Ioi YV)
      (hr : YU < (radiusScale x.1).val * r.val),
    P.forget V U h (DV.chart YV hV (x,r)) =
      DU.chart YU hU (crossForget x, ⟨(radiusScale x.1).val * r.val,hr⟩)
  induced_kernel : ∀ f : CrossSection AU → ℝ≥0∞, Measurable f →
    (∫⁻ ω, ENNReal.ofReal (radiusScale ω.1).val *
      ∫⁻ x, f (crossForget x) ∂DV.unipotent ω ∂DV.beta) =
      ∫⁻ ω, ∫⁻ x, f x ∂DU.unipotent ω ∂DU.beta

structure AllLevels (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) where
  totallyComplex : NumberField.InfinitePlace.nrRealPlaces F = 0
  atlas : ∀ U : Level F ζ hζ, KPFiniteCuspAtlas.Atlas F ζ hζ totallyComplex U
  disintegration : ∀ U, Disintegration (atlas U) R P
  compatible : ∀ V U h, Nonempty
    (LevelCompatibility F ζ hζ R P h (atlas V) (atlas U)
      (disintegration V) (disintegration U))

def fromRawRadial (D : KPMsFixedHaar.RadialData F ζ hζ) :
    RadialData F ζ hζ where
  slot := D.slot
  ell := D.ell
  continuous_ell := D.continuous_ell
  ell_one := D.ell_one
  ell_mul := D.ell_mul
  ell_cube := D.ell_cube
  ell_slots := D.ell_slots
  ell_finite := D.ell_finite
  ell_norm := D.ell_norm
  lift_ratio := D.lift_ratio
  continuous_section := D.continuous_section
  section_one := D.section_one
  section_mul := D.section_mul

 def fromRawDisintegration
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (D : KPMsFixedHaar.GeometricDisintegration A R (toRawTransport F ζ hζ P)) :
    Disintegration A R P where
  radial := fromRawRadial F ζ hζ D.radial
  beta := D.beta
  finite_beta := D.finite_beta
  positive_beta := D.positive_beta
  probability_mass := D.probability_mass
  unipotent := D.unipotent
  probability_unipotent := D.probability_unipotent
  fiber_support := D.fiber_support
  measurable_kernel := D.measurable_kernel
  fiber_formula := D.fiber_formula
  componentWeight := D.componentWeight
  positive_componentWeight := D.positive_componentWeight
  finite_componentWeight := D.finite_componentWeight
  component_measure := D.component_measure
  induced_beta := D.induced_beta
  section_disintegration := D.section_disintegration
  modulus := D.modulus
  measurable_modulus := D.measurable_modulus
  chart := D.chart
  measurable_chart := D.measurable_chart
  chart_range := D.chart_range
  chart_embedding := D.chart_embedding
  chart_modulus := D.chart_modulus
  chart_formula := D.chart_formula
  cusp_integral := (KPMsFixedHaar.fixed_haar_radial_integration A R
    (toRawTransport F ζ hζ P) D).cusp_integral
  shell_coefficient := (KPMsFixedHaar.fixed_haar_radial_integration A R
    (toRawTransport F ζ hζ P) D).shell_coefficient
  open_positive := (KPMsFixedHaar.fixed_haar_radial_integration A R
    (toRawTransport F ζ hζ P) D).open_positive

 def fromRawCompatibility
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : KPMsFixedHaar.GeometricDisintegration AV R (toRawTransport F ζ hζ P))
    (DU : KPMsFixedHaar.GeometricDisintegration AU R (toRawTransport F ζ hζ P))
    (C : KPMsFixedHaar.LevelCompatibility F ζ hζ R (toRawTransport F ζ hζ P)
      h AV AU DV DU) :
    LevelCompatibility F ζ hζ R P h AV AU
      (fromRawDisintegration F ζ hζ AV R P DV)
      (fromRawDisintegration F ζ hζ AU R P DU) where
  cuspForget := C.cuspForget
  radiusScale := C.radiusScale
  angular_label := C.angular_label
  cross_label := C.cross_label
  angularForget := C.angularForget
  measurable_angularForget := C.measurable_angularForget
  crossForget := C.crossForget
  measurable_crossForget := C.measurable_crossForget
  projection_commutes := C.projection_commutes
  induced_angular := C.induced_angular
  induced_probability := C.induced_probability
  coefficient := C.coefficient
  common_slot := C.common_slot
  chart_commutes := C.chart_commutes
  induced_kernel := C.induced_kernel

theorem disintegration_at_fixed_haar
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) : Nonempty (AllLevels F ζ hζ R P) := by
  let kernels := fun hF U (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) =>
    (KPMsFixedHaar.probability_fiber_kernel A).some
  obtain ⟨D, _⟩ := KPMsFixedHaar.coherent_cusp_geometry F ζ hζ R
    (toRawTransport F ζ hζ P) kernels
  refine ⟨{
    totallyComplex := D.totallyComplex
    atlas := D.atlas
    disintegration := fun U => fromRawDisintegration F ζ hζ (D.atlas U) R P
      (D.disintegration U)
    compatible := ?_ }⟩
  intro V U h
  obtain ⟨C⟩ := D.compatible V U h
  exact ⟨fromRawCompatibility F ζ hζ R P h (D.atlas V) (D.atlas U)
    (D.disintegration V) (D.disintegration U) C⟩

end KPMsFixedHaarDisintegration

theorem kp_ms_fixed_haar_disintegration
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μ : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure ∧
      ∃ P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ,
        Nonempty (KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) := by
  obtain ⟨R, hR, hpos, ⟨P⟩⟩ :=
    KPMsFixedHaarDisintegration.actual_haar_normalization F ζ hζ μ hμ
  exact ⟨R, hR, hpos, P,
    KPMsFixedHaarDisintegration.disintegration_at_fixed_haar F ζ hζ R P⟩

end DedekindZetaZeroFree

end
end
