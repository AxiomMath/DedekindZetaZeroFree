module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspRadialIntegrationAndShellVolumes
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicComponents.ProductDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArithmeticComponents.HyperbolicQuotientVolume
public import DedekindZetaZeroFree.Geometry.Cusps.FundamentalDomains.ExactRectangles
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.RadialProductPresentation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsFixedHaar

theorem spherical_measure_forget
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) :
    MeasureTheory.Measure.map (P.forget V U h) (sphericalMeasure F ζ hζ R P V) =
      sphericalMeasure F ζ hζ R P U := by
  unfold sphericalMeasure
  rw [MeasureTheory.Measure.map_map
    (P.forget_continuous V U h).measurable (P.continuous V).measurable]
  have he : P.forget V U h ∘ P.projection V = P.projection U := by
    funext x
    exact P.compatible V U h x
  rw [he]

section AngularMarginal
open MeasureTheory
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem angular_measurable : Measurable (angularProjection A) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro j
  exact continuous_sigmaMk.comp (Geometry A j).atlas.continuous_projection

private theorem kernel_angular_map (K : FiberKernel A) (ω : Omega A) :
    Measure.map (angularProjection A) (K.unipotent ω) = Measure.dirac ω := by
  rcases ω with ⟨j, b⟩
  induction b using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨dn, hdn, hprob, hformula⟩ := K.fiber_formula j b
    letI := hprob
    haveI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
      (Geometry A j).lattice.choose
    haveI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
        Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
    let lift := fun z : KPCuspCharts.Torus F (Parabolic A j).L =>
      (⟨j, (Geometry A j).atlas.lift (z,b)⟩ : CrossSection A)
    have hlift : Measurable lift := by
      apply Continuous.measurable
      exact continuous_sigmaMk.comp ((Geometry A j).atlas.continuous_lift.comp
        (continuous_id.prodMk continuous_const))
    have hconstant : angularProjection A ∘ lift = fun _ =>
        (⟨j, QuotientAddGroup.mk b⟩ : Omega A) := by
      funext z
      induction z using QuotientAddGroup.induction_on with
      | H x =>
        dsimp [lift, angularProjection]
        rw [(Geometry A j).atlas.lift_formula, (Geometry A j).atlas.projection_formula]
    rw [hformula, Measure.map_map (angular_measurable A) hlift, hconstant,
      Measure.map_const, measure_univ, one_smul]

 theorem kernel_angular_lintegral (K : FiberKernel A) (ω : Omega A)
    (f : Omega A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (angularProjection A x) ∂K.unipotent ω) = f ω := by
  rw [← lintegral_map hf (angular_measurable A), kernel_angular_map A K ω,
    lintegral_dirac' _ hf]

 theorem cross_section_inclusion_measurable (j : CuspIndex A) :
    Measurable (fun x => (⟨j,x⟩ : CrossSection A)) := by
  apply measurable_from_quotient.mpr
  have hmk : Continuous (fun p : KPCuspCharts.Cross F =>
      (⟨j, Quotient.mk _ p⟩ : CrossSection A)) :=
    continuous_sigmaMk.comp continuous_quotient_mk'
  exact hmk.measurable

 def weighted_section_measure (w : Fin A.componentCount → ℝ≥0∞) :
    Measure (CrossSection A) :=
  ∑ j : CuspIndex A,
    (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) •
      Measure.map (fun x => (⟨j, x⟩ : CrossSection A)) (Geometry A j).sectionMeasure

 theorem angular_marginal_of_disintegration (K : FiberKernel A)
    (w : Fin A.componentCount → ℝ≥0∞) (β : Measure (Omega A))
    (h : ∀ f : CrossSection A → ℝ≥0∞, Measurable f →
      (∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
        ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω ∂β) :
    Measure.map (angularProjection A) (weighted_section_measure A w) = β := by
  apply Measure.ext
  intro E hE
  let f : Omega A → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hid := h (fun x => f (angularProjection A x)) (hf.comp (angular_measurable A))
  simp_rw [kernel_angular_lintegral A K _ f hf] at hid
  have he : (∫⁻ x, f (angularProjection A x) ∂weighted_section_measure A w) =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          ∫⁻ x, f (angularProjection A ⟨j,x⟩) ∂(Geometry A j).sectionMeasure := by
    simp only [weighted_section_measure, lintegral_finsetSum_measure, lintegral_smul_measure]
    apply Finset.sum_congr rfl
    intro j _
    have hm := cross_section_inclusion_measurable A j
    have hmf : Measurable (fun x => f (angularProjection A x)) :=
      hf.comp (angular_measurable A)
    rw [lintegral_map hmf hm]
    rfl
  calc
    _ = ∫⁻ x, f x ∂Measure.map (angularProjection A) (weighted_section_measure A w) :=
      (lintegral_indicator_one hE).symm
    _ = ∫⁻ x, f (angularProjection A x) ∂weighted_section_measure A w :=
      lintegral_map hf (angular_measurable A)
    _ = ∫⁻ ω, f ω ∂β := he.trans hid
    _ = β E := lintegral_indicator_one hE

 def weighted_angular_measure (w : Fin A.componentCount → ℝ≥0∞) :
    Measure (Omega A) :=
  Measure.map (angularProjection A) (weighted_section_measure A w)

private theorem weighted_section_mass (w : Fin A.componentCount → ℝ≥0∞) :
    weighted_section_measure A w Set.univ =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          (Geometry A j).sectionMeasure Set.univ := by
  simp only [weighted_section_measure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (cross_section_inclusion_measurable A j) MeasurableSet.univ,
    Set.preimage_univ]

private theorem weighted_angular_apply (w : Fin A.componentCount → ℝ≥0∞)
    (E : Set (Omega A)) (hE : MeasurableSet E) :
    weighted_angular_measure A w E =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          (Geometry A j).sectionMeasure
            ((fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A)) ⁻¹' E) := by
  rw [weighted_angular_measure, Measure.map_apply (angular_measurable A) hE]
  simp only [weighted_section_measure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (cross_section_inclusion_measurable A j)
    ((angular_measurable A) hE)]
  rfl

 theorem weighted_section_finite (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, w i < ⊤) : IsFiniteMeasure (weighted_section_measure A w) := by
  constructor
  rw [weighted_section_mass A w]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  apply ENNReal.mul_lt_top
  · apply ENNReal.div_lt_top (ne_of_lt (hw j.1))
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))
  · exact (Geometry A j).finite_sectionMeasure.measure_univ_lt_top

private theorem weighted_section_positive (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, 0 < w i) : weighted_section_measure A w Set.univ ≠ 0 := by
  apply ne_of_gt
  rw [weighted_section_mass A w]
  apply Finset.sum_pos_iff.mpr
  let i : Fin A.componentCount := ⟨0, A.positive_componentCount⟩
  let a : Fin (A.cuspAtlas i).cuspCount := ⟨0, (A.cuspAtlas i).positive_cuspCount⟩
  refine ⟨⟨i,a⟩, Finset.mem_univ _, ?_⟩
  apply ENNReal.mul_pos
  · exact ENNReal.div_ne_zero.mpr ⟨ne_of_gt (hw i), ENNReal.ofReal_ne_top⟩
  · exact (Geometry A ⟨i,a⟩).positive_sectionMeasure

private theorem weighted_angular_finite (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, w i < ⊤) : IsFiniteMeasure (weighted_angular_measure A w) := by
  letI := weighted_section_finite A w hw
  unfold weighted_angular_measure
  infer_instance

private theorem weighted_angular_positive (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, 0 < w i) : weighted_angular_measure A w Set.univ ≠ 0 := by
  rw [weighted_angular_measure, Measure.map_apply (angular_measurable A) MeasurableSet.univ,
    Set.preimage_univ]
  exact weighted_section_positive A w hw

private theorem weighted_angular_probability (w : Fin A.componentCount → ℝ≥0∞)
    (hpos : ∀ i, 0 < w i) (hfin : ∀ i, w i < ⊤) :
    IsProbabilityMeasure (probability A (weighted_angular_measure A w)) := by
  constructor
  simp only [probability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (weighted_angular_positive A w hpos)
    (weighted_angular_finite A w hfin).measure_univ_lt_top.ne

end AngularMarginal

 theorem probability_map
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (βV : MeasureTheory.Measure (Omega AV)) (βU : MeasureTheory.Measure (Omega AU))
    (f : Omega AV → Omega AU) (hf : Measurable f)
    (hβ : MeasureTheory.Measure.map f βV = βU) :
    MeasureTheory.Measure.map f (probability AV βV) = probability AU βU := by
  have hmass : βV Set.univ = βU Set.univ := by
    rw [← hβ, MeasureTheory.Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  simp only [probability]
  rw [MeasureTheory.Measure.map_smul _ hf.aemeasurable, hmass, hβ]

section FiniteIsotropyMeasureComparison
open MeasureTheory Set
open scoped ENNReal Pointwise

private theorem lintegral_constant_orbit_multiplicity
    {H X : Type*} [Group H] [Countable H] [MeasurableSpace X]
    [MulAction H X] [MeasurableConstSMul H X]
    (ν : Measure X) [SMulInvariantMeasure H X ν]
    {s t : Set X} (hs : IsFundamentalDomain H s ν)
    (ht : MeasurableSet t) (c : ℝ≥0∞)
    (hcount : ∀ᵐ x ∂ν.restrict s,
      (∑' g : H, (g • t).indicator (fun _ => (1 : ℝ≥0∞)) x) = c)
    (f : X → ℝ≥0∞) (hinv : ∀ (g : H) (x : X), f (g • x) = f x) :
    (∫⁻ x in t, f x ∂ν) = c * ∫⁻ x in s, f x ∂ν := by
  have hm : (Measure.sum fun g : H => ν.restrict (g • t ∩ s)) =
      c • ν.restrict s :=
    KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.OrbitMultiplicity.sum_restrict_of_constant_multiplicity
      ν s (fun g : H => g • t) (fun g => ht.const_smul g) c hcount
  calc
    (∫⁻ x in t, f x ∂ν) = ∑' g : H, ∫⁻ x in g • t ∩ s, f x ∂ν := by
      rw [hs.setLIntegral_eq_tsum']
      simp only [hinv]
    _ = ∫⁻ x, f x ∂(Measure.sum fun g : H => ν.restrict (g • t ∩ s)) := by
      rw [lintegral_sum_measure]
    _ = c * ∫⁻ x in s, f x ∂ν := by rw [hm, lintegral_smul_measure, smul_eq_mul]

private theorem rectangle_section_measure
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (hB : ∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
      b + v.val ∈ B) :
    Measure.map (Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) =
      (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) •
        G.sectionMeasure := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun s => (G.crossAction s).continuous.measurable⟩
  letI := G.haar_shapeMeasure
  letI := G.finite_isotropy
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) :=
    ⟨fun s E hE => by
      have hm := congrArg (fun ν : Measure (KPCuspCharts.Cross F) => ν E) (G.measure_invariant s)
      rw [Measure.map_apply (G.crossAction s).continuous.measurable hE] at hm
      exact hm⟩
  have hmk : ∀ (s : S) (x : KPCuspCharts.Cross F),
      Quotient.mk (KPCuspCharts.crossRelation F S) (G.crossAction s x) =
        Quotient.mk (KPCuspCharts.crossRelation F S) x := by
    intro s x
    apply Quotient.sound
    change MulAction.orbitRel S _
      (KPCuspCharts.toArch F (G.crossAction s x, 0)) (KPCuspCharts.toArch F (x, 0))
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨s, ?_⟩
    obtain ⟨M, hM, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (x, 0)) = _
    rw [G.actual_action s M hM hc, G.crossAction_formula s M hM hc]
    rfl
  have hc : (ENat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) =
      (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) := by
    simp [ENat.card_eq_coe_natCard]
  apply Measure.ext
  intro E hE
  let f : KPCuspCharts.CrossQuotient F S → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have heq := lintegral_constant_orbit_multiplicity (volume.prod G.shapeMeasure)
    G.isFundamentalDomain (hAm.prod hBm)
    (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞)
    (Filter.Eventually.of_forall fun x =>
      (KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.rectangle_orbit_multiplicity
        G A hA B hB x).trans hc)
    (fun x => f (Quotient.mk (KPCuspCharts.crossRelation F S) x))
    (fun s x => congrArg f (hmk s x))
  rw [G.sectionMeasure_formula, Measure.smul_apply, smul_eq_mul]
  rw [← lintegral_map hf measurable_quotient_mk'',
    ← lintegral_map hf measurable_quotient_mk''] at heq
  simpa only [f, lintegral_indicator_const hE, one_mul] using heq

private theorem horizontal_domain_map
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {L : AddSubgroup X} [Countable L] [T2Space (X ⧸ L)]
    [SecondCountableTopology (X ⧸ L)]
    (ν : Measure X) [ν.IsAddHaarMeasure] [ν.IsAddRightInvariant] [SigmaFinite ν]
    (μ : Measure (X ⧸ L)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {A : Set X} (hA : IsAddFundamentalDomain L.op A ν) (hAfin : ν A ≠ ⊤) :
    Measure.map QuotientAddGroup.mk (ν.restrict A) = ν A • μ := by
  let μ' : Measure (X ⧸ L) := ν A • μ
  letI : Measure.IsAddLeftInvariant μ' := inferInstanceAs (Measure.IsAddLeftInvariant (ν A • μ))
  letI : IsFiniteMeasure μ' := ⟨by simp [μ', hAfin.lt_top]⟩
  letI : HasAddFundamentalDomain L.op X ν := hA.hasAddFundamentalDomain ν
  letI : AddQuotientMeasureEqMeasurePreimage ν μ' :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage ν (by
      rw [hA.covolume_eq_volume ν]
      simp [μ'])
  exact (measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage ν hA μ').map_eq

private theorem rectangle_torus_measure
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (q : KPCuspCharts.CrossQuotient F S → Y) (hq : Continuous q)
    (dn : Measure (KPCuspCharts.Torus F D.L)) (hdn : dn.IsAddHaarMeasure)
    (hprob : IsProbabilityMeasure dn)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A) :
    Measure.map (q ∘ Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) =
    (volume A) • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) := by
  letI := hdn
  letI := hprob
  obtain ⟨hd, _⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  letI : IsClosed (KPCuspCharts.translationLattice F D.L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  letI : Countable (KPCuspCharts.translationLattice F D.L) :=
    countable_of_Lindelof_of_discrete
  letI := G.haar_shapeMeasure
  have hinj : Function.Injective (KPCuspCharts.embedding F) := by
    intro a c hac
    have h0 := congrFun hac ⟨0, G.positive_dimension⟩
    exact (KPCusp.complexPlace F ⟨0, G.positive_dimension⟩).embedding.injective h0
  have htiling : ∀ y : KPCuspCharts.Horizontal F,
      ∃! l : (KPCuspCharts.translationLattice F D.L).op, l +ᵥ y ∈ A := by
    intro y
    obtain ⟨a, ha, hau⟩ := hA y
    let l : KPCuspCharts.translationLattice F D.L :=
      ⟨KPCuspCharts.embedding F a.val, ⟨a.val, a.property, rfl⟩⟩
    refine ⟨⟨AddOpposite.op l.val, l.property⟩, ha, ?_⟩
    intro k hk
    obtain ⟨c, hc, hec⟩ := k.property
    have hkc : y + KPCuspCharts.embedding F c ∈ A := by
      change y + k.val.unop ∈ A at hk
      rwa [← hec] at hk
    have he := hau ⟨c, hc⟩ hkc
    apply Subtype.ext
    apply AddOpposite.unop_injective
    exact hec.symm.trans (congrArg (fun x : D.L => KPCuspCharts.embedding F x.val) he)
  have hfd : IsAddFundamentalDomain (KPCuspCharts.translationLattice F D.L).op A volume :=
    IsAddFundamentalDomain.mk' hAm.nullMeasurableSet htiling
  have hm := horizontal_domain_map volume dn hfd hAb.measure_lt_top.ne
  have hcomp : (q ∘ G.atlas.lift) ∘ Prod.map QuotientAddGroup.mk id =
      q ∘ Quotient.mk (KPCuspCharts.crossRelation F S) := by
    funext p
    exact congrArg q (G.atlas.lift_formula p.1 p.2)
  rw [← Measure.prod_restrict]
  calc
    _ = Measure.map (q ∘ G.atlas.lift) ((Measure.map QuotientAddGroup.mk (volume.restrict A)).prod
        (G.shapeMeasure.restrict B)) := by
      have hp : (Measure.map (QuotientAddGroup.mk : KPCuspCharts.Horizontal F → KPCuspCharts.Torus F D.L) (volume.restrict A)).prod
          (G.shapeMeasure.restrict B) = Measure.map (Prod.map QuotientAddGroup.mk id)
          ((volume.restrict A).prod (G.shapeMeasure.restrict B)) := by
        simpa only [Measure.map_id] using Measure.map_prod_map (volume.restrict A)
          (G.shapeMeasure.restrict B) QuotientAddGroup.continuous_mk.measurable measurable_id
      rw [hp, Measure.map_map (hq.comp G.atlas.continuous_lift).measurable
        (QuotientAddGroup.continuous_mk.measurable.prodMap measurable_id), hcomp]
    _ = _ := by
      rw [hm, Measure.prod_smul_left]
      exact Measure.map_smul (volume A) (hq.comp G.atlas.continuous_lift).measurable.aemeasurable

private theorem section_torus_representation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (q : KPCuspCharts.CrossQuotient F S → Y) (hq : Continuous q) (hqm : Measurable q)
    (dn : Measure (KPCuspCharts.Torus F D.L)) (hdn : dn.IsAddHaarMeasure)
    (hprob : IsProbabilityMeasure dn) :
    ∃ B : Set (KPCuspCharts.Shape F), ∃ c : ℝ≥0∞,
      MeasurableSet B ∧ Bornology.IsBounded B ∧ c < ⊤ ∧
      Measure.map q G.sectionMeasure =
        c • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) := by
  obtain ⟨A, B, hAm, hAb, hBm, hBb, hA, hB⟩ :=
    KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.actual_exact_comparison_rectangle G
  let m : ℝ≥0∞ := Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits)
  letI := G.finite_isotropy
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Nat.card_pos (α := KPCuspCharts.kernelUnits F hF D.E D.integralUnits)).ne'
  have hmfin : m ≠ ⊤ := ENNReal.natCast_ne_top _
  have he := congrArg (Measure.map q) (rectangle_section_measure G A B hAm hBm hA hB)
  rw [Measure.map_map hqm measurable_quotient_mk'',
    Measure.map_smul _ hqm.aemeasurable] at he
  rw [rectangle_torus_measure G q hq dn hdn hprob A B hAm hAb hA] at he
  change (volume A) • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) =
    m • Measure.map q G.sectionMeasure at he
  refine ⟨B, m⁻¹ * volume A, hBm, hBb, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hm0).lt_top hAb.measure_lt_top
  · have he' := congrArg (fun μ : Measure Y => m⁻¹ • μ) he
    simpa only [smul_smul, ENNReal.inv_mul_cancel hm0 hmfin, one_smul] using he'.symm

section LocalSection
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem kernel_lintegral_measurable (K : FiberKernel A)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ x, f x ∂K.unipotent ω) := by
  exact (Measure.measurable_lintegral hf).comp
    (Measure.measurable_of_measurable_coe K.unipotent K.measurable_kernel)

private theorem local_section_disintegration (K : FiberKernel A) (j : CuspIndex A)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω
        ∂Measure.map (fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A))
          (Geometry A j).sectionMeasure := by
  obtain ⟨dn, hdn, hprob, _⟩ := K.fiber_formula j 0
  letI := hdn
  letI := hprob
  letI := (Geometry A j).haar_shapeMeasure
  letI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
    (Geometry A j).lattice.choose
  letI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
      Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
  obtain ⟨B, c, hBm, hBb, hc, hrep⟩ := section_torus_representation (Geometry A j)
    (fun x => (⟨j,x⟩ : CrossSection A)) continuous_sigmaMk
    (cross_section_inclusion_measurable A j) dn hdn hprob
  let lift := fun p : KPCuspCharts.Torus F (Parabolic A j).L × KPCuspCharts.Shape F =>
    (⟨j, (Geometry A j).atlas.lift p⟩ : CrossSection A)
  change Measure.map (fun x => (⟨j,x⟩ : CrossSection A)) (Geometry A j).sectionMeasure =
    c • Measure.map lift (dn.prod ((Geometry A j).shapeMeasure.restrict B)) at hrep
  have hliftc : Continuous lift :=
    (continuous_sigmaMk (σ := fun j : CuspIndex A => KPCuspCharts.CrossQuotient F
        (KPCuspArithmetic.conjugatedStabilizer F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))) (i := j)).comp
      (Geometry A j).atlas.continuous_lift
  have hlift : Measurable lift := hliftc.measurable
  have hbase : angularProjection A ∘ lift =
      fun p => (⟨j, QuotientAddGroup.mk p.2⟩ : Omega A) := by
    funext p
    obtain ⟨z,b⟩ := p
    induction z using QuotientAddGroup.induction_on with
    | H z =>
      dsimp [lift, angularProjection]
      rw [(Geometry A j).atlas.lift_formula, (Geometry A j).atlas.projection_formula]
  have hformula (b : KPCuspCharts.Shape F) :
      K.unipotent ⟨j, QuotientAddGroup.mk b⟩ =
        Measure.map (fun z => lift (z,b)) dn := by
    obtain ⟨ν, hν, hpν, heν⟩ := K.fiber_formula j b
    letI := hν
    letI := hpν
    letI := (Geometry A j).compact_torus
    letI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
      (Geometry A j).lattice.choose
    letI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
        Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
    have he : ν = dn := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure ν dn
    simpa only [he] using heν
  have hinc := cross_section_inclusion_measurable A j
  have hang := angular_measurable A
  have hmarg : Measure.map
      (fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A))
      (Geometry A j).sectionMeasure =
      c • Measure.map (angularProjection A ∘ lift)
        (dn.prod ((Geometry A j).shapeMeasure.restrict B)) := by
    have he := congrArg (Measure.map (angularProjection A)) hrep
    rw [Measure.map_map hang hinc, Measure.map_smul _ hang.aemeasurable,
      Measure.map_map hang hlift] at he
    exact he
  rw [← lintegral_map hf hinc, hrep, lintegral_smul_measure,
    lintegral_map hf hlift, lintegral_prod_symm' (fun p => f (lift p)) (hf.comp hlift),
    hmarg, lintegral_smul_measure,
    lintegral_map (kernel_lintegral_measurable A K f hf) (hang.comp hlift)]
  simp only [smul_eq_mul]
  congr 1
  rw [lintegral_prod_symm' (fun p => ∫⁻ x, f x ∂K.unipotent ((angularProjection A ∘ lift) p))
    ((kernel_lintegral_measurable A K f hf).comp (hang.comp hlift))]
  change (∫⁻ b in B, ∫⁻ z, f (lift (z,b)) ∂dn ∂(Geometry A j).shapeMeasure) =
    ∫⁻ b in B, ∫⁻ z, ∫⁻ x, f x ∂K.unipotent ((angularProjection A ∘ lift) (z,b))
      ∂dn ∂(Geometry A j).shapeMeasure
  rw [hbase]
  apply lintegral_congr
  intro b
  dsimp only
  have hlb : Measurable (fun z => lift (z,b)) := hlift.comp (measurable_id.prodMk measurable_const)
  rw [hformula, lintegral_map hf hlb]
  simp only [lintegral_const, measure_univ, mul_one]

private theorem weighted_section_disintegration (K : FiberKernel A)
    (w : Fin A.componentCount → ℝ≥0∞)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    (∑ j : CuspIndex A,
      (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
        ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω ∂weighted_angular_measure A w := by
  rw [weighted_angular_measure, weighted_section_measure,
    Measure.map_finset_sum' (angular_measurable A).aemeasurable]
  simp only [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul _ (angular_measurable A).aemeasurable,
    Measure.map_map (angular_measurable A) (cross_section_inclusion_measurable A j),
    lintegral_smul_measure]
  exact congrArg (fun t => (w j.1 / ENNReal.ofReal
    (2 * (KPCuspLogShape.dimension F : ℝ))) * t)
    (local_section_disintegration A K j f hf)

end LocalSection

end FiniteIsotropyMeasureComparison

namespace PinnedRadialCharts

 theorem actual_coordinate_relation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (p q : KPCuspCharts.Coordinates F) :
    KPCuspCharts.totalRelation F S p q ↔
      ∃ g : S, (G.crossAction g q.1, q.2) = p := by
  change (∃ g : S, g • KPCuspCharts.toArch F q = KPCuspCharts.toArch F p) ↔ _
  have ha (g : S) (q : KPCuspCharts.Coordinates F) :
      g • KPCuspCharts.toArch F q = KPCuspCharts.toArch F (G.crossAction g q.1, q.2) := by
    obtain ⟨M, hM, hc⟩ := D.upper g.val g.property
    change KPCuspSiegel.action F g.val _ = _
    rw [G.actual_action g M hM hc, G.crossAction_formula g M hM hc]
    rfl
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective
      ((ha g q).symm.trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (ha g q).trans (congrArg (KPCuspCharts.toArch F) hg)⟩

 def coordinate_shear
    {F : Type} [Field F] [NumberField F]
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) :
    KPCuspCharts.Coordinates F ≃ₜ KPCuspCharts.Coordinates F where
  toFun p := ((p.1.1, p.1.2 + a p.2), p.2)
  invFun p := ((p.1.1, p.1.2 - a p.2), p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.fst.prodMk
    (continuous_fst.snd.add (ha.comp continuous_snd))).prodMk continuous_snd
  continuous_invFun := (continuous_fst.fst.prodMk
    (continuous_fst.snd.sub (ha.comp continuous_snd))).prodMk continuous_snd

 theorem coordinate_shear_relation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a)
    (p q : KPCuspCharts.Coordinates F) :
    KPCuspCharts.totalRelation F S (coordinate_shear a ha p) (coordinate_shear a ha q) ↔
      KPCuspCharts.totalRelation F S p q := by
  rw [actual_coordinate_relation G, actual_coordinate_relation G]
  have hc (g : S) (p : KPCuspCharts.Cross F) (b : KPCuspCharts.Shape F) :
      G.crossAction g (p.1, p.2 + b) = ((G.crossAction g p).1, (G.crossAction g p).2 + b) := by
    obtain ⟨M, hM, hM0⟩ := D.upper g.val g.property
    rw [G.crossAction_formula g M hM hM0, G.crossAction_formula g M hM hM0]
    dsimp [KPCuspCharts.crossAffine, KPCuspCharts.affine]
    congr 1
    abel
  change (∃ g : S, (G.crossAction g (q.1.1, q.1.2 + a q.2), q.2) =
    coordinate_shear a ha p) ↔ _
  have he (g : S) : (G.crossAction g (q.1.1, q.1.2 + a q.2), q.2) =
      coordinate_shear a ha (G.crossAction g q.1, q.2) := by
    rw [hc]
    rfl
  simp only [he, (coordinate_shear a ha).injective.eq_iff]

 def actual_shape_translation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F) :
    KPCuspCharts.CrossQuotient F S ≃ₜ KPCuspCharts.CrossQuotient F S :=
  Homeomorph.Quotient.congr
    (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.addRight b))
    (fun p q => by
      change KPCuspCharts.totalRelation F S (p,0) (q,0) ↔
        KPCuspCharts.totalRelation F S ((p.1,p.2+b),0) ((q.1,q.2+b),0)
      exact (coordinate_shear_relation G (fun _ => b) continuous_const (p,0) (q,0)).symm)

 theorem actual_shape_translation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F)
    (p : KPCuspCharts.Cross F) :
    actual_shape_translation G b (Quotient.mk _ p) =
      Quotient.mk _ (p.1,p.2+b) := rfl

 def sheared_high_presentation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) (T : ℝ) :
    KPCuspCharts.CrossQuotient F S × Set.Ioi T ≃ₜ KPCuspCharts.HighQuotient F S T :=
  (G.highPresentation T).trans (Homeomorph.Quotient.congr
    ((coordinate_shear a ha).subtype (fun _ => Iff.rfl))
    (fun p q => (coordinate_shear_relation G a ha p.val q.val).symm))

private theorem sheared_high_presentation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) (T : ℝ)
    (p : KPCuspCharts.Cross F) (t : Set.Ioi T) :
    sheared_high_presentation G a ha T (Quotient.mk _ p, t) =
      Quotient.mk _ (⟨((p.1, p.2 + a t.val), t.val), t.property⟩ :
        {p : KPCuspCharts.Coordinates F // T < p.2}) := by
  dsimp [sheared_high_presentation]
  rw [G.highPresentation_formula]
  rfl

 theorem sectionShape_continuous
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) : Continuous (sectionShape F hF w) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hl : Continuous (fun r : Radius => Real.log r.val) :=
    continuous_subtype_val.log (fun r => ne_of_gt r.property)
  by_cases hi : KPCusp.complexPlace F i = w
  · convert (hl.div_const 2).sub (hl.div_const
      (2 * (KPCuspLogShape.dimension F : ℝ))) using 1
    funext r
    simp [hi]
  · convert (continuous_const (y := (0 : ℝ))).sub (hl.div_const
      (2 * (KPCuspLogShape.dimension F : ℝ))) using 1
    funext r
    simp [hi]

 def radius_log_homeomorph
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) : Radius ≃ₜ ℝ where
  toFun r := logHeight (F := F) r.val
  invFun t := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩
  left_inv r := by
    apply Subtype.ext
    dsimp [logHeight]
    rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))), Real.exp_log r.property]
  right_inv t := by
    dsimp [logHeight]
    rw [Real.log_exp, mul_div_cancel_left₀ t (ne_of_gt (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))))]
  continuous_toFun := (continuous_subtype_val.log (fun r => ne_of_gt r.property)).div_const _
  continuous_invFun := (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).subtype_mk _

 def high_radius_log_homeomorph
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Y : ℝ) (hY : 0 < Y) : Set.Ioi Y ≃ₜ Set.Ioi (logHeight (F := F) Y) where
  toFun r := ⟨logHeight (F := F) r.val, by
    change Real.log Y / (2 * (KPCuspLogShape.dimension F : ℝ)) <
      Real.log r.val / (2 * (KPCuspLogShape.dimension F : ℝ))
    apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))).mpr
    exact Real.log_lt_log hY r.property⟩
  invFun t := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t.val), by
    change Y < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t.val)
    calc Y = Real.exp (Real.log Y) := (Real.exp_log hY).symm
         _ < _ := Real.exp_lt_exp.mpr (by
           have ht : Real.log Y < t.val * (2 * (KPCuspLogShape.dimension F : ℝ)) :=
             (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
               (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))).mp t.property
           simpa only [mul_comm] using ht)⟩
  left_inv r := by
    apply Subtype.ext
    have he := congrArg (fun r : Radius => r.val) ((radius_log_homeomorph F hF).left_inv
      ⟨r.val, lt_trans hY r.property⟩)
    exact he
  right_inv t := by
    apply Subtype.ext
    exact (radius_log_homeomorph F hF).right_inv t.val
  continuous_toFun := (((continuous_subtype_val.log (fun r =>
    ne_of_gt (lt_trans hY r.property))).div_const _)).subtype_mk _
  continuous_invFun := (Real.continuous_exp.comp
    (continuous_const.mul continuous_subtype_val)).subtype_mk _

 def pinned_radial_presentation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    KPCuspCharts.CrossQuotient F S × Set.Ioi Y ≃ₜ
      KPCuspCharts.HighQuotient F S (logHeight (F := F) Y) :=
  (Homeomorph.prodCongr (Homeomorph.refl _) (high_radius_log_homeomorph F hF Y hY)).trans
    (sheared_high_presentation G
      (sectionShape F hF w ∘ (radius_log_homeomorph F hF).symm)
      ((sectionShape_continuous F hF w).comp (radius_log_homeomorph F hF).symm.continuous)
      (logHeight (F := F) Y))

private theorem pinned_radial_presentation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_radial_presentation G w Y hY (Quotient.mk _ p, r) =
      Quotient.mk _ (⟨((p.1, p.2 + sectionShape F hF w
        ⟨r.val, lt_trans hY r.property⟩), logHeight (F := F) r.val),
          (high_radius_log_homeomorph F hF Y hY r).property⟩ :
        {p : KPCuspCharts.Coordinates F // logHeight (F := F) Y < p.2}) := by
  change sheared_high_presentation G _ _ _
    (Quotient.mk _ p, high_radius_log_homeomorph F hF Y hY r) = _
  rw [sheared_high_presentation_formula]
  congr 1
  apply Subtype.ext
  have he := (radius_log_homeomorph F hF).symm_apply_apply
    (⟨r.val, lt_trans hY r.property⟩ : Radius)
  change (radius_log_homeomorph F hF).symm (logHeight (F := F) r.val) = _ at he
  simp only [Function.comp_apply]
  rw [show (high_radius_log_homeomorph F hF Y hY r).val =
    logHeight (F := F) r.val from rfl, he]

section PinnedLocalEnd
open Topology
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 def high_inclusion (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :=
  ((Geometry A j).highPresentation A.threshold) ∘
    Prod.map id (Set.inclusion (show Set.Ioi T ⊆ Set.Ioi A.threshold from
      fun _ hx => lt_of_le_of_lt hT hx)) ∘ ((Geometry A j).highPresentation T).symm
private theorem high_inclusion_open (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    IsOpenEmbedding (high_inclusion A j T hT) := by
  apply (Geometry A j).highPresentation A.threshold |>.isOpenEmbedding.comp
  apply IsOpenEmbedding.comp _ ((Geometry A j).highPresentation T).symm.isOpenEmbedding
  exact IsOpenEmbedding.id.prodMap (.inclusion _ (isOpen_Ioi.preimage continuous_subtype_val))
private theorem high_end_factor (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T =
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) A.threshold ∘
        high_inclusion A j T hT := by
  funext z
  obtain ⟨⟨q,t⟩,rfl⟩ := ((Geometry A j).highPresentation T).surjective z
  dsimp only [Function.comp_apply, high_inclusion]
  rw [Homeomorph.symm_apply_apply]
  induction q using Quotient.inductionOn with
  | h p =>
    dsimp only [Prod.map, id_eq]
    rw [(Geometry A j).highPresentation_formula, (Geometry A j).highPresentation_formula]
    rfl
private theorem high_end_open (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    IsOpenEmbedding (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T) := by
  rw [high_end_factor A j T hT]
  apply IsOpenEmbedding.comp _ (high_inclusion_open A j T hT)
  refine ⟨?_, ?_⟩
  · have he := (A.cuspAtlas j.1).end_embedding j.2
    rw [A.common_threshold j.1] at he
    exact he
  · rw [KPFiniteCuspAtlas.endMap_range F (Geometry A j).positive_dimension]
    simpa only [A.common_threshold j.1] using (A.cuspAtlas j.1).open_ends j.2

private theorem sigma_open_embedding {ι : Type*} {σ : ι → Type*} {X : Type*}
    [∀ i, TopologicalSpace (σ i)] [TopologicalSpace X]
    (f : (Σ i, σ i) → X)
    (hf : ∀ i, IsOpenEmbedding (fun x => f ⟨i,x⟩))
    (hd : Pairwise (fun i j => Disjoint (Set.range (fun x => f ⟨i,x⟩))
      (Set.range (fun x => f ⟨j,x⟩)))) : IsOpenEmbedding f := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_sigma (fun i => (hf i).continuous)
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    by_cases hij : i = j
    · subst j
      exact congrArg (Sigma.mk i) ((hf i).injective he)
    · exact False.elim (Set.disjoint_left.mp (hd hij) (Set.mem_range_self x)
        (show f ⟨i,x⟩ ∈ Set.range (fun y => f ⟨j,y⟩) from ⟨y,he.symm⟩))
  · exact isOpenMap_sigma.mpr (fun i => (hf i).isOpenMap)
private theorem actual_component_open (i : Fin A.componentCount) :
    IsOpenEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
      A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he]
  exact A.components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
private theorem endSet_mono (j : CuspIndex A) {T S : ℝ} (h : S ≤ T) :
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) T ⊆
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) S := by
  apply Set.image_mono
  apply Set.image_mono
  exact fun _ hx => lt_of_le_of_lt h hx
private theorem component_ends_disjoint (T : ℝ) (hT : A.threshold ≤ T) :
    Pairwise fun j k : CuspIndex A => Disjoint
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).representative j.2) T)
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative k.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
          ((A.cuspAtlas k.1).representative k.2) T) := by
  rintro ⟨i,a⟩ ⟨l,b⟩ hne
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
  have hec : A.components ⟨l,z⟩ = A.components ⟨i,y⟩ := by
    simpa only [A.components_formula] using he
  have hs := A.components.injective hec
  have hil : l = i := congrArg Sigma.fst hs
  subst l
  have hab : a ≠ b := fun h => hne (congrArg (Sigma.mk i) h)
  have hyz : z = y := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs
  subst z
  have hd := (A.cuspAtlas i).disjoint_ends hab
  apply Set.disjoint_left.mp hd
  · exact endSet_mono A ⟨i,a⟩ (by rw [A.common_threshold i]; exact hT) hy
  · exact endSet_mono A ⟨i,b⟩ (by rw [A.common_threshold i]; exact hT) hz

private theorem actual_endMap_continuous (j : CuspIndex A) (T : ℝ) :
    Continuous (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (((KPCuspCharts.projectiveHomeomorph F
      ((A.cuspAtlas j.1).representative j.2)).continuous.comp
        (KPCuspCharts.toArch_contDiff F).continuous).comp continuous_subtype_val)

 def pinned_local_end (j : CuspIndex A) (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) :
    KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)) × Set.Ioi Y →
        Spherical F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ∘
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)
      (logHeight (F := F) Y) ∘ pinned_radial_presentation (Geometry A j) w Y hY

private theorem pinned_local_end_continuous (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    Continuous (pinned_local_end A j w Y hY) := by
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) =
        fun x => A.components ⟨j.1,x⟩ := by
      funext x
      exact (A.components_formula j.1 x).symm
    rw [he]
    exact A.components.continuous.comp continuous_sigmaMk
  exact hc.comp ((actual_endMap_continuous A j _).comp
    (pinned_radial_presentation (Geometry A j) w Y hY).continuous)

private theorem pinned_local_end_range (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    Set.range (pinned_local_end A j w Y hY) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y) := by
  change Set.range (_ ∘ _ ∘ _) = _
  rw [Set.range_comp, Set.range_comp,
    (pinned_radial_presentation (Geometry A j) w Y hY).surjective.range_eq,
    Set.image_univ, KPFiniteCuspAtlas.endMap_range F (Geometry A j).positive_dimension]

private theorem pinned_local_end_formula (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_local_end A j w Y hY (Quotient.mk _ p,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F
            ((p.1, p.2 + sectionShape F hF w ⟨r.val, lt_trans hY r.property⟩),
              logHeight (F := F) r.val))) := by
  dsimp only [pinned_local_end, Function.comp_apply]
  rw [pinned_radial_presentation_formula]
  rfl
private theorem pinned_local_end_open (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsOpenEmbedding (pinned_local_end A j w Y hY.1) :=
  (actual_component_open A j.1).comp
    ((high_end_open A j _ hY.2).comp
      (pinned_radial_presentation (Geometry A j) w Y hY.1).isOpenEmbedding)

 def pinned_cusp_chart (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) : CrossSection A × Set.Ioi Y → Spherical F ζ hζ U :=
  (fun x => pinned_local_end A x.1 w Y hY x.2) ∘ Homeomorph.sigmaProdDistrib

private theorem pinned_cusp_chart_continuous (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) : Continuous (pinned_cusp_chart A w Y hY) := by
  apply Continuous.comp _ Homeomorph.sigmaProdDistrib.continuous
  apply continuous_sigma
  intro j
  exact pinned_local_end_continuous A j w Y hY

private theorem pinned_cusp_chart_range (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) :
    Set.range (pinned_cusp_chart A w Y hY) = cuspEnds A Y := by
  ext x
  change (∃ p : CrossSection A × Set.Ioi Y, pinned_cusp_chart A w Y hY p = x) ↔ _
  simp only [cuspEnds, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨j,p⟩,r⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← pinned_local_end_range A j w Y hY]
    exact ⟨(p,r), he⟩
  · rintro ⟨j, hx⟩
    rw [← pinned_local_end_range A j w Y hY] at hx
    obtain ⟨⟨p,r⟩,he⟩ := hx
    exact ⟨(⟨j,p⟩,r), he⟩

private theorem pinned_cusp_chart_open (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsOpenEmbedding (pinned_cusp_chart A w Y hY.1) := by
  apply IsOpenEmbedding.comp _ Homeomorph.sigmaProdDistrib.isOpenEmbedding
  apply sigma_open_embedding
  · intro j
    exact pinned_local_end_open A j w Y hY
  · simpa only [pinned_local_end_range] using
      component_ends_disjoint A (logHeight (F := F) Y) hY.2

private theorem pinned_cusp_chart_embedding (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsEmbedding (pinned_cusp_chart A w Y hY.1) :=
  (pinned_cusp_chart_open A w Y hY).isEmbedding

 theorem pinned_cusp_chart_formula (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) (j : CuspIndex A)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_cusp_chart A w Y hY (⟨j, Quotient.mk _ p⟩,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F
            ((p.1, p.2 + sectionShape F hF w ⟨r.val, lt_trans hY r.property⟩),
              logHeight (F := F) r.val))) :=
  pinned_local_end_formula A j w Y hY p r

 def base_cutoff : ℝ :=
  Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * A.threshold)

 theorem base_cutoff_admissible : AdmissibleCutoff A (base_cutoff A) := by
  refine ⟨Real.exp_pos _, ?_⟩
  unfold logHeight base_cutoff
  rw [Real.log_exp, mul_div_cancel_left₀ _ (ne_of_gt (mul_pos (by norm_num)
    (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))))]

private theorem base_cutoff_le (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    base_cutoff A ≤ Y := by
  unfold base_cutoff
  rw [← Real.exp_log hY.1]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))
  have ht := (le_div_iff₀ hd).mp hY.2
  simpa only [mul_comm] using ht

private theorem pinned_cusp_chart_cutoff (w : NumberField.InfinitePlace F)
    (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (x : CrossSection A)
    (r : Set.Ioi Y) (hr : Z < r.val) :
    pinned_cusp_chart A w Y hY (x,r) =
      pinned_cusp_chart A w Z hZ (x,⟨r.val,hr⟩) := by
  rcases x with ⟨j,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    rw [pinned_cusp_chart_formula, pinned_cusp_chart_formula]

 def pinned_modulus (w : NumberField.InfinitePlace F) :
    Spherical F ζ hζ U → ℝ :=
  Function.extend (pinned_cusp_chart A w (base_cutoff A) (base_cutoff_admissible A).1)
    (fun p => p.2.val) (fun _ => 0)

private theorem pinned_modulus_measurable (w : NumberField.InfinitePlace F) :
    Measurable (pinned_modulus A w) := by
  apply (pinned_cusp_chart_open A w _ (base_cutoff_admissible A)).measurableEmbedding.measurable_extend
  · exact measurable_subtype_coe.comp measurable_snd
  · exact measurable_const

private theorem pinned_modulus_base (w : NumberField.InfinitePlace F)
    (x : CrossSection A) (r : Set.Ioi (base_cutoff A)) :
    pinned_modulus A w
      (pinned_cusp_chart A w (base_cutoff A) (base_cutoff_admissible A).1 (x,r)) = r.val := by
  exact (pinned_cusp_chart_embedding A w _ (base_cutoff_admissible A)).injective.extend_apply
    (fun p => p.2.val) (fun _ => 0) (x,r)

private theorem pinned_cusp_chart_modulus (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) (x : CrossSection A) (r : Set.Ioi Y) :
    pinned_modulus A w (pinned_cusp_chart A w Y hY.1 (x,r)) = r.val := by
  have hr : base_cutoff A < r.val := lt_of_le_of_lt (base_cutoff_le A Y hY) r.property
  rw [pinned_cusp_chart_cutoff A w Y (base_cutoff A) hY.1
    (base_cutoff_admissible A).1 x r hr]
  exact pinned_modulus_base A w x ⟨r.val,hr⟩

end PinnedLocalEnd

end PinnedRadialCharts

namespace ComponentNormalization
open MeasureTheory Set
open scoped ENNReal Pointwise

private theorem smul_weight_unique
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hz : μ A ≠ 0) (ht : μ A ≠ ⊤) {a b : ℝ≥0∞}
    (h : a • μ = b • μ) : a = b := by
  have he := congrArg (fun ν : Measure X => ν A) h
  simp only [Measure.smul_apply, smul_eq_mul] at he
  exact (ENNReal.mul_right_inj hz ht).mp (by simpa only [mul_comm] using he)

end ComponentNormalization

namespace ComponentFiber
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming basepoint_continuous → basepoint_continuous
open MeasureTheory Set
open scoped ENNReal Pointwise
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finite_orbit_spherical (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x,c) : Spherical F ζ hζ U) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U g (KPCuspSiegel.projection F _ x) := by
  obtain ⟨ε,u,rfl⟩ := hc
  change Quotient.mk _ (x,_) = Quotient.mk _ (x,g)
  apply Eq.symm
  apply Quotient.sound
  refine ⟨1, ε, u, ?_, ?_⟩
  · simp
  · simp

 theorem spherical_fiber_formula (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (a : KPSmoothActualFlowData.GInfinity F) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U g
        (KPCuspSiegel.projection F _ (archBasepoint F a)) := by
  rw [P.formula]
  exact finite_orbit_spherical F ζ hζ U g c hc _

private theorem spherical_restrict_pushforward
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ)
    (C : Set (Spherical F ζ hζ U)) (hC : MeasurableSet C) :
    (sphericalMeasure F ζ hζ R P U).restrict C =
      Measure.map (P.projection U) (R.quotientHaar.restrict (P.projection U ⁻¹' C)) := by
  exact Measure.restrict_map (P.continuous U).measurable hC

private theorem component_range_clopen
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount) :
    IsClopen (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
      A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he, Set.range_comp]
  constructor
  · exact A.components.isClosedMap _ isClosed_range_sigmaMk
  · exact A.components.isOpenMap _ isOpen_range_sigmaMk

private theorem actual_component_weight
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (i : Fin A.componentCount) :
    ∃ w : ℝ≥0∞, 0 < w ∧ w < ⊤ ∧
      (sphericalMeasure F ζ hζ R P U).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
      w • Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
    change SecondCountableTopology ↥((KPCuspGenuineMonodromy.archProjection F ζ hζ).ker : Set (KPCuspGenuineMonodromy.Cover F ζ hζ))
    infer_instance
  obtain ⟨ep,hep,_,_,_,_,hLCP⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI : SecondCountableTopology (PGLComplex.AdelicSlicesRaw.ArchGroup F × PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) := by
    letI : SecondCountableTopology (PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) := ActualQuotient.actual_cover_secondCountable F ζ hζ
    exact ep.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).secondCountableTopology
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  obtain ⟨ν,hν,hprod,D,hDm,hD,hB,hBp,hBf,hq⟩ :=
    KPActualComponentHaarSources.actual_component_product_disintegration F ζ hζ hF U A R P i
  obtain ⟨c,hc,harch,hvol⟩ :=
    KPActualComponentHaarSources.arch_group_domain_quotient_volume F ζ hζ hF U A R i D hDm hD
  letI := hν
  letI := R.arch_isHaar
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F) := by
    obtain ⟨e,he,_,_,_,_,hLC⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
    letI : LocallyCompactSpace (PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    letI : LocallyCompactSpace (PGLComplex.AdelicSlicesRaw.ArchGroup F × PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
    exact (isOpenQuotientMap_fst (Y := PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).locallyCompactSpace
  let BB := KPActualComponentHaarSources.B F ζ hζ hF U A i
  letI : IsFiniteMeasure (ν.restrict BB) := ⟨by simpa [BB] using hBf⟩
  letI : SFinite R.archHaar := inferInstance
  refine ⟨ν (KPActualComponentHaarSources.B F ζ hζ hF U A i) * c,
    ENNReal.mul_pos hBp.ne' (ENNReal.coe_pos.mpr hc).ne', ENNReal.mul_lt_top hBf ENNReal.coe_lt_top, ?_⟩
  rw [spherical_restrict_pushforward R P U _ (component_range_clopen A i).isOpen.measurableSet,
    ]
  unfold KPActualComponentHaarSources.C at hq
  rw [hq]
  have hcm : Measurable (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
        A.components ∘ Sigma.mk i := by funext x; exact (A.components_formula i x).symm
    apply measurable_from_quotient.mpr
    have hh : Measurable (fun x : KPFiniteCuspAtlas.SymmetricSpace F => A.components ⟨i, KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) x⟩) :=
      (A.components.continuous.comp ((continuous_sigmaMk (i := i)).comp
        (continuous_quotient_mk' : Continuous (KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i))))).measurable
    convert hh using 1
    funext x
    exact (A.components_formula i (KPCuspSiegel.projection F _ x)).symm
  have hb : Measurable (KPCuspSiegel.projection F
      (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F) := by
    exact measurable_quotient_mk''.comp (basepoint_continuous F ζ hζ).measurable
  let f := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘ KPActualComponentHaarSources.m F ζ hζ
  let gg := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) ∘
    KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
  rw [Measure.map_map (P.continuous U).measurable hfm]
  have he : (P.projection U ∘ f) =ᵐ[(R.archHaar.restrict D).prod (ν.restrict BB)] gg ∘ Prod.fst := by
    have hmem : ∀ᵐ p ∂(R.archHaar.restrict D).prod (ν.restrict BB), p.2 ∈ BB :=
      (Measure.ae_prod_iff_ae_ae (measurable_snd hB)).mpr
        (Filter.Eventually.of_forall fun _ => ae_restrict_mem hB)
    filter_upwards [hmem] with p hp
    exact spherical_fiber_formula F ζ hζ P U (A.representative i) p.2 hp p.1
  rw [Measure.map_congr he, ← Measure.map_map (hcm.comp hb) measurable_fst,
    Measure.map_fst_prod, Measure.restrict_apply_univ,
    Measure.map_smul _ (hcm.comp hb).aemeasurable]
  have hvol' : Measure.map (KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F) (R.archHaar.restrict D) = (c : ℝ≥0∞) • KPFiniteCuspAtlas.quotientVolume F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) (A.cuspAtlas i).fundamentalDomain := hvol
  simp only [← Measure.map_map hcm hb, hvol', Measure.map_smul _ hcm.aemeasurable, smul_smul]
  rfl

private theorem actual_component_weights
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) :
    ∃ w : Fin A.componentCount → ℝ≥0∞, (∀ i, 0 < w i) ∧ (∀ i, w i < ⊤) ∧
      ∀ i, (sphericalMeasure F ζ hζ R P U).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
      w i • Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain) := by
  choose w hp hf he using fun i => actual_component_weight F ζ hζ A R P i
  exact ⟨w,hp,hf,he⟩

end ComponentFiber

namespace FixedLevelGeometry
open MeasureTheory

 theorem actual_fixed_level_geometry
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (B : RadialData F ζ hζ) (K : FiberKernel A) :
    ∃ D : GeometricDisintegration A R P, D.radial = B ∧ D.toFiberKernel = K := by
  obtain ⟨w,hpos,hfin,hcomp⟩ := ComponentFiber.actual_component_weights F ζ hζ A R P
  refine ⟨{
    toFiberKernel := K
    radial := B
    beta := weighted_angular_measure A w
    finite_beta := weighted_angular_finite A w hfin
    positive_beta := weighted_angular_positive A w hpos
    probability_mass := weighted_angular_probability A w hpos hfin
    componentWeight := w
    positive_componentWeight := hpos
    finite_componentWeight := hfin
    component_measure := hcomp
    induced_beta := weighted_angular_apply A w
    section_disintegration := weighted_section_disintegration A K w
    modulus := PinnedRadialCharts.pinned_modulus A B.slot
    measurable_modulus := PinnedRadialCharts.pinned_modulus_measurable A B.slot
    chart := fun Y hY => PinnedRadialCharts.pinned_cusp_chart A B.slot Y hY.1
    measurable_chart := fun Y hY =>
      (PinnedRadialCharts.pinned_cusp_chart_continuous A B.slot Y hY.1).measurable
    chart_range := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_range A B.slot Y hY.1
    chart_embedding := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_embedding A B.slot Y hY
    chart_modulus := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_modulus A B.slot Y hY
    chart_formula := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_formula A B.slot Y hY.1
    }, rfl, rfl⟩

end FixedLevelGeometry

namespace AllLevelGeometry
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

private theorem actual_component_matching
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ∃ (i : Fin A.componentCount) (δ : KPCuspArithmetic.PGL2 F)
      (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      A.representative i = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
        KPCuspGenuineMonodromy.central F ζ hζ ε * c * u := by
  let x : KPFiniteCuspAtlas.SymmetricSpace F := fun _ => (0,0)
  obtain ⟨⟨i,z⟩, hz⟩ := A.components.surjective (Quotient.mk _ (x,c))
  rw [A.components_formula] at hz
  induction z using Quotient.inductionOn with
  | h z =>
    obtain ⟨δ, ε, u, hx, hc⟩ := Quotient.exact hz.symm
    exact ⟨i, δ, ε, u, hc⟩

private theorem conjugate_subgroup_refinement
    {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (a g u : G) (hu : u ∈ K) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a).toMonoidHom ≤
      K.map (MulAut.conj (a * g * u)).toMonoidHom := by
  rintro x ⟨y, ⟨v,hv,rfl⟩, rfl⟩
  refine ⟨u⁻¹ * v * u, K.mul_mem (K.mul_mem (K.inv_mem hu) (h hv)) hu, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem actual_component_conjugate
    {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u) :
    (KPCuspGenuineMonodromy.Component F ζ hζ V c).map (MulAut.conj δ).toMonoidHom ≤
      KPCuspGenuineMonodromy.Component F ζ hζ U g := by
  let φ := KPCuspGenuineMonodromy.finiteBase F ζ hζ
  let d := KPFiniteComponents.diagonal F
  have hd : ∀ x, φ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ x) = d x := by
    intro x
    exact congrArg (fun f => f x) (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1
  have hz : φ (KPCuspGenuineMonodromy.central F ζ hζ ε) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
    exact ⟨ε,rfl⟩
  have hp : φ g = d δ * φ c * φ u := by
    rw [hg, map_mul, map_mul, map_mul, hd, hz, mul_one]
  rintro x ⟨y,hy,rfl⟩
  change d ((MulAut.conj δ) y) ∈
    (U.toOpenSubgroup.toSubgroup.map φ).map (MulAut.conj (φ g)).toMonoidHom
  rw [hp]
  have hh := conjugate_subgroup_refinement (Subgroup.map_mono (f := φ) h)
    (d δ) (φ c) (φ u) (show φ u ∈ U.toOpenSubgroup.toSubgroup.map φ from ⟨u,u.property,rfl⟩)
  apply hh
  refine ⟨d y,hy,?_⟩
  simp [d, MulAut.conj_apply]

private theorem conjugated_cusp_refinement
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)}
    {q r : KPCuspArithmetic.Cusp F} (σ τ δ : KPCuspArithmetic.PGL2 F)
    (h : Γ.map (MulAut.conj δ).toMonoidHom ≤ Δ) (hq : δ • q = r) :
    (KPCuspArithmetic.conjugatedStabilizer F Γ q σ).map
      (MulAut.conj (τ⁻¹ * δ * σ)).toMonoidHom ≤
        KPCuspArithmetic.conjugatedStabilizer F Δ r τ := by
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨δ * z * δ⁻¹, ⟨h ⟨z,hz.1,rfl⟩,?_⟩,?_⟩
  · change (δ * z * δ⁻¹) • r = r
    rw [← hq]
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (fun p => δ • p) hz.2
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

 def coordinate_transition (hd : 0 < KPCuspLogShape.dimension F)
    (t : KPCuspArithmetic.PGL2 F) : KPCuspCharts.Coordinates F ≃ₜ KPCuspCharts.Coordinates F :=
  ((KPCuspCharts.toArchHomeomorph F hd).trans (KPCuspCharts.projectiveHomeomorph F t)).trans
    (KPCuspCharts.toArchHomeomorph F hd).symm

 theorem coordinate_transition_formula (hd : 0 < KPCuspLogShape.dimension F)
    (t : KPCuspArithmetic.PGL2 F) (p : KPCuspCharts.Coordinates F) :
    KPCuspCharts.toArch F (coordinate_transition hd t p) = t • KPCuspCharts.toArch F p := by
  exact (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply _

 theorem actual_full_chart_commutes
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (j : CuspIndex AV) (k : CuspIndex AU)
    (δ : KPCuspArithmetic.PGL2 F)
    (η : KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : AU.representative k.1 = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative j.1 * u)
    (p : KPCuspCharts.Coordinates F) :
    P.forget V U h (Quotient.mk _
      (((AV.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p,
        AV.representative j.1)) =
    Quotient.mk _
      (((AU.cuspAtlas k.1).representative k.2) • KPCuspCharts.toArch F
        (coordinate_transition (KPCuspCharts.positive_dimension F hF)
          (((AU.cuspAtlas k.1).representative k.2)⁻¹ * (η.val⁻¹ * δ) *
            (AV.cuspAtlas j.1).representative j.2) p), AU.representative k.1) := by
  rw [P.forget_formula, coordinate_transition_formula]
  simp only [mul_smul, smul_inv_smul]
  calc
    Quotient.mk _ (((AV.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p,
        AV.representative j.1) =
      Quotient.mk _ (δ • (((AV.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p),
        AU.representative k.1) := by
      apply Quotient.sound
      exact ⟨δ,ε,u,rfl,hc⟩
    _ = _ := by
      change KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k.1)
        (KPCuspSiegel.projection F _ (δ • (((AV.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p))) =
        KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k.1)
        (KPCuspSiegel.projection F _ (η.val⁻¹ • (δ • (((AV.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F p))))
      congr 1
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨η,smul_inv_smul η.val _⟩

end AllLevelGeometry

namespace NormOneTransition
open MeasureTheory
open _root_.DedekindZetaZeroFree.KPCuspCharts renaming upper_action → upper_action
open _root_.DedekindZetaZeroFree.KPCuspChart.SectionConstruction renaming horizontalLinear → horizontalLinear
open _root_.DedekindZetaZeroFree.KPCuspChart.SectionConstruction renaming horizontal_det → horizontal_det
variable {F : Type} [Field F] [NumberField F]

 def shift (u : Fˣ)
    (hu : ∑ i : Fin (KPCuspLogShape.dimension F),
      Real.log ((KPCusp.complexPlace F i) (u : F)) = 0) : KPCuspCharts.Shape F :=
  ⟨fun i => Real.log ((KPCusp.complexPlace F i) (u : F)), hu⟩

 def crossCoordinate (u : Fˣ) (v : F)
    (hu : ∑ i : Fin (KPCuspLogShape.dimension F),
      Real.log ((KPCusp.complexPlace F i) (u : F)) = 0)
    (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  (fun i => (KPCusp.complexPlace F i).embedding (u : F) * p.1 i +
    (KPCusp.complexPlace F i).embedding v, p.2 + shift u hu)

 theorem crossCoordinate_continuous (u : Fˣ) (v : F)
    (hu : ∑ i : Fin (KPCuspLogShape.dimension F),
      Real.log ((KPCusp.complexPlace F i) (u : F)) = 0) :
    Continuous (crossCoordinate u v hu) := by
  exact (continuous_pi fun i => (continuous_const.mul
    ((continuous_apply i).comp continuous_fst)).add continuous_const).prodMk
      (continuous_snd.add continuous_const)

 def crossCoordinateHomeomorph (u : Fˣ) (v : F)
    (hu : ∑ i : Fin (KPCuspLogShape.dimension F),
      Real.log ((KPCusp.complexPlace F i) (u : F)) = 0) :
    KPCuspCharts.Cross F ≃ₜ KPCuspCharts.Cross F where
  toFun := crossCoordinate u v hu
  invFun := fun p =>
    (fun i => (p.1 i - (KPCusp.complexPlace F i).embedding v) /
      (KPCusp.complexPlace F i).embedding (u : F), p.2 - shift u hu)
  left_inv := by
    intro p
    apply Prod.ext
    · funext i
      dsimp [crossCoordinate]
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _
        ((map_ne_zero _).mpr (Units.ne_zero u))]
    · exact add_sub_cancel_right p.2 (shift u hu)
  right_inv := by
    intro p
    apply Prod.ext
    · funext i
      dsimp [crossCoordinate]
      rw [mul_div_cancel₀ _ ((map_ne_zero _).mpr (Units.ne_zero u)), sub_add_cancel]
    · exact sub_add_cancel p.2 (shift u hu)
  continuous_toFun := crossCoordinate_continuous u v hu
  continuous_invFun :=
    (continuous_pi fun i =>
      (((continuous_apply i).comp continuous_fst).sub continuous_const).div_const _).prodMk
        (continuous_snd.sub continuous_const)

private theorem prod_cancel_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) (ρ : Measure Y) [SigmaFinite ρ] (hρ : ρ ≠ 0)
    (h : μ.prod ρ = ν.prod ρ) : μ = ν := by
  obtain ⟨n,hn⟩ := (Measure.exists_measure_inter_spanningSets_pos (μ := ρ) Set.univ).mpr
    (Measure.measure_univ_pos.mpr hρ)
  simp only [Set.univ_inter] at hn
  apply Measure.ext
  intro E hE
  have he := congrArg (fun m : Measure (X × Y) => m (E ×ˢ spanningSets ρ n)) h
  simp only [Measure.prod_prod] at he
  exact (ENNReal.mul_left_inj hn.ne' (measure_spanningSets_lt_top ρ n).ne).mp he

private theorem prod_cancel_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (μ ν : Measure Y) [SigmaFinite ρ] [SFinite μ] [SFinite ν]
    (hρ : ρ ≠ 0) (h : ρ.prod μ = ρ.prod ν) : μ = ν := by
  obtain ⟨n,hn⟩ := (Measure.exists_measure_inter_spanningSets_pos (μ := ρ) Set.univ).mpr
    (Measure.measure_univ_pos.mpr hρ)
  simp only [Set.univ_inter] at hn
  apply Measure.ext
  intro E hE
  have he := congrArg (fun m : Measure (X × Y) => m (spanningSets ρ n ×ˢ E)) h
  simp only [Measure.prod_prod] at he
  exact (ENNReal.mul_right_inj hn.ne' (measure_spanningSets_lt_top ρ n).ne).mp he

 theorem shapeMeasure_eq
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S T : Subgroup (KPCuspArithmetic.PGL2 F)}
    {DS : KPCuspCharts.ParabolicData F S} {DT : KPCuspCharts.ParabolicData F T}
    (GS : KPCuspCharts.ChartOutput F hF S DS) (GT : KPCuspCharts.ChartOutput F hF T DT) :
    GS.shapeMeasure = GT.shapeMeasure := by
  letI := GS.haar_shapeMeasure
  letI := GT.haar_shapeMeasure
  let ρ := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  letI : SigmaFinite ρ := by dsimp [ρ, KPCuspCharts.radialMeasure]; infer_instance
  have hr : ρ ≠ 0 := by
    have hf : Measurable (fun t : ℝ => ENNReal.ofReal
        (Real.exp (-2 * (KPCuspLogShape.dimension F : ℝ) * t))) := by fun_prop
    have ha : (volume : Measure ℝ) ≪ ρ := withDensity_absolutelyContinuous' hf.aemeasurable
      (Filter.Eventually.of_forall fun t => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    intro he
    rw [he] at ha
    have hv := Measure.absolutelyContinuous_zero_iff.mp ha
    exact isOpen_univ.measure_ne_zero (μ := (volume : Measure ℝ)) Set.univ_nonempty
      (by rw [hv]; simp)
  have hh : ((volume : Measure (KPCuspCharts.Horizontal F)).prod GS.shapeMeasure).prod ρ =
      ((volume : Measure (KPCuspCharts.Horizontal F)).prod GT.shapeMeasure).prod ρ := by
    apply (KPCuspCharts.toArchHomeomorph F GS.positive_dimension).measurableEmbedding.map_injective
    exact GS.archVolume_formula.trans GT.archVolume_formula.symm
  have hv : (volume : Measure (KPCuspCharts.Horizontal F)) ≠ 0 := by
    intro he
    exact isOpen_univ.measure_ne_zero (μ := (volume : Measure (KPCuspCharts.Horizontal F)))
      Set.univ_nonempty (by rw [he]; simp)
  exact prod_cancel_left volume _ _ hv (prod_cancel_right _ _ ρ hr hh)

 theorem crossAction_toArch
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (g : S) (p : KPCuspCharts.Cross F) :
    g.val • KPCuspCharts.toArch F (p,0) = KPCuspCharts.toArch F (G.crossAction g p,0) := by
  obtain ⟨M,hM,hc⟩ := D.upper g.val g.property
  change KPCuspSiegel.action F g.val _ = _
  rw [G.actual_action g M hM hc, G.crossAction_formula g M hM hc]
  rfl

 theorem sectionMeasure_alt_domain
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (Ω : Set (KPCuspCharts.Cross F))
    (hΩ : letI := KPCuspCharts.homeomorphAction G.crossAction
      IsFundamentalDomain S Ω (volume.prod G.shapeMeasure)) :
    Measure.map (Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict Ω) = G.sectionMeasure := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun g => (G.crossAction g).continuous.measurable⟩
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) :=
    ⟨fun g E hE => by
      change (volume.prod G.shapeMeasure) ((G.crossAction g) ⁻¹' E) = _
      rw [← Measure.map_apply (G.crossAction g).continuous.measurable hE, G.measure_invariant]⟩
  have hq (g : S) (p : KPCuspCharts.Cross F) :
      Quotient.mk (KPCuspCharts.crossRelation F S) (G.crossAction g p) =
        Quotient.mk (KPCuspCharts.crossRelation F S) p := by
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨g, crossAction_toArch G g p⟩
  rw [G.sectionMeasure_formula]
  apply Measure.ext
  intro E hE
  have hm : Measurable (Quotient.mk (KPCuspCharts.crossRelation F S)) := measurable_quotient_mk''
  rw [Measure.map_apply measurable_quotient_mk'' hE,
    Measure.map_apply measurable_quotient_mk'' hE,
    Measure.restrict_apply (hm hE),
    Measure.restrict_apply (hm hE)]
  apply hΩ.measure_set_eq G.isFundamentalDomain (hm hE)
  intro g
  ext p
  change (Quotient.mk (KPCuspCharts.crossRelation F S) (G.crossAction g p) ∈ E) ↔ _
  rw [hq]
  rfl

open Set
open scoped ENNReal Pointwise
namespace IndexPort
 def cosetProd (G : Type*) [Group G] (H : Subgroup G) : (G ⧸ H) × H ≃ G :=
  Equiv.ofBijective (fun p => p.1.out * p.2.val) (by
    constructor
    · intro ⟨q,h⟩ ⟨r,k⟩ he
      have hq : q = r := by
        have : (q.out * h.val : G ⧸ H) = (r.out * k.val : G ⧸ H) := congrArg QuotientGroup.mk he
        simpa only [QuotientGroup.mk_mul_of_mem _ h.property,
          QuotientGroup.mk_mul_of_mem _ k.property, Quotient.out_eq'] using this
      subst r
      have hh : h = k := Subtype.ext (mul_left_cancel he)
      subst k
      rfl
    · intro g
      refine ⟨((g : G ⧸ H), ⟨((g : G ⧸ H).out)⁻¹ * g, ?_⟩), ?_⟩
      · exact QuotientGroup.eq.mp (Quotient.out_eq' (g : G ⧸ H))
      · simp)

 theorem integral_index
    {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    [Countable G] [MeasurableConstSMul G α] (μ : Measure α) [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [H.FiniteIndex] {s t : Set α}
    (hs : IsFundamentalDomain H s μ) (ht : IsFundamentalDomain G t μ)
    (f : α → ℝ≥0∞) (hf : ∀ (g : G) x, f (g • x) = f x) :
    (∫⁻ x in s, f x ∂μ) = H.index * ∫⁻ x in t, f x ∂μ := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [ht.setLIntegral_eq_tsum' f s]
  simp only [hf]
  rw [← (cosetProd G H).tsum_eq, ENNReal.tsum_prod']
  have he (q : G ⧸ H) :
      (∑' h : H, ∫⁻ x in (cosetProd G H (q,h)) • s ∩ t, f x ∂μ) =
        ∫⁻ x in t, f x ∂μ := by
    change (∑' h : H, ∫⁻ x in (q.out * h.val) • s ∩ t, f x ∂μ) = _
    have hi (h : H) :
        (∫⁻ x in (q.out * h.val) • s ∩ t, f x ∂μ) =
          ∫⁻ x in (q.out⁻¹ • t) ∩ h • s, f x ∂μ := by
      have hset : (q.out * h.val) • s ∩ t = q.out • ((q.out⁻¹ • t) ∩ h • s) := by
        change _ = q.out • ((q.out⁻¹ • t) ∩ h.val • s)
        simp only [smul_set_inter, smul_smul, mul_inv_cancel, one_smul, inter_comm]
      rw [hset]
      have he := (measurePreserving_smul q.out μ).setLIntegral_comp_emb
        (measurableEmbedding_const_smul _) f ((q.out⁻¹ • t) ∩ h • s)
      simpa only [hf, Set.image_smul] using he.symm
    simp_rw [hi]
    rw [← hs.setLIntegral_eq_tsum f (q.out⁻¹ • t)]
    have he := (measurePreserving_smul q.out⁻¹ μ).setLIntegral_comp_emb
      (measurableEmbedding_const_smul _) f t
    simpa only [hf, Set.image_smul] using he.symm
  simp_rw [he]
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Subgroup.index, Nat.card_eq_fintype_card]
end IndexPort

end NormOneTransition

namespace FiniteIndexContinuation

open MeasureTheory
private theorem level_finite_relindex
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V U : CompactOpenLevel G) :
    V.toOpenSubgroup.toSubgroup.IsFiniteRelIndex U.toOpenSubgroup.toSubgroup := by
  let : CompactSpace U.toOpenSubgroup.toSubgroup :=
    isCompact_iff_compactSpace.mp U.isCompact
  let : Finite (U.toOpenSubgroup.toSubgroup ⧸
      V.toOpenSubgroup.toSubgroup.subgroupOf U.toOpenSubgroup.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _
      (show IsOpen (Subtype.val ⁻¹' (V.toOpenSubgroup : Set G)) from
        V.toOpenSubgroup.isOpen.preimage continuous_subtype_val)
  exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
    Subgroup.finiteIndex_of_finite_quotient

private theorem conj_right_member {G : Type*} [Group G] (K : Subgroup G)
    (a u : G) (hu : u ∈ K) :
    K.map (MulAut.conj (a * u)).toMonoidHom = K.map (MulAut.conj a).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨u * y * u⁻¹, K.mul_mem (K.mul_mem hu hy) (K.inv_mem hu), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y,hy,rfl⟩
    refine ⟨u⁻¹ * y * u, K.mul_mem (K.mul_mem (K.inv_mem hu) hy) hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem conj_comap {G J : Type*} [Group G] [Group J]
    (f : G →* J) (H : Subgroup J) (a : G) :
    (H.comap f).map (MulAut.conj a).toMonoidHom =
      (H.map (MulAut.conj (f a)).toMonoidHom).comap f := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨f y, hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨a⁻¹ * x * a, ?_, ?_⟩
    · change f (a⁻¹ * x * a) ∈ H
      have hfy : f (a⁻¹ * x * a) = y := by
        simp only [map_mul, map_inv]
        change f a * y * (f a)⁻¹ = f x at he
        rw [← he]
        group
      rwa [hfy]
    · simp [MulAut.conj_apply, mul_assoc]
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

private theorem component_finite_relindex (V U : Level F ζ hζ)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    (KPCuspGenuineMonodromy.Component F ζ hζ V c).IsFiniteRelIndex
      (KPCuspGenuineMonodromy.Component F ζ hζ U c) := by
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  have hi := level_finite_relindex V U
  exact ((hi.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
    (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ c)).toMonoidHom).comap
      (KPFiniteComponents.diagonal F)

private theorem component_conjugate_eq (U : Level F ζ hζ)
    {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u) :
    (KPCuspGenuineMonodromy.Component F ζ hζ U c).map (MulAut.conj δ).toMonoidHom =
      KPCuspGenuineMonodromy.Component F ζ hζ U g := by
  let φ := KPCuspGenuineMonodromy.finiteBase F ζ hζ
  let d := KPFiniteComponents.diagonal F
  have hd : φ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ) = d δ :=
    congrArg (fun f => f δ) (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1
  have hz : φ (KPCuspGenuineMonodromy.central F ζ hζ ε) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
    exact ⟨ε,rfl⟩
  have hp : φ g = d δ * φ c * φ u := by
    rw [hg, map_mul, map_mul, map_mul, hd, hz, mul_one]
  change (((U.toOpenSubgroup.toSubgroup.map φ).map
    (MulAut.conj (φ c)).toMonoidHom).comap d).map (MulAut.conj δ).toMonoidHom =
      ((U.toOpenSubgroup.toSubgroup.map φ).map (MulAut.conj (φ g)).toMonoidHom).comap d
  rw [conj_comap, hp,
    conj_right_member _ _ _ (show φ u ∈ U.toOpenSubgroup.toSubgroup.map φ from ⟨u,u.property,rfl⟩),
    Subgroup.map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem inf_finite_relindex {G : Type*} [Group G]
    {H K : Subgroup G} (L : Subgroup G) (h : H.IsFiniteRelIndex K) :
    (H ⊓ L).IsFiniteRelIndex (K ⊓ L) := by
  have hi := (h.comap L.subtype).map L.subtype
  simpa only [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype] using hi

omit [NumberField F] in
private theorem conjugated_cusp_finite_relindex
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)}
    {q r : KPCuspArithmetic.Cusp F} (σ τ δ : KPCuspArithmetic.PGL2 F)
    (h : (Γ.map (MulAut.conj δ).toMonoidHom).IsFiniteRelIndex Δ)
    (hq : δ • q = r) :
    ((KPCuspArithmetic.conjugatedStabilizer F Γ q σ).map
      (MulAut.conj (τ⁻¹ * δ * σ)).toMonoidHom).IsFiniteRelIndex
        (KPCuspArithmetic.conjugatedStabilizer F Δ r τ) := by
  have hi := (inf_finite_relindex (MulAction.stabilizer (KPCuspArithmetic.PGL2 F) r) h).map
    (MulAut.conj τ⁻¹).toMonoidHom
  have he : (KPCuspArithmetic.conjugatedStabilizer F Γ q σ).map
      (MulAut.conj (τ⁻¹ * δ * σ)).toMonoidHom =
      ((Γ.map (MulAut.conj δ).toMonoidHom) ⊓
        MulAction.stabilizer (KPCuspArithmetic.PGL2 F) r).map
          (MulAut.conj τ⁻¹).toMonoidHom := by
    rw [← hq, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← Subgroup.map_inf _ _ _ (MulAut.conj δ).injective]
    unfold KPCuspArithmetic.conjugatedStabilizer
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [he]
  exact hi

private theorem component_conjugate_finite_relindex (V U : Level F ζ hζ)
    {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u) :
    ((KPCuspGenuineMonodromy.Component F ζ hζ V c).map
      (MulAut.conj δ).toMonoidHom).IsFiniteRelIndex
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) := by
  rw [← component_conjugate_eq U δ ε u hg]
  exact (component_finite_relindex V U c).map (MulAut.conj δ).toMonoidHom

private theorem conj_member_eq {G : Type*} [Group G] (K : Subgroup G)
    (a : G) (ha : a ∈ K) : K.map (MulAut.conj a).toMonoidHom = K := by
  have hi := conj_right_member K 1 a ha
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [one_mul, he, Subgroup.map_id] at hi
  exact hi

private theorem component_cusp_match_finite_relindex
    (V U : Level F ζ hζ) {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (η : KPCuspGenuineMonodromy.Component F ζ hζ U g)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u) :
    ((KPCuspGenuineMonodromy.Component F ζ hζ V c).map
      (MulAut.conj (η.val⁻¹ * δ)).toMonoidHom).IsFiniteRelIndex
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) := by
  have hi := (component_conjugate_finite_relindex V U δ ε u hg).map
    (MulAut.conj η.val⁻¹).toMonoidHom
  rw [conj_member_eq _ _ ((KPCuspGenuineMonodromy.Component F ζ hζ U g).inv_mem η.property)] at hi
  convert hi using 1
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem actual_cusp_match_index
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : CuspIndex AV) (k : CuspIndex AU)
    (δ : KPCuspArithmetic.PGL2 F)
    (η : KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : AU.representative k.1 = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative j.1 * u)
    (hq : η.val • (AU.cuspAtlas k.1).cusp k.2 = δ • (AV.cuspAtlas j.1).cusp j.2) :
    (((KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
      ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)).map
        (MulAut.conj (((AU.cuspAtlas k.1).representative k.2)⁻¹ * (η.val⁻¹ * δ) *
          (AV.cuspAtlas j.1).representative j.2)).toMonoidHom).subgroupOf
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1))
        ((AU.cuspAtlas k.1).cusp k.2) ((AU.cuspAtlas k.1).representative k.2))).FiniteIndex := by
  apply Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
  apply conjugated_cusp_finite_relindex
  · exact component_cusp_match_finite_relindex V U δ ε u η hc
  · rw [mul_smul, ← hq, inv_smul_smul]

end FiniteIndexContinuation

namespace CuspIndexAccounting

open MulAction
private theorem sum_stabilizer_indices
    (G X : Type*) [Group G] [MulAction G X] [Finite X] :
    let : Fintype (Quotient (orbitRel G X)) := Fintype.ofFinite _
    (∑ ω : Quotient (orbitRel G X), (stabilizer G ω.out).index) = Nat.card X := by
  let : Fintype (Quotient (orbitRel G X)) := Fintype.ofFinite _
  have hfinite (ω : Quotient (orbitRel G X)) : Finite (G ⧸ stabilizer G ω.out) :=
    Finite.of_equiv (orbit G ω.out) (orbitEquivQuotientStabilizer G ω.out)
  have he := Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer G X)
  rw [Nat.card_sigma] at he
  exact he.symm

private theorem coset_stabilizer (G : Type*) [Group G] (H K : Subgroup G) (a : G) :
    stabilizer K (a : G ⧸ H) = (H.map (MulAut.conj a).toMonoidHom).subgroupOf K := by
  ext k
  change ((k.val * a : G ⧸ H) = (a : G ⧸ H)) ↔ k.val ∈ H.map (MulAut.conj a).toMonoidHom
  rw [QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨a⁻¹ * k.val * a, ?_, ?_⟩
    · change a⁻¹ * k.val * a ∈ H
      convert H.inv_mem hk using 1; group
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨x,hx,hk⟩
    change a * x * a⁻¹ = k.val at hk
    rw [← hk]
    convert H.inv_mem hx using 1; group

private theorem sum_coset_stabilizer_indices (G : Type*) [Group G]
    (H K : Subgroup G) [H.FiniteIndex] :
    let : Fintype (Quotient (orbitRel K (G ⧸ H))) := Fintype.ofFinite _
    (∑ ω : Quotient (orbitRel K (G ⧸ H)),
      ((H.map (MulAut.conj ω.out.out).toMonoidHom).subgroupOf K).index) = H.index := by
  let : Fintype (Quotient (orbitRel K (G ⧸ H))) := Fintype.ofFinite _
  have hi := sum_stabilizer_indices K (G ⧸ H)
  have he (ω : Quotient (orbitRel K (G ⧸ H))) :
      stabilizer K ω.out = (H.map (MulAut.conj ω.out.out).toMonoidHom).subgroupOf K := by
    have hh := coset_stabilizer G H K ω.out.out
    simpa only [Quotient.out_eq'] using hh
  simpa only [he, Subgroup.index] using hi

 def cuspOrbitPoint {G X : Type*} [Group G] [MulAction G X]
    (q : X) (a : G) : orbit G q := ⟨a⁻¹ • q, mem_orbit q a⁻¹⟩

 theorem coset_cusp_orbit_iff {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (q : X) (a b : G) :
    orbitRel (stabilizer G q) (G ⧸ H) (a : G ⧸ H) (b : G ⧸ H) ↔
      orbitRel H (orbit G q) (cuspOrbitPoint q a) (cuspOrbitPoint q b) := by
  rw [orbitRel_apply, mem_orbit_iff, orbitRel_apply, mem_subgroup_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨k,hk⟩
    change (k.val * b : G ⧸ H) = (a : G ⧸ H) at hk
    have hh := H.inv_mem (QuotientGroup.eq.mp hk)
    refine ⟨⟨a⁻¹ * k.val * b, ?_⟩, ?_⟩
    · convert hh using 1; group
    · change (a⁻¹ * k.val * b) • (b⁻¹ • q) = a⁻¹ • q
      rw [mul_smul, mul_smul, smul_inv_smul, k.property]
  · rintro ⟨h,hh⟩
    change h.val • (b⁻¹ • q) = a⁻¹ • q at hh
    have hk : (a * h.val * b⁻¹) • q = q := by
      rw [mul_smul, mul_smul, hh, smul_inv_smul]
    refine ⟨⟨a * h.val * b⁻¹, hk⟩, ?_⟩
    change ((a * h.val * b⁻¹) * b : G ⧸ H) = (a : G ⧸ H)
    have he : (a * h.val * b⁻¹) * b = a * h.val := by group
    rw [he, QuotientGroup.mk_mul_of_mem _ h.property]

 def cosetToCuspOrbit {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (q : X) :
    (G ⧸ H) → Quotient (orbitRel H (orbit G q)) :=
  Quotient.lift (fun a => Quotient.mk'' (cuspOrbitPoint q a)) (by
    intro a b hab
    apply Quotient.sound
    apply (coset_cusp_orbit_iff H q a b).mp
    apply orbitRel_apply.mpr
    apply mem_orbit_iff.mpr
    exact ⟨1, by simpa using (Quotient.sound hab : (a : G ⧸ H) = (b : G ⧸ H)).symm⟩)

 def cosetOrbitsToCuspOrbits {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (q : X) :
    Quotient (orbitRel (stabilizer G q) (G ⧸ H)) →
      Quotient (orbitRel H (orbit G q)) :=
  Quotient.lift (cosetToCuspOrbit H q) (by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a =>
      induction b using QuotientGroup.induction_on with | H b =>
        apply Quotient.sound
        exact (coset_cusp_orbit_iff H q a b).mp hab)

 noncomputable def cosetOrbitsEquivCuspOrbits {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (q : X) :
    Quotient (orbitRel (stabilizer G q) (G ⧸ H)) ≃
      Quotient (orbitRel H (orbit G q)) :=
  Equiv.ofBijective (cosetOrbitsToCuspOrbits H q) (by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h a =>
        induction b using Quotient.inductionOn with | h b =>
          induction a using QuotientGroup.induction_on with | H a =>
            induction b using QuotientGroup.induction_on with | H b =>
              apply Quotient.sound
              exact (coset_cusp_orbit_iff H q a b).mpr (Quotient.exact hab)
    · intro x
      induction x using Quotient.inductionOn with | h x =>
        obtain ⟨a,ha⟩ := mem_orbit_iff.mp x.property
        refine ⟨Quotient.mk'' ((a⁻¹ : G) : G ⧸ H), ?_⟩
        change Quotient.mk'' (cuspOrbitPoint q a⁻¹) = Quotient.mk'' x
        congr 1
        apply Subtype.ext
        simpa [cuspOrbitPoint] using ha)

private theorem cusp_index_transport {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) (q : X) (a : Δ) (τ : G) :
    (((Γ.subgroupOf Δ).map (MulAut.conj a).toMonoidHom).subgroupOf
      (stabilizer Δ q)).index =
    ((Γ ⊓ stabilizer G (a.val⁻¹ • q)).map
      (MulAut.conj (τ⁻¹ * a.val)).toMonoidHom).relIndex
      ((Δ ⊓ stabilizer G q).map (MulAut.conj τ⁻¹).toMonoidHom) := by
  have hs : (stabilizer Δ q).map Δ.subtype = Δ ⊓ stabilizer G q := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hsx⟩
      exact ⟨⟨x,hx⟩,hsx,rfl⟩
  have hg : ((Γ.subgroupOf Δ).map (MulAut.conj a).toMonoidHom).map Δ.subtype =
      Γ.map (MulAut.conj a.val).toMonoidHom := by
    rw [Subgroup.map_map]
    have he : Δ.subtype.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj a.val).toMonoidHom.comp Δ.subtype := by ext x; rfl
    rw [he, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h]
  change ((Γ.subgroupOf Δ).map (MulAut.conj a).toMonoidHom).relIndex (stabilizer Δ q) = _
  rw [← Subgroup.relIndex_map_map_of_injective _ _ Δ.subtype_injective, hg, hs]
  have ht : (Γ ⊓ stabilizer G (a.val⁻¹ • q)).map
      (MulAut.conj (τ⁻¹ * a.val)).toMonoidHom =
      ((Γ.map (MulAut.conj a.val).toMonoidHom) ⊓ stabilizer G q).map
        (MulAut.conj τ⁻¹).toMonoidHom := by
    have he : stabilizer G (a.val⁻¹ • q) =
        (stabilizer G q).map (MulAut.conj a.val⁻¹).toMonoidHom :=
      stabilizer_smul_eq_stabilizer_map_conj _ _
    have hi : (MulAut.conj a.val).toMonoidHom.comp
        (MulAut.conj a.val⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hh : (stabilizer G (a.val⁻¹ • q)).map
        (MulAut.conj a.val).toMonoidHom = stabilizer G q := by
      rw [he, Subgroup.map_map, hi, Subgroup.map_id]
    rw [← hh, ← Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,
      Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [ht, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj τ⁻¹).injective]
  rw [Subgroup.relIndex, Subgroup.relIndex]
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact (and_iff_left x.property.2).symm

open DedekindZetaZeroFree

 def actual_component_cusp_orbit_equiv
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    (V U : Level F ζ hζ) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (q : KPCuspArithmetic.Cusp F) :
    let Γ := KPCuspGenuineMonodromy.Component F ζ hζ V c
    let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U c
    Quotient (orbitRel (stabilizer Δ q) (Δ ⧸ Γ.subgroupOf Δ)) ≃
      Quotient (orbitRel (Γ.subgroupOf Δ) (orbit Δ q)) :=
  cosetOrbitsEquivCuspOrbits _ q

end CuspIndexAccounting

namespace ActualIndexPort
open MeasureTheory
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 def arithmetic_forget
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (h : Γ ≤ Δ) :
    KPCuspSiegel.OrbitQuotient F Γ → KPCuspSiegel.OrbitQuotient F Δ :=
  Quotient.lift (KPCuspSiegel.projection F Δ) (by
    intro x y hxy
    apply Quotient.sound
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨⟨g.val,h g.property⟩,hg⟩))

private theorem arithmetic_forget_measurable
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (h : Γ ≤ Δ) :
    Measurable (arithmetic_forget h) := by
  apply measurable_from_quotient.mpr
  exact measurable_quotient_mk''

private theorem subgroupOf_fundamental
    {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) {μ : Measure X} {E : Set X}
    (hE : IsFundamentalDomain Γ E μ) :
    IsFundamentalDomain (Γ.subgroupOf Δ) E μ := by
  have he := hE.preimage_of_equiv (MeasureTheory.MeasurePreserving.id μ).quasiMeasurePreserving
    (Subgroup.subgroupOfEquivOfLe h).symm.bijective (by intro g x; rfl)
  exact he

private theorem arithmetic_volume_index
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (h : Γ ≤ Δ)
    [(Γ.subgroupOf Δ).FiniteIndex]
    {E D : Set (KPFiniteCuspAtlas.SymmetricSpace F)}
    (hE : IsFundamentalDomain Γ E (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)))
    (hD : IsFundamentalDomain Δ D (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    Measure.map (arithmetic_forget h) (KPFiniteCuspAtlas.quotientVolume F Γ E) =
      (Γ.relIndex Δ : ℝ≥0∞) • KPFiniteCuspAtlas.quotientVolume F Δ D := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  letI : MeasurableConstSMul Δ (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  letI : SMulInvariantMeasure Δ (KPFiniteCuspAtlas.SymmetricSpace F) μ :=
    ⟨fun g _ hs => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measure_preimage
      hs.nullMeasurableSet⟩
  unfold KPFiniteCuspAtlas.quotientVolume
  rw [Measure.map_map (arithmetic_forget_measurable h)
    (show Measurable (KPCuspSiegel.projection F Γ) from measurable_quotient_mk'')]
  have hcomp : arithmetic_forget h ∘ KPCuspSiegel.projection F Γ =
      KPCuspSiegel.projection F Δ := rfl
  rw [hcomp]
  ext T hT
  have hm : Measurable (KPCuspSiegel.projection F Δ) := measurable_quotient_mk''
  rw [Measure.smul_apply, Measure.map_apply hm hT, Measure.map_apply hm hT,
    Measure.restrict_apply (hm hT), Measure.restrict_apply (hm hT)]
  have hi := NormOneTransition.IndexPort.integral_index μ (Γ.subgroupOf Δ)
    (subgroupOf_fundamental h hE) hD
    (((KPCuspSiegel.projection F Δ) ⁻¹' T).indicator (fun _ => (1 : ℝ≥0∞)))
    (by
      intro g x
      have hq : KPCuspSiegel.projection F Δ (g • x) = KPCuspSiegel.projection F Δ x := by
        apply Quotient.sound
        exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g,rfl⟩)
      simp only [Set.indicator, Set.mem_preimage, hq])
  simpa only [lintegral_indicator (hm hT), setLIntegral_one,
    Measure.restrict_apply (hm hT), Set.inter_comm, Subgroup.relIndex, smul_eq_mul] using hi

end ActualIndexPort

namespace ShiftedIndexPort
open MeasureTheory
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 def arithmetic_transition
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (δ : KPCuspArithmetic.PGL2 F)
    (h : Γ.map (MulAut.conj δ).toMonoidHom ≤ Δ) :
    KPCuspSiegel.OrbitQuotient F Γ → KPCuspSiegel.OrbitQuotient F Δ :=
  Quotient.lift (fun x => KPCuspSiegel.projection F Δ (δ • x)) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine MulAction.mem_orbit_iff.mpr ⟨⟨δ * g.val * δ⁻¹, h ⟨g.val,g.property,rfl⟩⟩,?_⟩
    change (δ * g.val * δ⁻¹) • (δ • y) = δ • x
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (fun z => δ • z) hg)

private theorem arithmetic_transition_measurable
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (δ : KPCuspArithmetic.PGL2 F)
    (h : Γ.map (MulAut.conj δ).toMonoidHom ≤ Δ) :
    Measurable (arithmetic_transition δ h) := by
  apply measurable_from_quotient.mpr
  exact measurable_quotient_mk''.comp
    (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F δ).measurable

private theorem conjugated_fundamental
    {Γ : Subgroup (KPCuspArithmetic.PGL2 F)} (δ : KPCuspArithmetic.PGL2 F)
    {E : Set (KPFiniteCuspAtlas.SymmetricSpace F)}
    (hE : IsFundamentalDomain Γ E (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    IsFundamentalDomain (Γ.map (MulAut.conj δ).toMonoidHom)
      ((fun x => δ • x) '' E) (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
  let e := (MulAut.conj δ).subgroupMap Γ
  refine hE.image_of_equiv (MulAction.toPerm δ)
    (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F δ⁻¹).quasiMeasurePreserving
    e.symm.toEquiv ?_
  intro g x
  change δ • ((e.symm g).val • x) = g.val • (δ • x)
  have he : δ * (e.symm g).val * δ⁻¹ = g.val :=
    congrArg Subtype.val (e.apply_symm_apply g)
  rw [← he]
  simp only [mul_smul, inv_smul_smul]

private theorem rational_action_restrict
    (δ : KPCuspArithmetic.PGL2 F) (E : Set (KPFiniteCuspAtlas.SymmetricSpace F)) :
    Measure.map (fun x => δ • x)
      ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict E) =
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
        ((fun x => δ • x) '' E) := by
  letI : MeasurableConstSMul (KPCuspArithmetic.PGL2 F) (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g).measurable⟩
  exact ((KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F δ).restrict_image_emb
    (measurableEmbedding_const_smul δ) E).map_eq

private theorem conjugated_quotient_volume
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (δ : KPCuspArithmetic.PGL2 F)
    (E : Set (KPFiniteCuspAtlas.SymmetricSpace F)) :
    Measure.map (arithmetic_transition δ (le_refl (Γ.map (MulAut.conj δ).toMonoidHom)))
      (KPFiniteCuspAtlas.quotientVolume F Γ E) =
      KPFiniteCuspAtlas.quotientVolume F (Γ.map (MulAut.conj δ).toMonoidHom)
        ((fun x => δ • x) '' E) := by
  unfold KPFiniteCuspAtlas.quotientVolume
  rw [Measure.map_map (arithmetic_transition_measurable _ _)
    (show Measurable (KPCuspSiegel.projection F Γ) from measurable_quotient_mk''),
    ← rational_action_restrict δ E,
    Measure.map_map
      (show Measurable (KPCuspSiegel.projection F (Γ.map (MulAut.conj δ).toMonoidHom))
        from measurable_quotient_mk'')
      (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F δ).measurable]
  rfl

private theorem arithmetic_transition_volume_index
    {Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)} (δ : KPCuspArithmetic.PGL2 F)
    (h : Γ.map (MulAut.conj δ).toMonoidHom ≤ Δ)
    [((Γ.map (MulAut.conj δ).toMonoidHom).subgroupOf Δ).FiniteIndex]
    {E D : Set (KPFiniteCuspAtlas.SymmetricSpace F)}
    (hE : IsFundamentalDomain Γ E (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)))
    (hD : IsFundamentalDomain Δ D (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    Measure.map (arithmetic_transition δ h) (KPFiniteCuspAtlas.quotientVolume F Γ E) =
      ((Γ.map (MulAut.conj δ).toMonoidHom).relIndex Δ : ℝ≥0∞) •
        KPFiniteCuspAtlas.quotientVolume F Δ D := by
  have he : arithmetic_transition δ h = ActualIndexPort.arithmetic_forget h ∘
      arithmetic_transition δ (le_refl (Γ.map (MulAut.conj δ).toMonoidHom)) := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => rfl
  rw [he, ← Measure.map_map (ActualIndexPort.arithmetic_forget_measurable h)
    (arithmetic_transition_measurable δ _), conjugated_quotient_volume]
  exact ActualIndexPort.arithmetic_volume_index h (conjugated_fundamental δ hE) hD

private theorem actual_shifted_component_volume_index
    (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u)
    {E D : Set (KPFiniteCuspAtlas.SymmetricSpace F)}
    (hE : IsFundamentalDomain (KPCuspGenuineMonodromy.Component F ζ hζ V c) E
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)))
    (hD : IsFundamentalDomain (KPCuspGenuineMonodromy.Component F ζ hζ U g) D
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))) :
    Measure.map (arithmetic_transition δ (AllLevelGeometry.actual_component_conjugate h δ ε u hg))
      (KPFiniteCuspAtlas.quotientVolume F (KPCuspGenuineMonodromy.Component F ζ hζ V c) E) =
      (((KPCuspGenuineMonodromy.Component F ζ hζ V c).map (MulAut.conj δ).toMonoidHom).relIndex
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) : ℝ≥0∞) •
      KPFiniteCuspAtlas.quotientVolume F (KPCuspGenuineMonodromy.Component F ζ hζ U g) D := by
  letI := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
    (FiniteIndexContinuation.component_conjugate_finite_relindex V U δ ε u hg)
  exact arithmetic_transition_volume_index δ
    (AllLevelGeometry.actual_component_conjugate h δ ε u hg) hE hD

private theorem actual_shifted_component_commutes
    (P : SphericalTransport F ζ hζ) (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    {c g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hg : g = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u)
    (x : KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ V c)) :
    P.forget V U h (KPFiniteCuspAtlas.componentMap F ζ hζ V c x) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U g
        (arithmetic_transition δ (AllLevelGeometry.actual_component_conjugate h δ ε u hg) x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change P.forget V U h (Quotient.mk _ (x,c)) = Quotient.mk _ (δ • x,g)
    rw [P.forget_formula]
    exact Quotient.sound ⟨δ,ε,u,rfl,hg⟩

private theorem component_map_measurable
    (U : Level F ζ hζ) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Measurable (KPFiniteCuspAtlas.componentMap F ζ hζ U c) := by
  apply measurable_from_quotient.mpr
  exact (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)).measurable

private theorem actual_weighted_component_pushforward
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : GeometricDisintegration AV R P)
    (i : Fin AV.componentCount) (k : Fin AU.componentCount)
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : AU.representative k = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative i * u) :
    Measure.map (P.forget V U h)
      ((sphericalMeasure F ζ hζ R P V).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i)))) =
      (DV.componentWeight i *
        (((KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i)).map
          (MulAut.conj δ).toMonoidHom).relIndex
            (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)) : ℝ≥0∞)) •
      Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k))
        (KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k))
          (AU.cuspAtlas k).fundamentalDomain) := by
  have hfine := component_map_measurable V (AV.representative i)
  have hcoarse := component_map_measurable U (AU.representative k)
  have hforget := (P.forget_continuous V U h).measurable
  rw [DV.component_measure i, Measure.map_smul _ hforget.aemeasurable,
    Measure.map_map hforget hfine]
  have he : P.forget V U h ∘ KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k) ∘
        arithmetic_transition δ (AllLevelGeometry.actual_component_conjugate h δ ε u hc) := by
    funext x
    exact actual_shifted_component_commutes P V U h δ ε u hc x
  rw [he, ← Measure.map_map hcoarse (arithmetic_transition_measurable δ _),
    actual_shifted_component_volume_index V U h δ ε u hc
      (AV.cuspAtlas i).isFundamentalDomain (AU.cuspAtlas k).isFundamentalDomain,
    Measure.map_smul _ hcoarse.aemeasurable, smul_smul]

 def component_label
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (x : Spherical F ζ hζ U) :
    Fin A.componentCount := (A.components.symm x).1

private theorem component_label_formula
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount)
    (x : KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))) :
    component_label A (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) x) = i := by
  rw [← A.components_formula i x]
  simp [component_label]

private theorem component_range_disjoint
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Pairwise (fun i j : Fin A.componentCount => Disjoint
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)))
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨y,rfl⟩ ⟨z,hz⟩
  have he := congrArg (component_label A) hz
  rw [component_label_formula, component_label_formula] at he
  exact hij he.symm

private theorem matched_component_preimage
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (m : Fin AV.componentCount → Fin AU.componentCount)
    (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
    (ε : Fin AV.componentCount → rootsOfUnity 3 F)
    (u : Fin AV.componentCount → U.toOpenSubgroup)
    (hc : ∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
      KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i)
    (k : Fin AU.componentCount) :
    P.forget V U h ⁻¹' Set.range
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k)) =
      ⋃ i : {i : Fin AV.componentCount // m i = k},
        Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i.val)) := by
  ext x
  obtain ⟨⟨i,z⟩,rfl⟩ := AV.components.surjective x
  rw [AV.components_formula]
  constructor
  · rintro ⟨y,hy⟩
    have he := congrArg (component_label AU) hy
    rw [actual_shifted_component_commutes P V U h (δ i) (ε i) (u i) (hc i) z,
      component_label_formula, component_label_formula] at he
    exact Set.mem_iUnion.mpr ⟨⟨i,he.symm⟩, ⟨z,rfl⟩⟩
  · intro hx
    obtain ⟨⟨j,hj⟩,w,hw⟩ := Set.mem_iUnion.mp hx
    have he := congrArg (component_label AV) hw
    rw [component_label_formula, component_label_formula] at he
    change j = i at he
    subst j
    change P.forget V U h (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i) z) ∈
      Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k))
    rw [actual_shifted_component_commutes P V U h (δ i) (ε i) (u i) (hc i) z]
    rw [← hj]
    exact Set.mem_range_self _

private theorem matched_component_restriction_sum
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (m : Fin AV.componentCount → Fin AU.componentCount)
    (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
    (ε : Fin AV.componentCount → rootsOfUnity 3 F)
    (u : Fin AV.componentCount → U.toOpenSubgroup)
    (hc : ∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
      KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i)
    (k : Fin AU.componentCount) :
    (∑ i : {i : Fin AV.componentCount // m i = k},
      Measure.map (P.forget V U h) ((sphericalMeasure F ζ hζ R P V).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i.val))))) =
    (sphericalMeasure F ζ hζ R P U).restrict
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k))) := by
  have hf := (P.forget_continuous V U h).measurable
  rw [← spherical_measure_forget R P V U h,
    Measure.restrict_map hf (ComponentFiber.component_range_clopen AU k).isOpen.measurableSet,
    matched_component_preimage P h AV AU m δ ε u hc k]
  have hd : Pairwise (fun i j : {i : Fin AV.componentCount // m i = k} => Disjoint
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative i.val)))
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ V (AV.representative j.val)))) := by
    intro i j hij
    exact component_range_disjoint AV (by intro he; exact hij (Subtype.ext he))
  rw [Measure.restrict_iUnion hd
    (fun i => (ComponentFiber.component_range_clopen AV i.val).isOpen.measurableSet),
    Measure.sum_fintype, Measure.map_finset_sum' hf.aemeasurable]

private theorem actual_component_measure_balance
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P) :
    ∃ (m : Fin AV.componentCount → Fin AU.componentCount)
      (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
      (ε : Fin AV.componentCount → rootsOfUnity 3 F)
      (u : Fin AV.componentCount → U.toOpenSubgroup),
      (∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
        KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i) ∧
      ∀ k : Fin AU.componentCount,
        (∑ i : {i : Fin AV.componentCount // m i = k}, DV.componentWeight i.val *
          (((KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i.val)).map
            (MulAut.conj (δ i.val)).toMonoidHom).relIndex
            (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)) : ℝ≥0∞)) •
          Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k))
            (KPFiniteCuspAtlas.quotientVolume F
              (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k))
              (AU.cuspAtlas k).fundamentalDomain) =
        DU.componentWeight k •
          Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (AU.representative k))
            (KPFiniteCuspAtlas.quotientVolume F
              (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k))
              (AU.cuspAtlas k).fundamentalDomain) := by
  choose m δ ε u hc using fun i => AllLevelGeometry.actual_component_matching AU (AV.representative i)
  refine ⟨m,δ,ε,u,hc,?_⟩
  intro k
  rw [Finset.sum_smul]
  have hs := matched_component_restriction_sum R P h AV AU m δ ε u hc k
  rw [DU.component_measure k] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro i _
  rcases i with ⟨i,hi⟩
  change m i = k at hi
  subst k
  exact (actual_weighted_component_pushforward R P h AV AU DV i (m i)
    (δ i) (ε i) (u i) (hc i)).symm

private theorem radial_tail_mass (d : ℕ) (hd : 0 < d) (T : ℝ) :
    0 < (KPCuspCharts.radialMeasure d) (Set.Ioi T) ∧
      (KPCuspCharts.radialMeasure d) (Set.Ioi T) < ⊤ := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * (d : ℝ) * t))) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_const).mul continuous_id)).measurable.ennreal_ofReal
  rw [KPCuspCharts.radialMeasure, withDensity_apply _ measurableSet_Ioi]
  constructor
  · rw [setLIntegral_pos_iff hm]
    have hs : Function.support (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * (d : ℝ) * t))) = Set.univ := by
      ext t
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    rw [hs, Set.univ_inter]
    exact isOpen_Ioi.measure_pos volume (Set.nonempty_Ioi)
  · exact (integrableOn_exp_mul_Ioi (show (-2 * (d : ℝ)) < 0 by
      have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      linarith) T).lintegral_lt_top

private theorem component_positive_finite_test
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount) :
    ∃ E : Set (Spherical F ζ hζ U),
      0 < (Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain)) E ∧
      (Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain)) E < ⊤ := by
  let a : Fin (A.cuspAtlas i).cuspCount := ⟨0,(A.cuspAtlas i).positive_cuspCount⟩
  let j : CuspIndex A := ⟨i,a⟩
  let G := Geometry A j
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)
  let ν := KPFiniteCuspAtlas.quotientVolume F Γ (A.cuspAtlas i).fundamentalDomain
  let S := KPFiniteCuspAtlas.endSet F Γ ((A.cuspAtlas i).representative a) A.threshold
  let ρ := Measure.comap (Subtype.val : Set.Ioi A.threshold → ℝ)
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))
  have hr : ρ Set.univ = (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) (Set.Ioi A.threshold) := by
    rw [show ρ = Measure.comap (Subtype.val : Set.Ioi A.threshold → ℝ)
      (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) from rfl,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply, Set.image_univ,
      Subtype.range_coe]
  obtain ⟨hrp,hrf⟩ := radial_tail_mass (KPCuspLogShape.dimension F) G.positive_dimension A.threshold
  have hmass : ν S = G.sectionMeasure Set.univ * ρ Set.univ := by
    have he := RadialIntegrationSteps.end_section_lintegral A j A.threshold le_rfl
      (fun _ => (1 : ℝ≥0∞)) measurable_const
    simpa only [setLIntegral_one, lintegral_one, lintegral_const,
      Measure.restrict_apply_univ, mul_comm] using he
  have hs : MeasurableSet S := by
    apply IsOpen.measurableSet
    change IsOpen (KPFiniteCuspAtlas.endSet F Γ ((A.cuspAtlas i).representative a) A.threshold)
    rw [← A.common_threshold i]
    exact (A.cuspAtlas i).open_ends a
  let c := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)
  have hec : c = A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  have hci : Function.Injective c := by
    rw [hec]
    exact A.components.injective.comp (by intro x y he; simpa using he)
  have hE : MeasurableSet (c '' S) := by
    have hS : IsOpen S := by
      change IsOpen (KPFiniteCuspAtlas.endSet F Γ ((A.cuspAtlas i).representative a) A.threshold)
      rw [← A.common_threshold i]
      exact (A.cuspAtlas i).open_ends a
    rw [hec, Set.image_comp]
    exact (A.components.isOpenMap _ (isOpenMap_sigmaMk _ hS)).measurableSet
  refine ⟨c '' S, ?_⟩
  have hv : (Measure.map c ν) (c '' S) = ν S := by
    rw [Measure.map_apply (component_map_measurable U _) hE, Set.preimage_image_eq _ hci]
  change 0 < (Measure.map c ν) (c '' S) ∧ (Measure.map c ν) (c '' S) < ⊤
  rw [hv, hmass, hr]
  exact ⟨ENNReal.mul_pos G.positive_sectionMeasure hrp.ne',
    ENNReal.mul_lt_top G.finite_sectionMeasure.measure_univ_lt_top hrf⟩

private theorem actual_component_weight_balance
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P) :
    ∃ (m : Fin AV.componentCount → Fin AU.componentCount)
      (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
      (ε : Fin AV.componentCount → rootsOfUnity 3 F)
      (u : Fin AV.componentCount → U.toOpenSubgroup),
      (∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
        KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i) ∧
      ∀ k : Fin AU.componentCount,
        (∑ i : {i : Fin AV.componentCount // m i = k}, DV.componentWeight i.val *
          (((KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i.val)).map
            (MulAut.conj (δ i.val)).toMonoidHom).relIndex
            (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)) : ℝ≥0∞)) =
        DU.componentWeight k := by
  obtain ⟨m,δ,ε,u,hc,hbalance⟩ := actual_component_measure_balance R P h AV AU DV DU
  refine ⟨m,δ,ε,u,hc,?_⟩
  intro k
  obtain ⟨E,hp,hf⟩ := component_positive_finite_test AU k
  exact ComponentNormalization.smul_weight_unique _ E hp.ne' hf.ne (hbalance k)

end ShiftedIndexPort

namespace ActualCuspLabelPort
open MulAction
open scoped ENNReal

 def labelToOrbit {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} {n : ℕ} (c : Fin n → X) (q : X) :
    {a : Fin n // c a ∈ orbit Δ q} →
      Quotient (orbitRel (Γ.subgroupOf Δ) (orbit Δ q)) :=
  fun a => Quotient.mk'' ⟨c a.val,a.property⟩

 theorem labelToOrbit_bijective {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Γ), g • c a = x)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Γ, g • c a ≠ c b) (q : X) :
    Function.Bijective (labelToOrbit (Γ := Γ) (Δ := Δ) c q) := by
  constructor
  · intro a b hab
    have hr := Quotient.exact hab
    obtain ⟨g,hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hr)
    have he : (⟨g.val.val,g.property⟩ : Γ) • c b.val = c a.val :=
      congrArg Subtype.val hg
    apply Subtype.ext
    by_contra hn
    exact hin b.val a.val (Ne.symm hn) ⟨g.val.val,g.property⟩ he
  · intro x
    induction x using Quotient.inductionOn with
    | h x =>
      obtain ⟨a,g,hg⟩ := hex x.val
      have ha : c a ∈ orbit Δ q := by
        have he : c a = (⟨g.val,h g.property⟩ : Δ)⁻¹ • x.val := by
          rw [← hg]
          exact (inv_smul_smul (⟨g.val,h g.property⟩ : Δ) (c a)).symm
        rw [he]
        obtain ⟨v,hv⟩ := mem_orbit_iff.mp x.property
        exact mem_orbit_iff.mpr ⟨(⟨g.val,h g.property⟩ : Δ)⁻¹ * v,
          by rw [mul_smul,hv]⟩
      refine ⟨⟨a,ha⟩, ?_⟩
      apply Quotient.sound
      apply orbitRel_apply.mpr
      apply mem_orbit_iff.mpr
      refine ⟨⟨⟨g.val,h g.property⟩⁻¹,Γ.inv_mem g.property⟩, ?_⟩
      apply Subtype.ext
      change g.val⁻¹ • x.val = c a
      rw [← hg]
      exact inv_smul_smul g.val (c a)

 def labelsEquivCosetOrbits {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Γ), g • c a = x)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Γ, g • c a ≠ c b) (q : X) :
    {a : Fin n // c a ∈ orbit Δ q} ≃
      Quotient (orbitRel (stabilizer Δ q) (Δ ⧸ Γ.subgroupOf Δ)) :=
  (Equiv.ofBijective _ (labelToOrbit_bijective h c hex hin q)).trans
    (CuspIndexAccounting.cosetOrbitsEquivCuspOrbits (Γ.subgroupOf Δ) q).symm

private theorem degree_smul {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) (g : Γ) (x : X) :
    (Γ ⊓ stabilizer G (g.val • x)).relIndex (Δ ⊓ stabilizer G (g.val • x)) =
      (Γ ⊓ stabilizer G x).relIndex (Δ ⊓ stabilizer G x) := by
  have hΓ : Γ.map (MulAut.conj g.val).toMonoidHom = Γ :=
    FiniteIndexContinuation.conj_member_eq Γ g.val g.property
  have hΔ : Δ.map (MulAut.conj g.val).toMonoidHom = Δ :=
    FiniteIndexContinuation.conj_member_eq Δ g.val (h g.property)
  have hΓs : Γ ⊓ stabilizer G (g.val • x) =
      (Γ ⊓ stabilizer G x).map (MulAut.conj g.val).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g.val).injective, hΓ,
      stabilizer_smul_eq_stabilizer_map_conj]
  have hΔs : Δ ⊓ stabilizer G (g.val • x) =
      (Δ ⊓ stabilizer G x).map (MulAut.conj g.val).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g.val).injective, hΔ,
      stabilizer_smul_eq_stabilizer_map_conj]
  rw [hΓs,hΔs,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g.val).injective]

private theorem coset_degree {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) (q : X) (a : Δ) :
    (((Γ.subgroupOf Δ).map (MulAut.conj a).toMonoidHom).subgroupOf
      (stabilizer Δ q)).index =
    (Γ ⊓ stabilizer G (a.val⁻¹ • q)).relIndex
      (Δ ⊓ stabilizer G (a.val⁻¹ • q)) := by
  have hi := CuspIndexAccounting.cusp_index_transport h q a (1 : G)
  have hd : (Δ ⊓ stabilizer G (a.val⁻¹ • q)).map
      (MulAut.conj a.val).toMonoidHom = Δ ⊓ stabilizer G q := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,
      FiniteIndexContinuation.conj_member_eq Δ a.val a.property]
    congr 1
    rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map]
    have he : (MulAut.conj a.val).toMonoidHom.comp
        (MulAut.conj a.val⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [he, Subgroup.map_id]
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x; simp
  simp only [inv_one, one_mul, hid, Subgroup.map_id] at hi
  rw [← hd, Subgroup.relIndex_map_map_of_injective _ _
    (MulAut.conj a.val).injective] at hi
  exact hi

private theorem coset_orbit_formula {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (q : X)
    (ω : Quotient (orbitRel (stabilizer Δ q) (Δ ⧸ Γ.subgroupOf Δ))) :
    CuspIndexAccounting.cosetOrbitsEquivCuspOrbits (Γ.subgroupOf Δ) q ω =
      Quotient.mk'' (CuspIndexAccounting.cuspOrbitPoint q ω.out.out) := by
  conv_lhs => rw [← Quotient.out_eq ω]
  change CuspIndexAccounting.cosetToCuspOrbit (Γ.subgroupOf Δ) q ω.out = _
  conv_lhs => rw [← Quotient.out_eq ω.out]
  rfl

private theorem labels_degree {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Γ), g • c a = x)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Γ, g • c a ≠ c b) (q : X)
    (a : {a : Fin n // c a ∈ orbit Δ q}) :
    let ω := labelsEquivCosetOrbits h c hex hin q a
    (Γ ⊓ stabilizer G (c a.val)).relIndex (Δ ⊓ stabilizer G (c a.val)) =
      (((Γ.subgroupOf Δ).map (MulAut.conj ω.out.out).toMonoidHom).subgroupOf
        (stabilizer Δ q)).index := by
  let ω := labelsEquivCosetOrbits h c hex hin q a
  have he : CuspIndexAccounting.cosetOrbitsEquivCuspOrbits (Γ.subgroupOf Δ) q ω =
      labelToOrbit (Γ := Γ) (Δ := Δ) c q a := by
    exact (CuspIndexAccounting.cosetOrbitsEquivCuspOrbits (Γ.subgroupOf Δ) q).apply_symm_apply _
  rw [coset_orbit_formula] at he
  obtain ⟨g,hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact he))
  have hp : g.val.val • c a.val = ω.out.out.val⁻¹ • q := congrArg Subtype.val hg
  change _ = (((Γ.subgroupOf Δ).map (MulAut.conj ω.out.out).toMonoidHom).subgroupOf
    (stabilizer Δ q)).index
  rw [coset_degree h q ω.out.out, ← hp]
  exact (degree_smul h ⟨g.val.val,g.property⟩ (c a.val)).symm

private theorem sum_labels_degree {G X : Type*} [Group G] [MulAction G X]
    {Γ Δ : Subgroup G} (h : Γ ≤ Δ) [(Γ.subgroupOf Δ).FiniteIndex]
    {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Γ), g • c a = x)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Γ, g • c a ≠ c b) (q : X) :
    (∑ a : {a : Fin n // c a ∈ orbit Δ q},
      (Γ ⊓ stabilizer G (c a.val)).relIndex (Δ ⊓ stabilizer G (c a.val))) =
        Γ.relIndex Δ := by
  letI : Fintype (Quotient (orbitRel (stabilizer Δ q) (Δ ⧸ Γ.subgroupOf Δ))) :=
    Fintype.ofFinite _
  calc
    _ = ∑ ω : Quotient (orbitRel (stabilizer Δ q) (Δ ⧸ Γ.subgroupOf Δ)),
        (((Γ.subgroupOf Δ).map (MulAut.conj ω.out.out).toMonoidHom).subgroupOf
          (stabilizer Δ q)).index :=
      Fintype.sum_equiv (labelsEquivCosetOrbits h c hex hin q) _ _
        (labels_degree h c hex hin q)
    _ = Γ.relIndex Δ := CuspIndexAccounting.sum_coset_stabilizer_indices
      Δ (Γ.subgroupOf Δ) (stabilizer Δ q)

private theorem shifted_exhaustive {G X : Type*} [Group G] [MulAction G X]
    (Γ : Subgroup G) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Γ), g • c a = x) (δ : G) :
    ∀ x : X, ∃ (a : Fin n) (g : Γ.map (MulAut.conj δ).toMonoidHom),
      g • (δ • c a) = x := by
  intro x
  obtain ⟨a,g,hg⟩ := hex (δ⁻¹ • x)
  refine ⟨a,⟨δ * g.val * δ⁻¹,⟨g.val,g.property,rfl⟩⟩,?_⟩
  change (δ * g.val * δ⁻¹) • (δ • c a) = x
  rw [mul_smul,mul_smul,inv_smul_smul]
  change δ • (g • c a) = x
  rw [hg,smul_inv_smul]

private theorem shifted_inequivalent {G X : Type*} [Group G] [MulAction G X]
    (Γ : Subgroup G) {n : ℕ} (c : Fin n → X)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Γ, g • c a ≠ c b) (δ : G) :
    ∀ a b : Fin n, a ≠ b → ∀ g : Γ.map (MulAut.conj δ).toMonoidHom,
      g • (δ • c a) ≠ δ • c b := by
  intro a b hab g he
  obtain ⟨v,hv,hg⟩ := g.property
  have hx : (δ * v * δ⁻¹) • (δ • c a) = δ • c b := by
    change g.val • (δ • c a) = δ • c b at he
    change δ * v * δ⁻¹ = g.val at hg
    rwa [hg]
  rw [mul_smul,mul_smul,inv_smul_smul] at hx
  exact hin a b hab ⟨v,hv⟩ (MulAction.injective δ hx)

private theorem actual_shifted_cusp_index_sum
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin AV.componentCount) (k : Fin AU.componentCount)
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : AU.representative k = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative i * u)
    (q : KPCuspArithmetic.Cusp F) :
    let Γ := (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i)).map
      (MulAut.conj δ).toMonoidHom
    let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)
    (∑ a : {a : Fin (AV.cuspAtlas i).cuspCount // δ • (AV.cuspAtlas i).cusp a ∈ orbit Δ q},
      (Γ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • (AV.cuspAtlas i).cusp a.val)).relIndex
        (Δ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • (AV.cuspAtlas i).cusp a.val))) =
          Γ.relIndex Δ := by
  let Γ₀ := KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i)
  let Γ := Γ₀.map (MulAut.conj δ).toMonoidHom
  let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)
  letI : (Γ.subgroupOf Δ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp
    (FiniteIndexContinuation.component_conjugate_finite_relindex V U δ ε u hc)
  exact sum_labels_degree (AllLevelGeometry.actual_component_conjugate h δ ε u hc)
    (fun a => δ • (AV.cuspAtlas i).cusp a)
    (shifted_exhaustive Γ₀ (AV.cuspAtlas i).cusp (AV.cuspAtlas i).exhaustive δ)
    (shifted_inequivalent Γ₀ (AV.cuspAtlas i).cusp (AV.cuspAtlas i).inequivalent δ) q

 theorem actual_transition_degree
    {F : Type} [Field F] (Γ₀ Δ : Subgroup (KPCuspArithmetic.PGL2 F))
    (f q : KPCuspArithmetic.Cusp F) (δ σ τ : KPCuspArithmetic.PGL2 F)
    (η : Δ) (hq : η.val • q = δ • f) :
    ((KPCuspArithmetic.conjugatedStabilizer F Γ₀ f σ).map
      (MulAut.conj (τ⁻¹ * (η.val⁻¹ * δ) * σ)).toMonoidHom).relIndex
        (KPCuspArithmetic.conjugatedStabilizer F Δ q τ) =
    ((Γ₀.map (MulAut.conj δ).toMonoidHom) ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • f)).relIndex
      (Δ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • f)) := by
  let Γ := Γ₀.map (MulAut.conj δ).toMonoidHom
  have hs : ((KPCuspArithmetic.conjugatedStabilizer F Γ₀ f σ).map
      (MulAut.conj (τ⁻¹ * (η.val⁻¹ * δ) * σ)).toMonoidHom) =
      ((Γ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • f)).map
        (MulAut.conj η.val⁻¹).toMonoidHom).map (MulAut.conj τ⁻¹).toMonoidHom := by
    unfold KPCuspArithmetic.conjugatedStabilizer
    have he : Γ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • f) =
        (Γ₀ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) f).map (MulAut.conj δ).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj δ).injective,
        stabilizer_smul_eq_stabilizer_map_conj]
    rw [he,Subgroup.map_map,Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
    group
  have ht : KPCuspArithmetic.conjugatedStabilizer F Δ q τ =
      ((Δ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • f)).map
        (MulAut.conj η.val⁻¹).toMonoidHom).map (MulAut.conj τ⁻¹).toMonoidHom := by
    unfold KPCuspArithmetic.conjugatedStabilizer
    congr 1
    rw [Subgroup.map_inf _ _ _ (MulAut.conj η.val⁻¹).injective,
      FiniteIndexContinuation.conj_member_eq Δ η.val⁻¹ (Δ.inv_mem η.property)]
    rw [← stabilizer_smul_eq_stabilizer_map_conj,← hq,inv_smul_smul]
  rw [hs,ht,Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj τ⁻¹).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj η.val⁻¹).injective]

 def cuspCorrection {G X : Type*} [Group G] [MulAction G X]
    (Δ : Subgroup G) (q x : X) (hx : x ∈ orbit Δ q) : Δ :=
  (mem_orbit_iff.mp hx).choose

 theorem cuspCorrection_formula {G X : Type*} [Group G] [MulAction G X]
    (Δ : Subgroup G) (q x : X) (hx : x ∈ orbit Δ q) :
    (cuspCorrection Δ q x hx).val • q = x :=
  (mem_orbit_iff.mp hx).choose_spec

private theorem actual_pinned_cusp_index_sum
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin AV.componentCount) (k : Fin AU.componentCount)
    (δ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : AU.representative k = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * AV.representative i * u)
    (a : Fin (AU.cuspAtlas k).cuspCount) :
    let Γ₀ := KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i)
    let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)
    let q := (AU.cuspAtlas k).cusp a
    let τ := (AU.cuspAtlas k).representative a
    (∑ b : {b : Fin (AV.cuspAtlas i).cuspCount // δ • (AV.cuspAtlas i).cusp b ∈ orbit Δ q},
      ((KPCuspArithmetic.conjugatedStabilizer F Γ₀
        ((AV.cuspAtlas i).cusp b.val) ((AV.cuspAtlas i).representative b.val)).map
          (MulAut.conj (τ⁻¹ * ((cuspCorrection Δ q
            (δ • (AV.cuspAtlas i).cusp b.val) b.property).val⁻¹ * δ) *
              (AV.cuspAtlas i).representative b.val)).toMonoidHom).relIndex
        (KPCuspArithmetic.conjugatedStabilizer F Δ q τ)) =
      (Γ₀.map (MulAut.conj δ).toMonoidHom).relIndex Δ := by
  let Γ₀ := KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i)
  let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)
  let q := (AU.cuspAtlas k).cusp a
  let τ := (AU.cuspAtlas k).representative a
  calc
    _ = ∑ b : {b : Fin (AV.cuspAtlas i).cuspCount // δ • (AV.cuspAtlas i).cusp b ∈ orbit Δ q},
        ((Γ₀.map (MulAut.conj δ).toMonoidHom) ⊓ stabilizer (KPCuspArithmetic.PGL2 F)
          (δ • (AV.cuspAtlas i).cusp b.val)).relIndex
            (Δ ⊓ stabilizer (KPCuspArithmetic.PGL2 F) (δ • (AV.cuspAtlas i).cusp b.val)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact actual_transition_degree Γ₀ Δ ((AV.cuspAtlas i).cusp b.val) q δ
        ((AV.cuspAtlas i).representative b.val) τ
        (cuspCorrection Δ q (δ • (AV.cuspAtlas i).cusp b.val) b.property)
        (cuspCorrection_formula Δ q (δ • (AV.cuspAtlas i).cusp b.val) b.property)
    _ = _ := actual_shifted_cusp_index_sum h AV AU i k δ ε u hc q

 theorem actual_weighted_pinned_cusp_degree_balance
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P) :
    ∃ (m : Fin AV.componentCount → Fin AU.componentCount)
      (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
      (ε : Fin AV.componentCount → rootsOfUnity 3 F)
      (u : Fin AV.componentCount → U.toOpenSubgroup),
      (∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
        KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i) ∧
      ∀ (k : Fin AU.componentCount) (a : Fin (AU.cuspAtlas k).cuspCount),
        let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)
        let q := (AU.cuspAtlas k).cusp a
        let τ := (AU.cuspAtlas k).representative a
        (∑ i : {i : Fin AV.componentCount // m i = k},
          ∑ b : {b : Fin (AV.cuspAtlas i.val).cuspCount //
                δ i.val • (AV.cuspAtlas i.val).cusp b ∈ orbit Δ q},
            DV.componentWeight i.val *
            (((KPCuspArithmetic.conjugatedStabilizer F
              (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i.val))
              ((AV.cuspAtlas i.val).cusp b.val) ((AV.cuspAtlas i.val).representative b.val)).map
                (MulAut.conj (τ⁻¹ * ((cuspCorrection Δ q
                  (δ i.val • (AV.cuspAtlas i.val).cusp b.val) b.property).val⁻¹ * δ i.val) *
                    (AV.cuspAtlas i.val).representative b.val)).toMonoidHom).relIndex
              (KPCuspArithmetic.conjugatedStabilizer F Δ q τ) : ℝ≥0∞)) =
          DU.componentWeight k := by
  obtain ⟨m,δ,ε,u,hc,hbalance⟩ := ShiftedIndexPort.actual_component_weight_balance R P h AV AU DV DU
  refine ⟨m,δ,ε,u,hc,?_⟩
  intro k a
  calc
    _ = ∑ i : {i : Fin AV.componentCount // m i = k}, DV.componentWeight i.val *
        (((KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative i.val)).map
          (MulAut.conj (δ i.val)).toMonoidHom).relIndex
            (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k)) : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, ← Nat.cast_sum]
      congr 2
      exact actual_pinned_cusp_index_sum h AV AU i.val k (δ i.val) (ε i.val) (u i.val)
        (by simpa only [i.property] using hc i.val) a
    _ = _ := hbalance k

 def coarseLabel {G X : Type*} [Group G] [MulAction G X]
    (Δ : Subgroup G) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Δ), g • c a = x) (x : X) : Fin n :=
  (hex x).choose

 theorem coarseLabel_mem {G X : Type*} [Group G] [MulAction G X]
    (Δ : Subgroup G) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Δ), g • c a = x) (x : X) :
    x ∈ orbit Δ (c (coarseLabel Δ c hex x)) :=
  mem_orbit_iff.mpr (hex x).choose_spec

private theorem coarseLabel_eq_iff {G X : Type*} [Group G] [MulAction G X]
    (Δ : Subgroup G) {n : ℕ} (c : Fin n → X)
    (hex : ∀ x : X, ∃ (a : Fin n) (g : Δ), g • c a = x)
    (hin : ∀ a b : Fin n, a ≠ b → ∀ g : Δ, g • c a ≠ c b)
    (x : X) (a : Fin n) :
    coarseLabel Δ c hex x = a ↔ x ∈ orbit Δ (c a) := by
  constructor
  · intro he
    simpa only [he] using coarseLabel_mem Δ c hex x
  · intro hx
    obtain ⟨g,hg⟩ := mem_orbit_iff.mp (coarseLabel_mem Δ c hex x)
    obtain ⟨v,hv⟩ := mem_orbit_iff.mp hx
    by_contra hn
    have he : (v⁻¹ * g) • c (coarseLabel Δ c hex x) = c a := by
      rw [mul_smul,hg,← hv,inv_smul_smul]
    exact hin _ a hn (v⁻¹ * g) he

 def actualCuspLabel
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (m : Fin AV.componentCount → Fin AU.componentCount)
    (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F) (j : CuspIndex AV) :
    CuspIndex AU :=
  ⟨m j.1,coarseLabel _ (AU.cuspAtlas (m j.1)).cusp (AU.cuspAtlas (m j.1)).exhaustive
    (δ j.1 • (AV.cuspAtlas j.1).cusp j.2)⟩

 theorem actualCuspLabel_preimage
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (m : Fin AV.componentCount → Fin AU.componentCount)
    (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
    (i : Fin AV.componentCount) (a : Fin (AU.cuspAtlas (m i)).cuspCount)
    (b : Fin (AV.cuspAtlas i).cuspCount) :
    actualCuspLabel AV AU m δ ⟨i,b⟩ = ⟨m i,a⟩ ↔
      δ i • (AV.cuspAtlas i).cusp b ∈
        orbit (KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative (m i)))
          ((AU.cuspAtlas (m i)).cusp a) := by
  change Sigma.mk (m i) (coarseLabel _ (AU.cuspAtlas (m i)).cusp
    (AU.cuspAtlas (m i)).exhaustive (δ i • (AV.cuspAtlas i).cusp b)) =
      (⟨m i,a⟩ : CuspIndex AU) ↔ _
  rw [Sigma.mk.inj_iff]
  simp only [true_and,heq_eq_eq]
  exact coarseLabel_eq_iff _ _ (AU.cuspAtlas (m i)).exhaustive
    (AU.cuspAtlas (m i)).inequivalent _ a

 theorem actual_label_transition
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (m : Fin AV.componentCount → Fin AU.componentCount)
    (δ : Fin AV.componentCount → KPCuspArithmetic.PGL2 F)
    (ε : Fin AV.componentCount → rootsOfUnity 3 F)
    (u : Fin AV.componentCount → U.toOpenSubgroup)
    (hc : ∀ i, AU.representative (m i) = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (δ i) *
      KPCuspGenuineMonodromy.central F ζ hζ (ε i) * AV.representative i * u i)
    (j : CuspIndex AV) :
    let k := actualCuspLabel AV AU m δ j
    let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1)
    let q := (AU.cuspAtlas k.1).cusp k.2
    let η := cuspCorrection Δ q (δ j.1 • (AV.cuspAtlas j.1).cusp j.2)
      (coarseLabel_mem _ _ (AU.cuspAtlas (m j.1)).exhaustive _)
    let t := ((AU.cuspAtlas k.1).representative k.2)⁻¹ * (η.val⁻¹ * δ j.1) *
      (AV.cuspAtlas j.1).representative j.2
    let S := KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1))
      ((AV.cuspAtlas j.1).cusp j.2) ((AV.cuspAtlas j.1).representative j.2)
    let T := KPCuspArithmetic.conjugatedStabilizer F Δ q ((AU.cuspAtlas k.1).representative k.2)
    t • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F ∧
      S.map (MulAut.conj t).toMonoidHom ≤ T ∧
      ((S.map (MulAut.conj t).toMonoidHom).subgroupOf T).FiniteIndex := by
  dsimp only
  let k := actualCuspLabel AV AU m δ j
  let Δ := KPCuspGenuineMonodromy.Component F ζ hζ U (AU.representative k.1)
  let q := (AU.cuspAtlas k.1).cusp k.2
  let η := cuspCorrection Δ q (δ j.1 • (AV.cuspAtlas j.1).cusp j.2)
    (coarseLabel_mem _ _ (AU.cuspAtlas (m j.1)).exhaustive _)
  have hq : η.val • q = δ j.1 • (AV.cuspAtlas j.1).cusp j.2 :=
    cuspCorrection_formula _ _ _ _
  have hq' : (η.val⁻¹ * δ j.1) • (AV.cuspAtlas j.1).cusp j.2 = q := by
    rw [mul_smul,← hq,inv_smul_smul]
  have hconj : (KPCuspGenuineMonodromy.Component F ζ hζ V (AV.representative j.1)).map
      (MulAut.conj (η.val⁻¹ * δ j.1)).toMonoidHom ≤ Δ := by
    rintro x ⟨v,hv,rfl⟩
    have hm := AllLevelGeometry.actual_component_conjugate h (δ j.1) (ε j.1) (u j.1)
      (hc j.1) ⟨v,hv,rfl⟩
    have hn := Δ.mul_mem (Δ.mul_mem (Δ.inv_mem η.property) hm) η.property
    convert hn using 1 <;> simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply] <;> group
  refine ⟨?_,?_,?_⟩
  · rw [mul_smul,mul_smul,(AV.cuspAtlas j.1).representative_formula,hq']
    change ((AU.cuspAtlas k.1).representative k.2)⁻¹ • (AU.cuspAtlas k.1).cusp k.2 = _
    rw [← (AU.cuspAtlas k.1).representative_formula,inv_smul_smul]
  · exact AllLevelGeometry.conjugated_cusp_refinement _ _ _ hconj hq'
  · exact FiniteIndexContinuation.actual_cusp_match_index AV AU j k
      (δ j.1) η (ε j.1) (u j.1) (hc j.1) hq

end ActualCuspLabelPort

namespace AllLevelMeasureTransport
open MeasureTheory
open scoped ENNReal

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U V : Level F ζ hζ}
  {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ} {P : SphericalTransport F ζ hζ}

 theorem section_lintegral
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (D : GeometricDisintegration A R P)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂weighted_section_measure A D.componentWeight) =
      ∫⁻ ω, ∫⁻ x, f x ∂D.unipotent ω ∂D.beta := by
  rw [← D.section_disintegration f hf]
  simp only [weighted_section_measure, lintegral_finsetSum_measure, lintegral_smul_measure,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_map hf (cross_section_inclusion_measurable A j)]

 theorem beta_eq_marginal
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (D : GeometricDisintegration A R P) :
    weighted_angular_measure A D.componentWeight = D.beta := by
  exact angular_marginal_of_disintegration A D.toFiberKernel D.componentWeight D.beta
    D.section_disintegration

end AllLevelMeasureTransport

end DedekindZetaZeroFree.KPMsFixedHaar

end
