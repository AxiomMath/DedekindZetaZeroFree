module

public import DedekindZetaZeroFree.Geometry.Cusps.FundamentalDomains.ExactRectangles

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical
namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.ActualDomain
variable {F : Type} [Field F] [NumberField F]
 {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
 {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

theorem finiteMeasure (G : KPCuspCharts.ChartOutput F hF S D) :
    IsFiniteMeasure ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  constructor
  letI := G.finite_sectionMeasure
  have h := measure_lt_top G.sectionMeasure Set.univ
  rw [G.sectionMeasure_formula,
    Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ] at h
  simpa using h

theorem bounded (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.Cross F → ℝ) (hf : Continuous f)
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F), f (G.crossAction s x) = f x) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  have hrel : ∀ x y, KPCuspCharts.crossRelation F S x y → f x = f y := by
    intro x y hxy
    change MulAction.orbitRel S _ (KPCuspCharts.toArch F (x, 0))
      (KPCuspCharts.toArch F (y, 0)) at hxy
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp hxy)
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (y, 0)) =
      KPCuspCharts.toArch F (x, 0) at hs
    rw [G.actual_action s A hA hc] at hs
    have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective hs
    have hx : G.crossAction s y = x := by
      rw [G.crossAction_formula s A hA hc]
      exact congrArg Prod.fst hp
    rw [← hx]
    exact hinv s y
  let q : KPCuspCharts.CrossQuotient F S → ℝ := Quotient.lift f hrel
  have hq : Continuous q := hf.quotient_lift _
  letI := G.compact_cross
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  exact ⟨C, fun x => hC (Quotient.mk _ x) (Set.mem_univ _)⟩

theorem integrable (G : KPCuspCharts.ChartOutput F hF S D)
    (f : KPCuspCharts.Cross F → ℝ) (hf : Continuous f)
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F), f (G.crossAction s x) = f x)
    (ν : Measure (KPCuspCharts.Cross F)) [IsFiniteMeasure ν] : Integrable f ν := by
  obtain ⟨C, hC⟩ := bounded G f hf hinv
  exact ⟨hf.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hC)⟩

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.ActualDomain

end

end

section
noncomputable section
open MeasureTheory
open scoped Classical ENNReal Pointwise
namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection
variable {F : Type} [Field F] [NumberField F]
 {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
 {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

theorem actual_rectangle_integral_comparison (G : KPCuspCharts.ChartOutput F hF S D)
 (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
 (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
 (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
 (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
   y + KPCuspCharts.embedding F l.val ∈ A)
 (hB : ∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
   b + v.val ∈ B)
 (f : KPCuspCharts.Cross F → ℝ) (hf : Continuous f)
 (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F), f (G.crossAction s x) = f x) :
 (∫ x in A ×ˢ B, f x ∂volume.prod G.shapeMeasure) =
 (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ) *
 (∫ x in G.fundamentalDomain, f x ∂volume.prod G.shapeMeasure) := by
 letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
 letI : Encodable F := Encodable.ofCountable F
 letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
 letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
 letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
 letI := KPCuspCharts.homeomorphAction G.crossAction
 letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
   ⟨fun s => (G.crossAction s).continuous.measurable⟩
 letI := G.haar_shapeMeasure
 letI := G.finite_isotropy
 letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) :=
   ⟨fun s U hU => by
     have hm := congrArg (fun ν : Measure (KPCuspCharts.Cross F) => ν U) (G.measure_invariant s)
     rw [Measure.map_apply (G.crossAction s).continuous.measurable hU] at hm
     exact hm⟩
 letI := ActualDomain.finiteMeasure G
 letI : IsFiniteMeasure ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) := by
   constructor
   rw [Measure.restrict_apply MeasurableSet.univ]
   simp only [Set.univ_inter]
   rw [Measure.prod_prod A B]
   exact ENNReal.mul_lt_top hAb.measure_lt_top hBb.measure_lt_top
 have hc : (ENat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) =
     (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) := by
   simp [ENat.card_eq_coe_natCard]
 have heq := OrbitMultiplicity.integral_comparison (volume.prod G.shapeMeasure)
   G.isFundamentalDomain (hAm.prod hBm)
   (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits)) (by simp)
   (Filter.Eventually.of_forall fun x => (rectangle_orbit_multiplicity G A hA B hB x).trans hc)
   f hinv (ActualDomain.integrable G f hf hinv _) (ActualDomain.integrable G f hf hinv _)
 simpa using heq
end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.HorizontalFD

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  {L : AddSubgroup X} [Countable L] [T2Space (X ⧸ L)]
  [SecondCountableTopology (X ⧸ L)]
  [MeasurableSpace Y]

theorem integral_lift_eq_zero
    (ν : Measure X) [ν.IsAddHaarMeasure] [ν.IsAddRightInvariant] [SigmaFinite ν]
    (μ : Measure (X ⧸ L)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {A : Set X} (hA : IsAddFundamentalDomain L.op A ν) (hAfin : ν A ≠ ⊤)
    (f : X ⧸ L → ℝ) (hf : AEStronglyMeasurable f μ) (hzero : ∫ z, f z ∂μ = 0) :
    (∫ x in A, f (QuotientAddGroup.mk x) ∂ν) = 0 := by
  let μ' : Measure (X ⧸ L) := ν A • μ
  letI : Measure.IsAddLeftInvariant μ' := inferInstanceAs (Measure.IsAddLeftInvariant (ν A • μ))
  letI : IsFiniteMeasure μ' := by
    dsimp [μ']
    exact ⟨by simp [hAfin.lt_top]⟩
  letI : HasAddFundamentalDomain L.op X ν := hA.hasAddFundamentalDomain ν
  letI : AddQuotientMeasureEqMeasurePreimage ν μ' :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage ν (by
      rw [hA.covolume_eq_volume ν]
      simp [μ'])
  have hmp := measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage ν hA μ'
  have hm : AEStronglyMeasurable f μ' := hf.smul_measure (ν A)
  rw [← hmp.map_eq] at hm
  rw [← integral_map hmp.measurable.aemeasurable hm, hmp.map_eq]
  simp [μ', integral_smul_measure, hzero]

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.HorizontalFD

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical
namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem full_torus_zero_mean_descent
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ)
    (hf : Continuous (fun x : KPCuspCharts.Cross F =>
      f (QuotientAddGroup.mk x.1) x.2))
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2)
    (hzero : ∀ b : KPCuspCharts.Shape F, (∫ z, f z b ∂μ) = 0) :
    ∃ ν : Measure (KPCuspCharts.Torus F D.L),
      ν.IsAddHaarMeasure ∧ IsProbabilityMeasure ν ∧
      ∃ g : KPCuspCharts.Torus F D.L → KPCuspCharts.Shape F → ℝ,
        Continuous (fun x : KPCuspCharts.Cross F =>
          g (QuotientAddGroup.mk x.1) x.2) ∧
        (∀ x b, g (QuotientAddGroup.mk x) b = f (QuotientAddGroup.mk x) b) ∧
        (∀ b, AEStronglyMeasurable (fun z => g z b) ν) ∧
        (∀ b, (∫ z, g z b ∂ν) = 0) := by
  letI := hμ
  letI := hprob
  obtain ⟨hd, _⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  have hle : KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, ha.1, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule :=
    DiscreteTopology.of_subset hd hle
  letI : DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)) :=
    ‹DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule›
  let q : KPCuspGenuineMonodromy.KernelTorus S D ρ →+ KPCuspCharts.Torus F D.L :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id _) hle
  have hqmk (x : KPCuspCharts.Horizontal F) :
      q (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := rfl
  have hqc : Continuous q := by
    rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact QuotientAddGroup.continuous_mk
  have hqs : Function.Surjective q := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  let ν := Measure.map q μ
  letI : ν.IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ q hqc hqs
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hrel (b : KPCuspCharts.Shape F) (x y : KPCuspCharts.Horizontal F)
      (hxy : QuotientAddGroup.leftRel (KPCuspCharts.translationLattice F D.L) x y) :
      f (QuotientAddGroup.mk x) b = f (QuotientAddGroup.mk y) b := by
    obtain ⟨a, ha, hea⟩ := (QuotientAddGroup.leftRel_apply.mp hxy)
    have hy : y = x + KPCuspCharts.embedding F a := by
      rw [hea]
      abel
    rw [hy]
    let l : D.L := ⟨a, ha⟩
    let s := D.inclusion (Multiplicative.ofAdd l)
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    have h := G.actual_action s A hA hc ((x, b), 0)
    rw [G.unipotent_action l ((x, b), 0)] at h
    have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective h
    have hs : G.crossAction s (x, b) = (x + KPCuspCharts.embedding F a, b) := by
      rw [G.crossAction_formula s A hA hc]
      exact (congrArg Prod.fst hp).symm
    have hh := hinv s (x, b)
    rw [hs] at hh
    exact hh.symm
  let g : KPCuspCharts.Torus F D.L → KPCuspCharts.Shape F → ℝ :=
    fun z b => Quotient.lift (fun x => f (QuotientAddGroup.mk x) b) (hrel b) z
  have hgmk (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) :
      g (QuotientAddGroup.mk x) b = f (QuotientAddGroup.mk x) b := rfl
  have hgq (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) (b : KPCuspCharts.Shape F) :
      g (q z) b = f z b := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rfl
  have hgm (b : KPCuspCharts.Shape F) : Measurable (fun z => g z b) := by
    apply measurable_from_quotient.mpr
    exact (hf.comp (continuous_id.prodMk continuous_const)).measurable
  refine ⟨ν, inferInstance, inferInstance, g, ?_, hgmk, fun b => (hgm b).aestronglyMeasurable, ?_⟩
  · exact hf
  · intro b
    rw [integral_map hqc.measurable.aemeasurable (hgm b).aestronglyMeasurable]
    simpa only [hgq] using hzero b

theorem horizontal_exact_domain_integral_zero
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ)
    (hf : Continuous (fun x : KPCuspCharts.Cross F =>
      f (QuotientAddGroup.mk x.1) x.2))
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2)
    (hzero : ∀ b : KPCuspCharts.Shape F, (∫ z, f z b ∂μ) = 0)
    {A : Set (KPCuspCharts.Horizontal F)} (hAm : MeasurableSet A)
    (hAb : Bornology.IsBounded A)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (b : KPCuspCharts.Shape F) :
    (∫ y in A, f (QuotientAddGroup.mk y) b) = 0 := by
  obtain ⟨ν, hν, hνprob, g, _, hgmk, hgm, hgzero⟩ :=
    full_torus_zero_mean_descent G μ hμ hprob f hf hinv hzero
  letI := hν
  letI := hνprob
  obtain ⟨hd, _⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
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
    refine ⟨⟨AddOpposite.op l.val, l.property⟩, ?_, ?_⟩
    · exact ha
    · intro k hk
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
  have hAfin : (volume : Measure (KPCuspCharts.Horizontal F)) A ≠ ⊤ :=
    hAb.measure_lt_top.ne
  letI : Countable (KPCuspCharts.translationLattice F D.L) :=
    countable_of_Lindelof_of_discrete
  have hz := HorizontalFD.integral_lift_eq_zero volume ν hfd hAfin (fun z => g z b)
    (hgm b) (hgzero b)
  simpa only [hgmk] using hz

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem crossAction_inclusion
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (l : D.L) (x : KPCuspCharts.Cross F) :
    G.crossAction (D.inclusion (Multiplicative.ofAdd l)) x =
      (x.1 + KPCuspCharts.embedding F l.val, x.2) := by
  let s := D.inclusion (Multiplicative.ofAdd l)
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  have h := G.actual_action s A hA hc (x, 0)
  rw [G.unipotent_action l (x, 0)] at h
  have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective h
  rw [G.crossAction_formula s A hA hc]
  exact (congrArg Prod.fst hp).symm

theorem invariant_zero_mean_fiber_integral
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ)
    (hf : Continuous (fun x : KPCuspCharts.Cross F =>
      f (QuotientAddGroup.mk x.1) x.2))
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2)
    (hzero : ∀ b : KPCuspCharts.Shape F, (∫ z, f z b ∂μ) = 0) :
    (∫ x : KPCuspCharts.Cross F, f (QuotientAddGroup.mk x.1) x.2
      ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) = 0 := by
  obtain ⟨A, B, hAm, hAb, hBm, hBb, hA, hB⟩ := actual_exact_comparison_rectangle G
  let k : KPCuspCharts.Cross F → ℝ := fun x => f (QuotientAddGroup.mk x.1) x.2
  have hkinv : ∀ (s : S) (x : KPCuspCharts.Cross F), k (G.crossAction s x) = k x := hinv
  letI := G.haar_shapeMeasure
  letI := G.finite_isotropy
  letI : IsFiniteMeasure ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    rw [Measure.prod_prod A B]
    exact ENNReal.mul_lt_top hAb.measure_lt_top hBb.measure_lt_top
  have hkint := ActualDomain.integrable G k hf hkinv
    ((volume.prod G.shapeMeasure).restrict (A ×ˢ B))
  have hrect : (∫ x in A ×ˢ B, k x ∂volume.prod G.shapeMeasure) = 0 := by
    rw [← Measure.prod_restrict] at hkint ⊢
    rw [integral_prod_symm k hkint]
    have hz (b : KPCuspCharts.Shape F) : (∫ y in A, k (y, b)) = 0 :=
      horizontal_exact_domain_integral_zero G μ hμ hprob f hf hinv hzero hAm hAb hA b
    simp_rw [hz]
    simp
  have heq := actual_rectangle_integral_comparison G A B hAm hAb hBm hBb hA hB k hf hkinv
  have hcard : (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) ≠ 0)
  exact (mul_eq_zero.mp (heq.symm.trans hrect)).resolve_left hcard

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end
