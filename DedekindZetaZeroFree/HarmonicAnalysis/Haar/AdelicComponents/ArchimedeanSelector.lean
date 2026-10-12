module

public import DedekindZetaZeroFree.Adeles.Quotients.RationalComponents.Defs
public import DedekindZetaZeroFree.Adeles.Quotients.SphericalProjection

@[expose] public section

noncomputable section
open scoped Classical NumberField Pointwise
open MeasureTheory Topology Set

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar

open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming rationalLift_split → rationalLift_split
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming rationalLift → rationalLift
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming rationalLift_arch → rationalLift_arch
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming rationalLift_finite → rationalLift_finite
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming actual_split → actual_split
open _root_.DedekindZetaZeroFree.KPMsFixedHaar renaming archProjection_compare → archProjection_compare
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem restricted_discrete
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : Fin A.componentCount) :
    DiscreteTopology (Ga F ζ hζ hF U A j) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  obtain ⟨e, he⟩ := actual_split F ζ hζ
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F) :=
    (isOpenQuotientMap_fst (Y := KPFiniteCuspAtlas.FiniteCover F ζ hζ)).locallyCompactSpace
  letI : T2Space (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.isEmbedding.t2Space
  letI : T2Space (KPSmoothActualFlowData.GInfinity F) :=
    (IsEmbedding.of_leftInverse (fun _ => rfl) continuous_fst
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : KPSmoothActualFlowData.GInfinity F => (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ))))).t2Space
  let g := A.representative j
  let H : Set (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    ⋃ ε : rootsOfUnity 3 F, (fun u => KPCuspGenuineMonodromy.central F ζ hζ ε * g * u * g⁻¹) '' (U.toOpenSubgroup : Set _)
  have hH : IsCompact H := isCompact_iUnion fun ε => U.isCompact.image (by fun_prop)
  obtain ⟨W, ho, h1W, hc⟩ := exists_isOpen_mem_isCompact_closure (1 : KPSmoothActualFlowData.GInfinity F)
  let C := e '' (closure W ×ˢ H)
  have hC : IsCompact C := (hc.prod hH).image e.continuous
  let Γ := ActualQuotient.rationalSubgroup F ζ hζ
  let T : Set (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) := (Γ : Set _) ∩ C
  have hd := ActualQuotient.actual_rational_closed_discrete F ζ hζ
  have hT : T.Finite := (hC.inter_left hd.1).finite (hd.2.mono inter_subset_left)
  let p := KPSmoothLocalQuotientCharts.archProjection F ζ hζ
  let Bad := p '' T \ {1}
  have hBad : Bad.Finite := (hT.image p).diff
  have h1Bad : (1 : KPSmoothActualFlowData.GInfinity F) ∉ Bad := by simp [Bad]
  have hsmall : ∀ a ∈ Ga F ζ hζ hF U A j, a ∈ W → a ∈ p '' T := by
    intro a ha haw
    obtain ⟨σ, hσ, rfl⟩ := ha
    let r := rationalLift F ζ hζ σ
    have hrΓ : r ∈ Γ := ⟨rationalEquiv F σ, rfl⟩
    obtain ⟨ε, hε⟩ := rationalLift_split F ζ hζ σ
    obtain ⟨η, u, hu⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U g ⟨σ, hσ⟩
    let c := KPCuspGenuineMonodromy.central F ζ hζ ε * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ
    have hcH : c ∈ H := by
      refine mem_iUnion.mpr ⟨ε * η, ?_⟩
      refine ⟨u, u.property, ?_⟩
      have hu' := congrArg (fun x : KPFiniteCuspAtlas.FiniteCover F ζ hζ => x * g⁻¹) hu
      simp only [mul_assoc, mul_inv_cancel, mul_one] at hu'
      dsimp [c]
      rw [hu']
      simp [map_mul, mul_assoc]
    have hp : p r = _ := rationalLift_arch F ζ hζ σ
    have hrC : r ∈ C := by
      refine ⟨(p r, c), ⟨?_, hcH⟩, ?_⟩
      · exact subset_closure haw
      · rw [he, hp]
        exact hε.symm
    exact ⟨r, ⟨hrΓ, hrC⟩, rfl⟩
  apply discreteTopology_of_isOpen_singleton_one
  have hopen : IsOpen (W \ Bad) := ho.inter hBad.isClosed.isOpen_compl
  have hpre : (Subtype.val : Ga F ζ hζ hF U A j → _) ⁻¹' (W \ Bad) = {1} := by
    ext a
    constructor
    · intro ha
      have heq : a.val = 1 := by
        by_contra hn
        exact ha.2 ⟨hsmall a.val a.property ha.1, hn⟩
      exact Set.mem_singleton_iff.mpr (Subtype.ext heq)
    · rintro rfl
      exact ⟨h1W, h1Bad⟩
  rw [← hpre]
  exact hopen.preimage continuous_subtype_val

theorem actual_component_arch_group_selector
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (i : Fin A.componentCount) :
    IsClosed (Ga F ζ hζ hF U A i : Set (KPSmoothActualFlowData.GInfinity F)) ∧
      DiscreteTopology (Ga F ζ hζ hF U A i) ∧
      ∃ D : Set (KPSmoothActualFlowData.GInfinity F), MeasurableSet D ∧
        ∀ x : KPSmoothActualFlowData.GInfinity F,
          ∃! γ : Ga F ζ hζ hF U A i, γ.val * x ∈ D := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨e, he⟩ := actual_split F ζ hζ
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    e.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F) :=
    (isOpenQuotientMap_fst (Y := KPFiniteCuspAtlas.FiniteCover F ζ hζ)).locallyCompactSpace
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isOpenQuotientMap_fst.comp e.symm.isOpenQuotientMap).secondCountableTopology
  letI : T2Space (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) := e.isEmbedding.t2Space
  letI : T2Space (KPSmoothActualFlowData.GInfinity F) :=
    (IsEmbedding.of_leftInverse (fun _ => rfl) continuous_fst
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : KPSmoothActualFlowData.GInfinity F => (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ))))).t2Space
  let Γ := Ga F ζ hζ hF U A i
  letI : DiscreteTopology Γ := restricted_discrete F ζ hζ hF U A i
  have hclosed : IsClosed (Γ : Set (KPSmoothActualFlowData.GInfinity F)) := Subgroup.isClosed_of_discreteTopology
  letI : Countable Γ := (hclosed.isLindelof.countable_of_isDiscrete
    (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).to_subtype
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  haveI : ProperlyDiscontinuousSMul Γ (KPSmoothActualFlowData.GInfinity F) := by
    have hstab : MulAction.stabilizer (KPSmoothActualFlowData.GInfinity F) (1 : KPSmoothActualFlowData.GInfinity F) = ⊥ := by
      ext g; simp [MulAction.mem_stabilizer_iff]
    apply KPArithmeticAction.properlyDiscontinuous_of_section (1 : KPSmoothActualFlowData.GInfinity F) id
      continuous_id (fun x => by simp)
    rw [hstab]
    exact isCompact_singleton
  have hfree : ∀ᵐ x ∂(Measure.count : Measure (KPSmoothActualFlowData.GInfinity F)),
      ∀ g : Γ, g • x = x → g = 1 := by
    apply Filter.Eventually.of_forall
    intro x g hg
    change g.val * x = x at hg
    apply Subtype.ext
    exact mul_right_cancel (hg.trans (one_mul x).symm)
  obtain ⟨D, hD, hfund⟩ :=
    KPCuspChart.SectionConstruction.measurable_fundamental_domain_of_properly_discontinuous_ae_free
      (H := Γ) Measure.count hfree
  refine ⟨hclosed, inferInstance, D, hD, ?_⟩
  intro x
  obtain ⟨g, hg⟩ := Measure.ae_count_iff.mp hfund.ae_covers x
  refine ⟨g, hg, ?_⟩
  intro a ha
  by_contra hne
  have hd := hfund.aedisjoint (show a⁻¹ ≠ g⁻¹ from fun h => hne (inv_injective h))
  have hempty : a⁻¹ • D ∩ g⁻¹ • D = ∅ := Measure.count_eq_zero_iff.mp hd
  have hx : x ∈ a⁻¹ • D ∩ g⁻¹ • D := by
    constructor
    · exact ⟨a • x, ha, by simp⟩
    · exact ⟨g • x, hg, by simp⟩
  rw [hempty] at hx
  exact hx

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
