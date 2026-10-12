module

public import DedekindZetaZeroFree.Adeles.Quotients.ArchimedeanFiniteProduct

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex.AdelicSlicesRaw
open MeasureTheory Topology NumberField
open scoped Classical Pointwise NumberField ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def quotientMap : ActualCover F ζ hζ → X F ζ hζ :=
  _root_.Quotient.mk _

def levelMap (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    ActualCover F ζ hζ → LevelSpace F ζ hζ U geometric :=
  DoubleCoset.mk (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric)

def levelMeasure (μX : Measure (X F ζ hζ)) (U : FiniteLevel F ζ hζ)
    (geometric : Bool) : Measure (LevelSpace F ζ hζ U geometric) :=
  Measure.map (_root_.Quotient.lift (levelMap F ζ hζ U geometric) (by
    intro a b hab
    apply _root_.Quotient.sound
    obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ rationalSubgroup F ζ hζ, b = γ * a := by
      refine ⟨b * a⁻¹, ?_, by simp⟩
      exact QuotientGroup.rightRel_apply.mp hab
    exact DoubleCoset.rel_iff.mpr ⟨γ, hγ, 1,
      (rightSubgroup F ζ hζ U geometric).one_mem, by simpa using hγeq⟩)) μX

theorem productHaarTransport
    (μ : Measure (ActualCover F ζ hζ)) [μ.IsHaarMeasure]
    (μArch : Measure (ArchGroup F)) [μArch.IsHaarMeasure] :
    ∃ ν : Measure (finiteSubgroup F ζ hζ), ν.IsHaarMeasure ∧
      Measure.map (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
        archimedeanInsertion F ζ hζ p.1 * p.2) (μArch.prod ν) = μ := by
  obtain ⟨e, he, _, _, _, _, hLC⟩ := actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI := hLC
  letI : BorelSpace (ArchGroup F) := ⟨rfl⟩
  letI : SecondCountableTopology (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (ArchGroup F) :=
    (isEmbedding_prodMkLeft (1 : finiteSubgroup F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (finiteSubgroup F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : ArchGroup F)).secondCountableTopology
  letI : LocallyCompactSpace (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := finiteSubgroup F ζ hζ)).locallyCompactSpace
  letI : IsTopologicalGroup (ArchGroup F) := inferInstance
  let ν₀ : Measure (finiteSubgroup F ζ hζ) := MeasureTheory.Measure.haar
  haveI : ν₀.IsHaarMeasure := inferInstance
  haveI : SFinite ν₀ := inferInstance
  haveI : SFinite μArch := inferInstance
  let μ₀ := Measure.map e (μArch.prod ν₀)
  let c := Measure.haarScalarFactor μ μ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  letI : (c • ν₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  refine ⟨c • ν₀, inferInstance, ?_⟩
  have heq : (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
      archimedeanInsertion F ζ hζ p.1 * p.2) = e := by
    funext p; exact (he p.1 p.2).symm
  rw [heq, Measure.prod_smul_right, Measure.map_smul]
  · exact (Measure.isMulLeftInvariant_eq_smul μ μ₀).symm
  · exact e.continuous.measurable.aemeasurable

namespace ProductHaarTransportProof
open Set Function
variable {G A : Type*} [_root_.Group G] [MulAction G A] [MeasurableSpace A]
  [Countable G] [MeasurableConstSMul G A]
  {μ : Measure A} [SMulInvariantMeasure G A μ]
lemma unfold_injective_slice {D S : Set A} (hD : IsFundamentalDomain G D μ)
    (hS : MeasurableSet S) (hd : Pairwise (Disjoint on fun g : G => g • S))
    (f : A → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ (g : G) (x : A), f (g • x) = f x) :
    (∫⁻ x in S, f x ∂μ) = ∫⁻ x in (⋃ g : G, g • S) ∩ D, f x ∂μ := by
  rw [hD.setLIntegral_eq_tsum' f S]
  simp_rw [hinv]
  rw [← lintegral_iUnion₀ (fun g => (hS.nullMeasurableSet.smul g).inter hD.nullMeasurableSet)]
  · rw [iUnion_inter]
  · exact fun g k hne => ((hd hne).mono inter_subset_left inter_subset_left).aedisjoint
private lemma rightSubgroup_le_finite (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    rightSubgroup F ζ hζ U geometric ≤ finiteSubgroup F ζ hζ := by
  have hc := (actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.2.1
  have hl : levelSubgroup F ζ hζ U ≤ finiteSubgroup F ζ hζ := by
    rintro _ ⟨u, hu, rfl⟩
    exact u.property
  cases geometric <;> simp only [rightSubgroup, Bool.false_eq_true, ↓reduceIte, sup_le_iff]
  · exact hl
  · exact ⟨hl, hc⟩
lemma slice_pairwise_disjoint
    (U : FiniteLevel F ζ hζ) (geometric : Bool) (h : finiteSubgroup F ζ hζ)
    (W : Set (ArchGroup F))
    (hinj : Function.Injective (fun y : W => levelMap F ζ hζ U geometric
      (archimedeanInsertion F ζ hζ y.val * h))) :
    Pairwise (Disjoint on fun γ : rationalSubgroup F ζ hζ =>
      γ • {g : ActualCover F ζ hζ | ∃ y ∈ W, ∃ k ∈ rightSubgroup F ζ hζ U geometric,
        g = archimedeanInsertion F ζ hζ y * h * k}) := by
  obtain ⟨e, he, _, ha, hker, _, _⟩ := actualArchFiniteSplitting F ζ hζ
  have hk (k : ActualCover F ζ hζ) (hk : k ∈ rightSubgroup F ζ hζ U geometric) :
      archProjection F ζ hζ k = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact rightSubgroup_le_finite F ζ hζ U geometric hk
  have hh : archProjection F ζ hζ h = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact h.property
  intro γ δ hne
  apply Set.disjoint_left.mpr
  intro g hg hd
  obtain ⟨s, ⟨y, hy, k, hkm, rfl⟩, hgs⟩ := hg
  obtain ⟨t, ⟨z, hz, l, hlm, rfl⟩, hgt⟩ := hd
  have heq : (γ : ActualCover F ζ hζ) * (archimedeanInsertion F ζ hζ y * h * k) =
      (δ : ActualCover F ζ hζ) * (archimedeanInsertion F ζ hζ z * h * l) := by
    exact hgs.trans hgt.symm
  have hlevel : levelMap F ζ hζ U geometric (archimedeanInsertion F ζ hζ y * h) =
      levelMap F ζ hζ U geometric (archimedeanInsertion F ζ hζ z * h) := by
    apply Quotient.sound
    apply DoubleCoset.rel_iff.mpr
    refine ⟨δ⁻¹ * γ, (rationalSubgroup F ζ hζ).mul_mem δ⁻¹.property γ.property,
      k * l⁻¹, (rightSubgroup F ζ hζ U geometric).mul_mem hkm
        ((rightSubgroup F ζ hζ U geometric).inv_mem hlm), ?_⟩
    have heq' := congrArg (fun g : ActualCover F ζ hζ => (δ : ActualCover F ζ hζ)⁻¹ * g * l⁻¹) heq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, mul_one] using heq'.symm
  have hyz : y = z := congrArg Subtype.val (hinj (a₁ := ⟨y, hy⟩) (a₂ := ⟨z, hz⟩) hlevel)
  have harch := congrArg (archProjection F ζ hζ) heq
  simp only [map_mul, ha, hh, hk k hkm, hk l hlm, mul_one] at harch
  rw [hyz] at harch
  have hγδ : archProjection F ζ hζ γ = archProjection F ζ hζ δ := mul_right_cancel harch
  have hi := ActualQuotient.actual_rational_arch_injective F ζ hζ
  exact hne (hi hγδ)
lemma slice_saturation (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (h : finiteSubgroup F ζ hζ) (W : Set (ArchGroup F)) :
    levelMap F ζ hζ U geometric ⁻¹'
      ((fun y : W => levelMap F ζ hζ U geometric
        (archimedeanInsertion F ζ hζ y.val * h)) '' Set.univ) =
      ⋃ γ : rationalSubgroup F ζ hζ,
        γ • {g : ActualCover F ζ hζ | ∃ y ∈ W, ∃ k ∈ rightSubgroup F ζ hζ U geometric,
          g = archimedeanInsertion F ζ hζ y * h * k} := by
  ext g
  constructor
  · rintro ⟨⟨y, hy⟩, _, heq⟩
    obtain ⟨γ, hγ, k, hk, hg⟩ := DoubleCoset.rel_iff.mp (Quotient.exact heq)
    exact mem_iUnion.mpr ⟨⟨γ, hγ⟩, ⟨archimedeanInsertion F ζ hζ y * h * k,
      ⟨y, hy, k, hk, rfl⟩, by simpa [mul_assoc] using hg.symm⟩⟩
  · intro hg
    obtain ⟨γ, t, ⟨y, hy, k, hk, ht⟩, heq⟩ := mem_iUnion.mp hg
    refine ⟨⟨y, hy⟩, mem_univ _, ?_⟩
    apply Quotient.sound
    apply DoubleCoset.rel_iff.mpr
    exact ⟨γ, γ.property, k, hk, by simpa [ht, mul_assoc, Subgroup.smul_def] using heq.symm⟩
lemma slice_isOpen (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (h : finiteSubgroup F ζ hζ) (W : Set (ArchGroup F)) (hW : IsOpen W) :
    IsOpen {g : ActualCover F ζ hζ | ∃ y ∈ W, ∃ k ∈ rightSubgroup F ζ hζ U geometric,
      g = archimedeanInsertion F ζ hζ y * h * k} := by
  obtain ⟨e, he, _, _, hker, hc, _⟩ := actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let K := (rightSubgroup F ζ hζ U geometric).comap (finiteSubgroup F ζ hζ).subtype
  have hK : IsOpen (K : Set (finiteSubgroup F ζ hζ)) := by
    apply Subgroup.isOpen_mono (H₁ := U.toOpenSubgroup.toSubgroup) _ U.toOpenSubgroup.isOpen
    intro k hk
    change k.val ∈ rightSubgroup F ζ hζ U geometric
    have hl : k.val ∈ levelSubgroup F ζ hζ U := ⟨k, hk, rfl⟩
    cases geometric <;> simp only [rightSubgroup, Bool.false_eq_true, ↓reduceIte]
    · exact hl
    · exact (le_sup_left : levelSubgroup F ζ hζ U ≤ _ ) hl
  have hle : rightSubgroup F ζ hζ U geometric ≤ finiteSubgroup F ζ hζ := by
    have hl : levelSubgroup F ζ hζ U ≤ finiteSubgroup F ζ hζ := by
      rintro _ ⟨u, hu, rfl⟩; exact u.property
    cases geometric <;> simp only [rightSubgroup, Bool.false_eq_true, ↓reduceIte, sup_le_iff]
    · exact hl
    · exact ⟨hl, hc⟩
  have hset : {g : ActualCover F ζ hζ | ∃ y ∈ W, ∃ k ∈ rightSubgroup F ζ hζ U geometric,
      g = archimedeanInsertion F ζ hζ y * h * k} =
      e '' (W ×ˢ (h • (K : Set (finiteSubgroup F ζ hζ)))) := by
    ext g
    constructor
    · rintro ⟨y, hy, k, hk, rfl⟩
      refine ⟨(y, h * ⟨k, hle hk⟩), ⟨hy, ?_⟩, ?_⟩
      · exact ⟨⟨k, hle hk⟩, hk, rfl⟩
      · simpa [mul_assoc] using he y (h * ⟨k, hle hk⟩)
    · rintro ⟨⟨y, a⟩, ⟨hy, b, hb, hab⟩, heg⟩
      refine ⟨y, hy, b, hb, ?_⟩
      change h * b = a at hab
      rw [← heg, ← hab, he]
      simp [mul_assoc]
  rw [hset]
  exact e.toHomeomorph.isOpenMap _ (hW.prod (hK.smul h))
lemma levelMeasure_eq_map (μ : Measure (ActualCover F ζ hζ))
    (μX : Measure (X F ζ hζ)) (D : Set (ActualCover F ζ hζ))
    (hnorm : Measure.map (quotientMap F ζ hζ) (μ.restrict D) = μX)
    (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    levelMeasure F ζ hζ μX U geometric =
      Measure.map (levelMap F ζ hζ U geometric) (μ.restrict D) := by
  letI : BorelSpace (LevelSpace F ζ hζ U geometric) := ⟨rfl⟩
  have hl : Continuous (levelMap F ζ hζ U geometric) := continuous_quot_mk
  have hq : Continuous (quotientMap F ζ hζ) := continuous_quot_mk
  rw [levelMeasure, ← hnorm, Measure.map_map]
  · rfl
  · exact (hl.quotient_lift _).measurable
  · exact hq.measurable
lemma sliceImage_isOpen (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (h : finiteSubgroup F ζ hζ) (W : Set (ArchGroup F)) (hW : IsOpen W) :
    IsOpen ((fun y : W => levelMap F ζ hζ U geometric
      (archimedeanInsertion F ζ hζ y.val * h)) '' Set.univ) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (levelMap F ζ hζ U geometric ⁻¹' _)
  rw [slice_saturation F ζ hζ U geometric h W]
  apply isOpen_iUnion
  intro γ
  exact (slice_isOpen F ζ hζ U geometric h W hW).smul γ
lemma levelMap_mul_left (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (γ : rationalSubgroup F ζ hζ) (g : ActualCover F ζ hζ) :
    levelMap F ζ hζ U geometric (γ * g) = levelMap F ζ hζ U geometric g := by
  apply Quotient.sound
  apply DoubleCoset.rel_iff.mpr
  exact ⟨γ⁻¹, γ⁻¹.property, 1, (rightSubgroup F ζ hζ U geometric).one_mem, by simp⟩
lemma levelMap_mul_right (U : FiniteLevel F ζ hζ) (geometric : Bool)
    (k : ActualCover F ζ hζ) (hk : k ∈ rightSubgroup F ζ hζ U geometric)
    (g : ActualCover F ζ hζ) :
    levelMap F ζ hζ U geometric (g * k) = levelMap F ζ hζ U geometric g := by
  apply Quotient.sound
  apply DoubleCoset.rel_iff.mpr
  exact ⟨1, (rationalSubgroup F ζ hζ).one_mem, k⁻¹,
    (rightSubgroup F ζ hζ U geometric).inv_mem hk, by simp⟩
end ProductHaarTransportProof

theorem fixedProductHaarSliceIntegral
    (μ : Measure (ActualCover F ζ hζ)) [μ.IsHaarMeasure]
    (μArch : Measure (ArchGroup F)) [μArch.IsHaarMeasure]
    (ν : Measure (finiteSubgroup F ζ hζ)) [ν.IsHaarMeasure]
    (hproduct : Measure.map (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
      archimedeanInsertion F ζ hζ p.1 * p.2) (μArch.prod ν) = μ)
    (μX : Measure (X F ζ hζ)) (D : Set (ActualCover F ζ hζ))
    (hD : MeasurableSet D) (hfund : IsFundamentalDomain (rationalSubgroup F ζ hζ) D μ)
    (hnorm : Measure.map (quotientMap F ζ hζ) (μ.restrict D) = μX) :
    ∀ (U : FiniteLevel F ζ hζ) (geometric : Bool)
        (h : finiteSubgroup F ζ hζ) (W : Set (ArchGroup F)),
        IsOpen W →
        Function.Injective (fun y : W => levelMap F ζ hζ U geometric
          (archimedeanInsertion F ζ hζ y.val * h)) →
        ∀ q : LevelSpace F ζ hζ U geometric → ℝ≥0∞, Measurable q →
          (∫⁻ x in (fun y : W => levelMap F ζ hζ U geometric
            (archimedeanInsertion F ζ hζ y.val * h)) '' Set.univ,
              q x ∂levelMeasure F ζ hζ μX U geometric) =
          ν ((finiteSubgroup F ζ hζ).subtype ⁻¹'
            (rightSubgroup F ζ hζ U geometric : Set (ActualCover F ζ hζ))) *
          ∫⁻ y in W, q (levelMap F ζ hζ U geometric
            (archimedeanInsertion F ζ hζ y * h)) ∂μArch := by
  open ProductHaarTransportProof Set Function in
  intro U geometric h W hW hinj q hq
  obtain ⟨e, he, _, _, hker, hc, hLC⟩ := actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI := hLC
  letI : BorelSpace (ArchGroup F) := ⟨rfl⟩
  letI : BorelSpace (LevelSpace F ζ hζ U geometric) := ⟨rfl⟩
  letI : SecondCountableTopology (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (ArchGroup F) :=
    (isEmbedding_prodMkLeft (1 : finiteSubgroup F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (finiteSubgroup F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : ArchGroup F)).secondCountableTopology
  letI : LocallyCompactSpace (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := finiteSubgroup F ζ hζ)).locallyCompactSpace
  haveI : Countable (rationalSubgroup F ζ hζ) := by
    have hd := (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2
    exact (IsLindelof.countable_of_isDiscrete (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1.isLindelof hd).to_subtype
  let S : Set (ActualCover F ζ hζ) := {g | ∃ y ∈ W, ∃ k ∈ rightSubgroup F ζ hζ U geometric,
    g = archimedeanInsertion F ζ hζ y * h * k}
  let K : Set (finiteSubgroup F ζ hζ) := (finiteSubgroup F ζ hζ).subtype ⁻¹'
    (rightSubgroup F ζ hζ U geometric : Set (ActualCover F ζ hζ))
  have hS : MeasurableSet S := (slice_isOpen F ζ hζ U geometric h W hW).measurableSet
  have hl : Measurable (levelMap F ζ hζ U geometric) :=
    (show Continuous (levelMap F ζ hζ U geometric) from continuous_quot_mk).measurable
  have hfun : Measurable (fun g => q (levelMap F ζ hζ U geometric g)) := hq.comp hl
  rw [levelMeasure_eq_map F ζ hζ μ μX D hnorm U geometric,
    setLIntegral_map (sliceImage_isOpen F ζ hζ U geometric h W hW).measurableSet hq
      hl,
    Measure.restrict_restrict ((sliceImage_isOpen F ζ hζ U geometric h W hW).measurableSet.preimage hl),
    slice_saturation F ζ hζ U geometric h W]
  have hinv : ∀ (γ : rationalSubgroup F ζ hζ) (g : ActualCover F ζ hζ),
      q (levelMap F ζ hζ U geometric (γ • g)) = q (levelMap F ζ hζ U geometric g) := by
    intro γ g
    simpa only [Subgroup.smul_def, smul_eq_mul] using congrArg q (levelMap_mul_left F ζ hζ U geometric γ g)
  rw [← unfold_injective_slice hfund hS (slice_pairwise_disjoint F ζ hζ U geometric h W hinj)
    _ hfun hinv]
  have heq : (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
      archimedeanInsertion F ζ hζ p.1 * p.2) = e := by
    funext p; exact (he p.1 p.2).symm
  rw [heq] at hproduct
  have hem : Measurable (e : ArchGroup F × finiteSubgroup F ζ hζ → ActualCover F ζ hζ) :=
    e.continuous.measurable
  rw [← hproduct, setLIntegral_map hS hfun hem]
  have hpre : e ⁻¹' S = W ×ˢ (h • K) := by
    ext p
    constructor
    · rintro ⟨y, hy, k, hk, hg⟩
      have hle : k ∈ finiteSubgroup F ζ hζ := by
        have hlev : levelSubgroup F ζ hζ U ≤ finiteSubgroup F ζ hζ := by
          rintro _ ⟨u, hu, rfl⟩; exact u.property
        cases geometric <;> simp only [rightSubgroup, Bool.false_eq_true, ↓reduceIte] at hk
        · exact hlev hk
        · exact (sup_le hlev hc) hk
      have hekg := he y (h * ⟨k, hle⟩)
      have hp : p = (y, h * ⟨k, hle⟩) := e.injective (hg.trans (by simpa [mul_assoc] using hekg.symm))
      rw [hp]
      exact ⟨hy, ⟨⟨k, hle⟩, hk, rfl⟩⟩
    · rintro ⟨hp, k, hk, hpk⟩
      refine ⟨p.1, hp, k, hk, ?_⟩
      rw [he, ← hpk]
      simp [mul_assoc]
  have hfe : Measurable (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
      q (levelMap F ζ hζ U geometric (e p))) := hfun.comp hem
  rw [hpre, setLIntegral_prod (μ := μArch) (ν := ν)
    (fun p => q (levelMap F ζ hζ U geometric (e p))) hfe.aemeasurable]
  have hK : MeasurableSet K := by
    have hcl := ActualQuotient.actual_right_compact F ζ hζ U geometric
    exact hcl.isClosed.measurableSet.preimage measurable_subtype_coe
  have hKh : MeasurableSet (h • K) := by
    exact (measurableEmbedding_const_smul h).measurableSet_image.mpr hK
  have hinner (y : ArchGroup F) :
      (∫⁻ k in h • K, q (levelMap F ζ hζ U geometric (e (y, k))) ∂ν) =
        ν K * q (levelMap F ζ hζ U geometric (archimedeanInsertion F ζ hζ y * h)) := by
    rw [setLIntegral_congr_fun hKh]
    · rw [setLIntegral_const, measure_smul]
      exact mul_comm _ _
    · intro a ha
      obtain ⟨k, hk, rfl⟩ := ha
      change q (levelMap F ζ hζ U geometric (e (y, h * k))) = _
      rw [he]
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, levelMap_mul_right F ζ hζ U geometric k hk]
  simp_rw [hinner]
  have hm : Measurable (fun y : ArchGroup F => archimedeanInsertion F ζ hζ y * h) := by
    have hm' : Measurable (fun y : ArchGroup F => e (y, h)) :=
      hem.comp (measurable_id.prodMk measurable_const)
    simpa only [he] using hm'
  exact lintegral_const_mul _ (hfun.comp hm)

end DedekindZetaZeroFree.PGLComplex.AdelicSlicesRaw

end
