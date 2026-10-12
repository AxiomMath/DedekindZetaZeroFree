module

public import ClassFieldTheory.All
public import DedekindZetaZeroFree.Adeles.Approximation.FiniteStrongApproximation

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

def integralFiniteAdeles (F : Type*) [Field F] [NumberField F] :
    AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro v; exact (v.adicCompletionIntegers F).zero_mem
  add_mem' := by intro x y hx hy v; exact (v.adicCompletionIntegers F).toSubring.add_mem (hx v) (hy v)
  neg_mem' := by intro x hx v; exact (v.adicCompletionIntegers F).toSubring.neg_mem (hx v)

def integerScaleHom {A : Type*} [AddCommGroup A] (n : ℤ) : A →+ A where
  toFun x := n • x
  map_zero' := by simp
  map_add' := by intros; simp [smul_add]

def integerScaledSubgroup {A : Type*} [AddCommGroup A] (n : ℤ) (H : AddSubgroup A) :
    AddSubgroup A := H.map (integerScaleHom n)

def integerFieldSubgroup (F : Type*) [Field F] [NumberField F] : AddSubgroup F :=
  (algebraMap (𝓞 F) F).toAddMonoidHom.range

def finiteLevelFieldSubgroup {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) : AddSubgroup F :=
  K.comap (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toAddMonoidHom

def finiteLevelLattice {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    Submodule ℤ (NumberField.mixedEmbedding.mixedSpace F) :=
  (finiteLevelFieldSubgroup K).toIntSubmodule.map
    (NumberField.mixedEmbedding F).toIntAlgHom.toLinearMap

theorem mem_finiteLevelLattice_iff {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    x ∈ finiteLevelLattice K ↔ ∃ lam : F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) lam ∈ K ∧ NumberField.mixedEmbedding F lam = x := by
  rfl

def finiteLevelDiagonal {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) : finiteLevelFieldSubgroup K →+ K where
  toFun x := ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) x, x.property⟩
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

namespace FiniteLevelHelpers

theorem integral_diagonal_iff {F : Type*} [Field F] [NumberField F] (x : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) x ∈ integralFiniteAdeles F ↔
      x ∈ integerFieldSubgroup F := by
  constructor
  · intro hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one F x
    intro v
    have hv := hx v
    simpa only [FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv
  · rintro ⟨z, rfl⟩ v
    change ((algebraMap (𝓞 F) F z : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v z

theorem scaled_integral_diagonal_iff {F : Type*} [Field F] [NumberField F]
    (a : ℕ) (ha : 0 < a) (x : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) x ∈
        integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ↔
      x ∈ integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F) := by
  constructor
  · rintro ⟨y, hy, heq⟩
    let z : F := (a : F)⁻¹ * x
    have hz : (a : ℤ) • z = x := by
      simp [z, zsmul_eq_mul, show (a : F) ≠ 0 by exact_mod_cast ha.ne']
    have hdiag : algebraMap F (FiniteAdeleRing (𝓞 F) F) z = y := by
      apply smul_right_injective (FiniteAdeleRing (𝓞 F) F)
        (show (a : F) ≠ 0 by exact_mod_cast ha.ne')
      have h : (a : ℤ) • algebraMap F (FiniteAdeleRing (𝓞 F) F) z = (a : ℤ) • y := by
        rw [← map_zsmul, hz]
        exact heq.symm
      simpa only [natCast_zsmul, ← Nat.cast_smul_eq_nsmul F] using h
    exact ⟨z, (integral_diagonal_iff z).mp (hdiag ▸ hy), hz⟩
  · rintro ⟨z, hz, heq⟩
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) z, (integral_diagonal_iff z).mpr hz, ?_⟩
    change (a : ℤ) • algebraMap F (FiniteAdeleRing (𝓞 F) F) z = _
    rw [← map_zsmul]
    exact congrArg (algebraMap F (FiniteAdeleRing (𝓞 F) F)) heq

 theorem compact_open_bound {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (H K : AddSubgroup A)
    (hH : IsCompact (H : Set A)) (hK : IsOpen (K : Set A)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ H, (n : ℤ) • x ∈ K := by
  let q := QuotientAddGroup.mk' K
  letI : DiscreteTopology (A ⧸ K) := QuotientAddGroup.discreteTopology hK
  have hc : IsCompact (H.map q : Set (A ⧸ K)) := by
    change IsCompact (q '' (H : Set A))
    exact hH.image QuotientAddGroup.continuous_mk
  letI : Finite (H.map q) := hc.finite_of_discrete.to_subtype
  refine ⟨Nat.card (H.map q), Nat.card_pos, ?_⟩
  intro x hx
  have hh : Nat.card (H.map q) • (⟨q x, ⟨x, hx, rfl⟩⟩ : H.map q) = 0 := card_nsmul_eq_zero'
  have hh' : Nat.card (H.map q) • q x = 0 := congrArg Subtype.val hh
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change q ((Nat.card (H.map q) : ℤ) • x) = 0
  simpa only [map_zsmul, natCast_zsmul, map_nsmul] using hh'

 theorem integral_isOpen (F : Type*) [Field F] [NumberField F] :
    IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  exact RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

set_option backward.isDefEq.respectTransparency false in
 theorem integral_isCompact (F : Type*) [Field F] [NumberField F] :
    IsCompact (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  letI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => by
      apply isCompact_iff_compactSpace.mp
      change IsCompact ((Valued.integer (v.adicCompletion F)) : Set (v.adicCompletion F))
      exact isCompact_iff_compactSpace.mpr
        (Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance)
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set _)) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

 theorem scaled_integral_isOpen {F : Type*} [Field F] [NumberField F] (a : ℕ) (ha : 0 < a) :
    IsOpen (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) :
      Set (FiniteAdeleRing (𝓞 F) F)) := by
  let A := FiniteAdeleRing (𝓞 F) F
  let u : Aˣ := (Units.mk0 (a : F) (by exact_mod_cast ha.ne')).map (algebraMap F A)
  have hu (x : A) : ContinuousAddEquiv.mulLeft u x = (a : ℤ) • x := by
    simp [u, zsmul_eq_mul]
  have heq : (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set A) =
      (ContinuousAddEquiv.mulLeft u).toHomeomorph '' (integralFiniteAdeles F : Set A) := by
    ext x
    change (∃ y ∈ integralFiniteAdeles F, integerScaleHom (a : ℤ) y = x) ↔ _
    change (∃ y ∈ integralFiniteAdeles F, (a : ℤ) • y = x) ↔
      (∃ y ∈ integralFiniteAdeles F, ContinuousAddEquiv.mulLeft u y = x)
    simp only [hu]
  rw [heq]
  exact (ContinuousAddEquiv.mulLeft u).toHomeomorph.isOpenMap _ (integral_isOpen F)

end FiniteLevelHelpers

open FiniteLevelHelpers in

theorem finiteLevel_integer_bounds {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K ∧
      K ≤ (integralFiniteAdeles F).comap (integerScaleHom (b : ℤ)) ∧
      integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F) ≤ finiteLevelFieldSubgroup K ∧
      finiteLevelFieldSubgroup K ≤ (integerFieldSubgroup F).comap (integerScaleHom (b : ℤ)) := by
  obtain ⟨a, ha, hlow⟩ := compact_open_bound (integralFiniteAdeles F) K (integral_isCompact F) hopen
  obtain ⟨b, hb, hupp⟩ := compact_open_bound K (integralFiniteAdeles F) hcompact (integral_isOpen F)
  have hl : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    exact hlow y hy
  refine ⟨a, b, ha, hb, hl, hupp, ?_, ?_⟩
  · intro x hx
    exact hl ((scaled_integral_diagonal_iff a ha x).mpr hx)
  · intro x hx
    apply (integral_diagonal_iff _).mp
    change algebraMap F (FiniteAdeleRing (𝓞 F) F) ((b : ℤ) • x) ∈ _
    rw [map_zsmul]
    exact hupp _ hx

theorem finiteLevelLattice_discrete {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    DiscreteTopology (finiteLevelLattice K) := by
  obtain ⟨a, b, ha, hb, h₁, h₂, h₃, h₄⟩ := finiteLevel_integer_bounds K hcompact hopen
  let g : finiteLevelLattice K → mixedEmbedding.integerLattice F := fun x =>
    ⟨(b : ℤ) • x.val, by
      obtain ⟨lam, hlam, heq⟩ := (mem_finiteLevelLattice_iff K x.val).mp x.property
      rw [← heq]
      obtain ⟨z, hz⟩ := h₄ hlam
      refine ⟨z, ?_⟩
      change mixedEmbedding F (algebraMap (𝓞 F) F z) = (b : ℤ) • mixedEmbedding F lam
      change algebraMap (𝓞 F) F z = (b : ℤ) • lam at hz
      rw [hz]
      exact (mixedEmbedding F).map_zsmul (b : ℤ) lam⟩
  apply DiscreteTopology.of_continuous_injective (f := g)
  · exact (continuous_subtype_val.zsmul (b : ℤ)).subtype_mk _
  · intro x y hxy
    apply Subtype.ext
    exact smul_right_injective (mixedEmbedding.mixedSpace F)
      (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne') (congrArg Subtype.val hxy)

theorem finiteLevelLattice_full_rank {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    letI := finiteLevelLattice_discrete K hcompact hopen
    IsZLattice ℝ (finiteLevelLattice K) ∧
      Module.finrank ℤ (finiteLevelLattice K) = Module.finrank ℚ F := by
  letI := finiteLevelLattice_discrete K hcompact hopen
  obtain ⟨a, b, ha, hb, h₁, h₂, h₃, h₄⟩ := finiteLevel_integer_bounds K hcompact hopen
  have hspan : Submodule.span ℝ (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F)) ≤
      Submodule.span ℝ (finiteLevelLattice K : Set (mixedEmbedding.mixedSpace F)) := by
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ Submodule.span ℝ (finiteLevelLattice K : Set (mixedEmbedding.mixedSpace F))
    obtain ⟨z, hz⟩ := hx
    change mixedEmbedding F (algebraMap (𝓞 F) F z) = x at hz
    have hax : (a : ℤ) • x ∈ finiteLevelLattice K := by
      apply (mem_finiteLevelLattice_iff K _).mpr
      refine ⟨(a : ℤ) • algebraMap (𝓞 F) F z, h₃ ?_, ?_⟩
      · exact ⟨algebraMap (𝓞 F) F z, ⟨z, rfl⟩, rfl⟩
      · rw [map_zsmul, hz]
    have hs := (Submodule.span ℝ (finiteLevelLattice K : Set (mixedEmbedding.mixedSpace F))).smul_mem
      ((a : ℝ)⁻¹) (Submodule.subset_span hax)
    simpa only [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℝ a x,
      smul_smul, inv_mul_cancel₀ (show (a : ℝ) ≠ 0 by exact_mod_cast ha.ne'), one_smul] using hs
  letI : IsZLattice ℝ (finiteLevelLattice K) := ⟨by
    apply top_unique
    rw [← IsZLattice.span_top (L := mixedEmbedding.integerLattice F)]
    exact hspan⟩
  exact ⟨inferInstance, (ZLattice.rank ℝ (finiteLevelLattice K)).trans
    (mixedEmbedding.finrank F)⟩

open FiniteLevelHelpers in

theorem finiteLevel_quotient_comparison {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (a : ℕ) (ha : 0 < a)
    (hlevel : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K) :
    let H := (integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F)).comap
      (finiteLevelFieldSubgroup K).subtype
    let U := (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).comap K.subtype
    Finite (finiteLevelFieldSubgroup K ⧸ H) ∧ Finite (K ⧸ U) ∧
      ∃ e : (finiteLevelFieldSubgroup K ⧸ H) ≃+ (K ⧸ U),
        ∀ x : finiteLevelFieldSubgroup K,
          e (QuotientAddGroup.mk x) = QuotientAddGroup.mk (finiteLevelDiagonal K x) := by
  let H := (integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F)).comap
      (finiteLevelFieldSubgroup K).subtype
  let U := (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).comap K.subtype
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  letI : DiscreteTopology (K ⧸ U) := QuotientAddGroup.discreteTopology
    ((scaled_integral_isOpen a ha).preimage continuous_subtype_val)
  letI : Finite (K ⧸ U) := finite_of_compact_of_discrete
  let φ : finiteLevelFieldSubgroup K →+ (K ⧸ U) :=
    (QuotientAddGroup.mk' U).comp (finiteLevelDiagonal K)
  have hker : H = φ.ker := by
    ext x
    change ((x : F) ∈ integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F)) ↔
      QuotientAddGroup.mk (finiteLevelDiagonal K x) = (0 : K ⧸ U)
    rw [QuotientAddGroup.eq_zero_iff]
    exact (scaled_integral_diagonal_iff a ha (x : F)).symm
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    let V := {y : FiniteAdeleRing (𝓞 F) F |
      y - x.val ∈ integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)}
    have hV : IsOpen V := (scaled_integral_isOpen a ha).preimage (continuous_id.sub continuous_const)
    have hxV : x.val ∈ V := by
      change x.val - x.val ∈ integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)
      simp
    obtain ⟨lam, hlam⟩ := (finiteAdele_dense F).exists_mem_open hV ⟨x.val, hxV⟩
    have hlamK : algebraMap F (FiniteAdeleRing (𝓞 F) F) lam ∈ K := by
      have ht := K.add_mem (hlevel hlam) x.property
      simpa only [sub_add_cancel] using ht
    refine ⟨⟨lam, hlamK⟩, ?_⟩
    change QuotientAddGroup.mk (finiteLevelDiagonal K ⟨lam, hlamK⟩) = QuotientAddGroup.mk x
    apply QuotientAddGroup.eq.mpr
    change -algebraMap F (FiniteAdeleRing (𝓞 F) F) lam + x.val ∈
      integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)
    have ht : -(algebraMap F (FiniteAdeleRing (𝓞 F) F) lam - x.val) ∈
        integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) :=
      (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).neg_mem hlam
    simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using ht
  let e : (finiteLevelFieldSubgroup K ⧸ H) ≃+ (K ⧸ U) :=
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)
  have hfin : Finite (finiteLevelFieldSubgroup K ⧸ H) := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, inferInstance, e, ?_⟩
  intro x
  change QuotientAddGroup.kerLift φ
    (QuotientAddGroup.quotientAddEquivOfEq hker (QuotientAddGroup.mk x)) = _
  rw [QuotientAddGroup.quotientAddEquivOfEq_mk, QuotientAddGroup.kerLift_mk]
  rfl

end
end DedekindZetaZeroFree
