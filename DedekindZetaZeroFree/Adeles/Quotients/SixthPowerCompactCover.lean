module

public import DedekindZetaZeroFree.Adeles.Quotients.NormOneSUnitCompactness
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientDimensions
public import DedekindZetaZeroFree.Geometry.CompactQuotientLifts

@[expose] public section

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

instance finiteIndex_Gamma1_subgroupOf_L :
    (A.Gamma1.subgroupOf A.L).FiniteIndex := by
  letI : Finite (PowerQuotient A.Rˣ 6) := A.sunit_structure_and_power_quotients.2.2.2.2
  letI : ((powMonoidHom (α := A.Rˣ) 6).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hU : A.unitSixthPowers =
      ((powMonoidHom (α := A.Rˣ) 6).range).comap A.unitEquiv.toMonoidHom := by
    ext u
    change (∃ v : A.U, v ^ 6 = u) ↔ ∃ v : A.Rˣ, v ^ 6 = A.unitEquiv u
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨A.unitEquiv v, (map_pow A.unitEquiv v 6).symm⟩
    · rintro ⟨v, hv⟩
      refine ⟨A.unitEquiv.symm v, ?_⟩
      apply A.unitEquiv.injective
      simpa using hv
  letI : A.unitSixthPowers.FiniteIndex := hU ▸ inferInstance
  have hm := Subgroup.FiniteIndex.map_of_surjective A.unitSixthPowers
    A.diagonalS.rangeRestrict_surjective
  have hEq : A.Gamma1.subgroupOf A.L =
      A.unitSixthPowers.map A.diagonalS.rangeRestrict := by
    rw [A.Gamma1_eq_sixthPower_image]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, Subtype.ext hux⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨u, hu, congrArg Subtype.val hux⟩
  exact hEq ▸ hm

theorem exists_compact_balanced_cover :
    ∃ K_bal : Set A.G1, IsCompact K_bal ∧
      ∀ y : A.G1, ∃ γ : A.Gamma1, (γ : A.G1) * y ∈ K_bal := by
  classical
  have hrel : MulAction.orbitRel A.L A.G1 = QuotientGroup.leftRel A.L := by
    change QuotientGroup.rightRel A.L = _
    apply Setoid.ext
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply, mul_comm]
  letI : CompactSpace (Quotient (MulAction.orbitRel A.L A.G1)) :=
    hrel ▸ (inferInstance : CompactSpace (A.G1 ⧸ A.L))
  obtain ⟨K, hK, hcover⟩ := exists_compact_subgroup_left_translates A.L
  let H := A.Gamma1.subgroupOf A.L
  let Q := A.L ⧸ H
  let r : Q → A.L := Quotient.out
  refine ⟨⋃ q : Q, (fun x : A.G1 => (r q : A.G1)⁻¹ * x) '' K,
    isCompact_iUnion (fun q => hK.image (continuous_const.mul continuous_id)), ?_⟩
  intro y
  obtain ⟨l, hl⟩ := hcover y
  let q : Q := QuotientGroup.mk l
  have hq : (l : Q) = (r q : Q) := (Quotient.out_eq q).symm
  have hd : l / r q ∈ H := QuotientGroup.eq_iff_div_mem.mp hq
  let γ : A.Gamma1 := ⟨(l / r q : A.L).val, hd⟩
  refine ⟨γ, Set.mem_iUnion.mpr ⟨q, l.val * y, hl, ?_⟩⟩
  dsimp [γ]
  simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

instance compactSpace_Gamma1Quotient : CompactSpace (A.G1 ⧸ A.Gamma1) := by
  obtain ⟨K, hK, hcover⟩ := A.exists_compact_balanced_cover
  have heq : QuotientGroup.mk '' K = (Set.univ : Set (A.G1 ⧸ A.Gamma1)) := by
    rw [Set.eq_univ_iff_forall]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨γ, hγ⟩ := hcover y
    refine ⟨γ.val * y, hγ, ?_⟩
    change QuotientGroup.mk' A.Gamma1 (γ.val * y) = QuotientGroup.mk' A.Gamma1 y
    rw [map_mul]
    have hγone : QuotientGroup.mk' A.Gamma1 γ.val = 1 :=
      (QuotientGroup.eq_one_iff γ.val).mpr γ.prop
    rw [hγone, one_mul]
  exact isCompact_univ_iff.mp (heq ▸ hK.image QuotientGroup.continuous_mk)

end
end SArithmeticData
end DedekindZetaZeroFree
