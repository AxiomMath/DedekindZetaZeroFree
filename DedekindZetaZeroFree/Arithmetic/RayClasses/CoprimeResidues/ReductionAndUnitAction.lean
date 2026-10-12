module

public import DedekindZetaZeroFree.Theta.RayClasses.WeightedIdealBlocks
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualsAndFractionalQuotients

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

abbrev coprimeIdealResidue (F : Type) [Field F] [NumberField F]
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥) :=
  fractionalIdealQuotient
    (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
    ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)

theorem coprimeIdealResidue_mem (a : Ideal (𝓞 F)) (ha : a ≠ ⊥)
    (x : 𝓞 F) (hx : x ∈ a) :
    (algebraMap (𝓞 F) F) x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F) := by
  exact FractionalIdeal.mem_coeIdeal_of_mem _ hx

 def integralToFractional (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    a →ₗ[𝓞 F] (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule where
  toFun x := ⟨algebraMap (𝓞 F) F x.val, coprimeIdealResidue_mem a ha x.val x.property⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (by simp [Algebra.smul_def])

 def integralFractionalEquiv (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    a ≃ₗ[𝓞 F] (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule :=
  LinearEquiv.ofBijective (integralToFractional a ha) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply IsFractionRing.injective (𝓞 F) F
      exact congrArg (fun z : (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule => z.val) h
    · intro x
      obtain ⟨y, hy, hxy⟩ := (FractionalIdeal.mem_coeIdeal _).mp x.property
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩)

 def integralReduction (m a : Ideal (𝓞 F)) : a →ₗ[𝓞 F] (𝓞 F ⧸ m) :=
  (Ideal.Quotient.mkₐ (𝓞 F) m).toLinearMap.comp a.subtype

 theorem integralReduction_surjective (m a : Ideal (𝓞 F)) (hcop : a ⊔ m = ⊤) :
    Function.Surjective (integralReduction m a) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hx : x ∈ a ⊔ m := by rw [hcop]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
  refine ⟨⟨y, hy⟩, ?_⟩
  change Ideal.Quotient.mk m y = Ideal.Quotient.mk m x
  rw [← hyz, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hz, add_zero]

 def fractionalReduction (m a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :=
  (integralReduction m a).comp (integralFractionalEquiv a ha).symm.toLinearMap

 theorem fractionalReduction_kernel (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ha : a ≠ ⊥) (hcop : a ⊔ m = ⊤) :
    (((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule.comap
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule.subtype) =
      (fractionalReduction m a ha).ker := by
  ext x
  let y := (integralFractionalEquiv a ha).symm x
  have hy : algebraMap (𝓞 F) F y.val = x.val :=
    congrArg Subtype.val ((integralFractionalEquiv a ha).apply_symm_apply x)
  change (x.val ∈ ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)) ↔ Ideal.Quotient.mk m y.val = 0
  change (x.val ∈ ((a : FractionalIdeal (𝓞 F)⁰ F) * (m : FractionalIdeal (𝓞 F)⁰ F))) ↔ _
  rw [← FractionalIdeal.coeIdeal_mul, ← hy, FractionalIdeal.mem_coeIdeal,
    Ideal.mul_eq_inf_of_coprime hcop, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · rintro ⟨z, hz, he⟩
    have : z = y.val := (IsFractionRing.injective (𝓞 F) F) he
    simpa [this] using hz.2
  · intro h
    exact ⟨y.val, ⟨y.property, h⟩, rfl⟩

def coprimeIdealResidueReduction (F : Type) [Field F] [NumberField F]
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) :
    coprimeIdealResidue F m a hm ha ≃ₗ[𝓞 F] (𝓞 F ⧸ m) := by
  exact (Submodule.quotEquivOfEq _ _ (fractionalReduction_kernel m a hm ha hcop)).trans
    ((fractionalReduction m a ha).quotKerEquivOfSurjective
      ((integralReduction_surjective m a hcop).comp
        (integralFractionalEquiv a ha).symm.surjective))

@[simp] theorem coprimeIdealResidueReduction_mk
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (x : 𝓞 F) (hx : x ∈ a) :
    coprimeIdealResidueReduction F m a hm ha hcop
      (fractionalIdealQuotientMk
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
        ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F)
        ⟨(algebraMap (𝓞 F) F) x, coprimeIdealResidue_mem a ha x hx⟩) =
      Ideal.Quotient.mk m x := by
  change (fractionalReduction m a ha)
    ⟨algebraMap (𝓞 F) F x, coprimeIdealResidue_mem a ha x hx⟩ = _
  have he : (integralFractionalEquiv a ha).symm
      ⟨algebraMap (𝓞 F) F x, coprimeIdealResidue_mem a ha x hx⟩ = ⟨x, hx⟩ :=
    (integralFractionalEquiv a ha).symm_apply_apply ⟨x, hx⟩
  change Ideal.Quotient.mk m ((integralFractionalEquiv a ha).symm _).val = _
  rw [he]

theorem coprimeIdealResidue_quotientMap_surjective
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) :
    Function.Surjective (fun x : a =>
      fractionalIdealQuotientMk
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
        ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F)
        ⟨(algebraMap (𝓞 F) F) x.val,
          coprimeIdealResidue_mem a ha x.val x.property⟩) := by
  exact (fractionalIdealQuotientMk_surjective _ _).comp
    (integralFractionalEquiv a ha).surjective

theorem coprimeIdealResidue_finite
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) : Finite (coprimeIdealResidue F m a hm ha) := by
  letI := Ring.HasFiniteQuotients.finiteQuotient hm
  exact Finite.of_equiv (𝓞 F ⧸ m) (coprimeIdealResidueReduction F m a hm ha hcop).symm.toEquiv

def coprimeIdealResidueUnits (F : Type) [Field F] [NumberField F]
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :=
  {q : coprimeIdealResidue F m a hm ha //
    IsUnit (coprimeIdealResidueReduction F m a hm ha hcop q)}

def coprimeIdealResidueUnitsEquiv (F : Type) [Field F] [NumberField F]
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    coprimeIdealResidueUnits F m a hm ha hcop hmt ≃ (𝓞 F ⧸ m)ˣ := by
  let e := coprimeIdealResidueReduction F m a hm ha hcop
  refine
    { toFun := fun q => q.property.unit
      invFun := fun u => ⟨e.symm (u : 𝓞 F ⧸ m), by simpa only [← show e = coprimeIdealResidueReduction F m a hm ha hcop from rfl, e.apply_symm_apply] using u.isUnit⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    apply Subtype.ext
    apply e.injective
    simp [e, IsUnit.unit_spec]
  · intro u
    apply Units.ext
    simp [IsUnit.unit_spec, ← show e = coprimeIdealResidueReduction F m a hm ha hcop from rfl]

@[simp] theorem coprimeIdealResidueUnitsEquiv_coe
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (q : coprimeIdealResidueUnits F m a hm ha hcop hmt) :
    (coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt q : 𝓞 F ⧸ m) =
      coprimeIdealResidueReduction F m a hm ha hcop q.val := by
  exact IsUnit.unit_spec q.property

@[instance_reducible] def coprimeIdealResidueUnitAction (F : Type) [Field F] [NumberField F]
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    MulAction (residueUnitImage F m)
      (coprimeIdealResidueUnits F m a hm ha hcop hmt) := by
  exact (coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt).mulAction
    (residueUnitImage F m)

theorem coprimeIdealResidueUnitAction_apply
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
    ∀ (g : residueUnitImage F m)
      (q : coprimeIdealResidueUnits F m a hm ha hcop hmt),
      coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt (g • q) =
        g.val * coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt q := by
  intro g q
  exact (coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt).apply_symm_apply _

theorem coprimeIdealResidueUnitAction_free
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
    ∀ q : coprimeIdealResidueUnits F m a hm ha hcop hmt,
      Function.Injective (fun g : residueUnitImage F m => g • q) := by
  intro q g h he
  have he' := congrArg (coprimeIdealResidueUnitsEquiv F m a hm ha hcop hmt) he
  rw [coprimeIdealResidueUnitAction_apply, coprimeIdealResidueUnitAction_apply] at he'
  exact Subtype.ext (mul_right_cancel he')

theorem coprimeIdealResidueUnitAction_orbit_card
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤) :
    letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
    ∀ q : coprimeIdealResidueUnits F m a hm ha hcop hmt,
      Nat.card (MulAction.orbit (residueUnitImage F m) q) =
        residueUnitImageCard F m ∧ 0 < residueUnitImageCard F m := by
  letI := coprimeIdealResidueUnitAction F m a hm ha hcop hmt
  intro q
  constructor
  · exact (Nat.card_congr (Equiv.ofInjective (fun g : residueUnitImage F m => g • q)
      (coprimeIdealResidueUnitAction_free m a hm ha hcop hmt q))).symm
  · exact residueUnitImageCard_pos hm

end DedekindZetaZeroFree.Hecke.Theta

end
