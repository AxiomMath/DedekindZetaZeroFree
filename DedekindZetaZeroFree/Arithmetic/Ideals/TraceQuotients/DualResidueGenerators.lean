module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.RankOne
public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.CoprimeGeneratorLifts
public import DedekindZetaZeroFree.Algebra.RankOneModules.GeneratorTorsor
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualIdeal

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

def rayCodifferent (F : Type*) [Field F] [NumberField F] :
    FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

def rayDifferentFrac (F : Type*) [Field F] [NumberField F] :
    FractionalIdeal (𝓞 F)⁰ F := (rayCodifferent F)⁻¹

def rayDualFractionalIdeal (a : FractionalIdeal (𝓞 F)⁰ F) :
    FractionalIdeal (𝓞 F)⁰ F := rayCodifferent F * a⁻¹

def rayDualResidueNumerator (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F :=
  rayDualFractionalIdeal (a * (m : FractionalIdeal (𝓞 F)⁰ F))

abbrev rayDualResidueDenominator (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) :
    Submodule (𝓞 F) (rayDualResidueNumerator m a : Submodule (𝓞 F) F) :=
  Submodule.comap (rayDualResidueNumerator m a : Submodule (𝓞 F) F).subtype
    (rayDualFractionalIdeal a : Submodule (𝓞 F) F)

abbrev rayDualResidueModule (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) :=
  (rayDualResidueNumerator m a : Submodule (𝓞 F) F) ⧸
    rayDualResidueDenominator m a

theorem rayCodifferent_ne_zero : rayCodifferent F ≠ 0 := by
  exact FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero

theorem rayDualResidueNumerator_ne_zero (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    rayDualResidueNumerator m a ≠ 0 := by
  exact mul_ne_zero rayCodifferent_ne_zero
    (inv_ne_zero (mul_ne_zero ha (FractionalIdeal.coeIdeal_ne_zero.mpr hm)))

theorem rayDualResidue_mul_eq (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    (m : FractionalIdeal (𝓞 F)⁰ F) * rayDualResidueNumerator m a =
      rayDualFractionalIdeal a := by
  have hM : (m : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hm
  simp only [rayDualResidueNumerator, rayDualFractionalIdeal, mul_inv_rev]
  calc
    _ = rayCodifferent F * a⁻¹ *
        ((m : FractionalIdeal (𝓞 F)⁰ F) * (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem rayDualResidue_denominator_le (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    rayDualFractionalIdeal a ≤ rayDualResidueNumerator m a := by
  rw [← rayDualResidue_mul_eq m a hm ha]
  exact fractionalResidue_mul_le m (rayDualResidueNumerator m a)

theorem rayDualResidueDenominator_eq (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    rayDualResidueDenominator m a =
      fractionalResidueDenominator m (rayDualResidueNumerator m a) := by
  unfold rayDualResidueDenominator fractionalResidueDenominator
  rw [rayDualResidue_mul_eq m a hm ha]

theorem rayDualResidueModule_isTorsionBySet (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) :
    Module.IsTorsionBySet (𝓞 F) (rayDualResidueModule m a) (m : Set (𝓞 F)) := by
  by_cases hm : m = ⊥
  · subst m
    intro x r
    have hr : (r : 𝓞 F) = 0 := r.property
    rw [hr, zero_smul]
  by_cases ha : a = 0
  · subst a
    have hI : rayDualResidueNumerator m (0 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
      simp [rayDualResidueNumerator, rayDualFractionalIdeal]
    intro x r
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y = 0 := by
      apply Subtype.ext
      have := y.property
      simpa [hI] using this
    rw [hy, Submodule.Quotient.mk_zero, smul_zero]
  change Module.IsTorsionBySet (𝓞 F)
    ((rayDualResidueNumerator m a : Submodule (𝓞 F) F) ⧸
      rayDualResidueDenominator m a) (m : Set (𝓞 F))
  rw [rayDualResidueDenominator_eq m a hm ha]
  exact fractionalResidueModule_isTorsionBySet m (rayDualResidueNumerator m a)

noncomputable instance rayDualResidueModuleModule (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) :
    Module ((𝓞 F) ⧸ m) (rayDualResidueModule m a) :=
  (rayDualResidueModule_isTorsionBySet m a).module

noncomputable def rayDualResidueModuleEquiv (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    rayDualResidueModule m a ≃ₗ[(𝓞 F) ⧸ m]
      fractionalResidueModule m (rayDualResidueNumerator m a) := by
  letI := (rayDualResidueModule_isTorsionBySet m a).isScalarTower (S := 𝓞 F)
  letI := (fractionalResidueModule_isTorsionBySet m
    (rayDualResidueNumerator m a)).isScalarTower (S := 𝓞 F)
  exact LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Submodule.quotEquivOfEq _ _ (rayDualResidueDenominator_eq m a hm ha))

@[simp] theorem rayDualResidueModuleEquiv_mk (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0)
    (x : (rayDualResidueNumerator m a : Submodule (𝓞 F) F)) :
    rayDualResidueModuleEquiv m a hm ha
      (Submodule.Quotient.mk (p := rayDualResidueDenominator m a) x) =
        Submodule.Quotient.mk
          (p := fractionalResidueDenominator m (rayDualResidueNumerator m a)) x := by
  exact Submodule.quotEquivOfEq_mk _ _ (rayDualResidueDenominator_eq m a hm ha) x

noncomputable def rayDualResidueEquiv (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    ((𝓞 F) ⧸ m) ≃ₗ[(𝓞 F) ⧸ m] rayDualResidueModule m a :=
  (fractionalResidueEquiv m (rayDualResidueNumerator m a) hm
    (rayDualResidueNumerator_ne_zero m a hm ha)).trans
      (rayDualResidueModuleEquiv m a hm ha).symm

noncomputable def rayDualResidueGenerator (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    rayDualResidueModule m a := rayDualResidueEquiv m a hm ha 1

theorem rayDualResidueGenerator_bijective (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (ha : a ≠ 0) :
    Function.Bijective (LinearMap.toSpanSingleton ((𝓞 F) ⧸ m)
      (rayDualResidueModule m a) (rayDualResidueGenerator m a hm ha)) := by
  have he : (LinearMap.toSpanSingleton ((𝓞 F) ⧸ m)
      (rayDualResidueModule m a) (rayDualResidueGenerator m a hm ha) :
      ((𝓞 F) ⧸ m) → rayDualResidueModule m a) = rayDualResidueEquiv m a hm ha := by
    funext k
    change k • rayDualResidueEquiv m a hm ha 1 = rayDualResidueEquiv m a hm ha k
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [he]
  exact (rayDualResidueEquiv m a hm ha).bijective

theorem rayDualResidueGenerator_lift_coprime (m : Ideal (𝓞 F))
    (a : FractionalIdeal (𝓞 F)⁰ F) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) (ha : a ≠ 0)
    (z : rayDualResidueModule m a)
    (hz : Function.Surjective (fun k : (𝓞 F) ⧸ m => k • z))
    (β : F) (hβ : β ∈ rayDualResidueNumerator m a)
    (hlift : Submodule.Quotient.mk (p := rayDualResidueDenominator m a)
      ⟨β, hβ⟩ = z) :
    β ≠ 0 ∧ ∃ b : Ideal (𝓞 F),
      b ≠ ⊥ ∧ m ⊔ b = ⊤ ∧
      (b : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ β *
        (a * (m : FractionalIdeal (𝓞 F)⁰ F)) * rayDifferentFrac F ∧
      FractionalIdeal.spanSingleton (𝓞 F)⁰ β =
        (b : FractionalIdeal (𝓞 F)⁰ F) * rayDualResidueNumerator m a := by
  let e := rayDualResidueModuleEquiv m a hm ha
  have hz' : Function.Surjective (fun k : (𝓞 F) ⧸ m => k • e z) := by
    intro y
    obtain ⟨k, hk⟩ := hz (e.symm y)
    refine ⟨k, ?_⟩
    change k • z = e.symm y at hk
    change k • e z = y
    rw [← e.map_smul, hk, e.apply_symm_apply]
  have hlift' : Submodule.Quotient.mk
      (p := fractionalResidueDenominator m (rayDualResidueNumerator m a))
      ⟨β, hβ⟩ = e z := by
    rw [← rayDualResidueModuleEquiv_mk m a hm ha, hlift]
  have hn := (fractionalResidueGenerator_lift_properties m _ hm hm1
    (rayDualResidueNumerator_ne_zero m a hm ha) (e z) hz' β hβ hlift').1
  obtain ⟨b, hb, hb0, hcop, hprincipal⟩ :=
    fractionalResidueGenerator_lift_coprime_ideal m _ hm hm1
      (rayDualResidueNumerator_ne_zero m a hm ha) (e z) hz' β hβ hlift'
  refine ⟨hn, b, hb0, hcop, ?_, hprincipal⟩
  rw [hb]
  simp only [fractionalResidueLiftIdeal, rayDualResidueNumerator,
    rayDualFractionalIdeal, rayDifferentFrac, mul_inv_rev, inv_inv]
  ac_rfl

@[simp] theorem rayDualResidueNumerator_one (m : Ideal (𝓞 F)) :
    rayDualResidueNumerator m 1 =
      (m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * rayCodifferent F := by
  simp only [rayDualResidueNumerator, rayDualFractionalIdeal, one_mul]
  exact mul_comm _ _

@[simp] theorem rayDualFractionalIdeal_one :
    rayDualFractionalIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) = rayCodifferent F := by
  simp [rayDualFractionalIdeal]

end

end DedekindZetaZeroFree.Hecke
