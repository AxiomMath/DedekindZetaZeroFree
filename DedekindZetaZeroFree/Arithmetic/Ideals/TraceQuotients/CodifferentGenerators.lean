module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PerfectTraceQuotientPairing
public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceQuotients.DualResidueGenerators
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.BalancedPairingGeneratorCharacter

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [hNF : NumberField F]

include hNF

def quotientPresentationEquiv
    (I J I' J' : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I = I') (hJ : J = J') :
    fractionalIdealQuotient I J ≃ₗ[NumberField.RingOfIntegers F]
      fractionalIdealQuotient I' J' := by
  subst I' J'
  exact LinearEquiv.refl _ _

private theorem quotientPresentationEquiv_mk
    (I J I' J' : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I = I') (hJ : J = J') (β : I.coeToSubmodule) :
    quotientPresentationEquiv I J I' J' hI hJ (fractionalIdealQuotientMk I J β) =
      fractionalIdealQuotientMk I' J' ⟨(β : F), by rw [← hI]; exact β.property⟩ := by
  subst I' J'
  rfl

theorem traceNumerator_eq
    (m : Ideal (NumberField.RingOfIntegers F)) :
    (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ * codifferentFractionalIdeal F =
      rayDualResidueNumerator m 1 := (rayDualResidueNumerator_one m).symm

theorem traceDenominator_eq :
    codifferentFractionalIdeal F = rayDualFractionalIdeal (1 : FractionalIdeal
      (NumberField.RingOfIntegers F)⁰ F) := rayDualFractionalIdeal_one.symm

theorem traceQuotient_torsion
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    Module.IsTorsionBySet (NumberField.RingOfIntegers F) (rayTraceQuotient m)
      (m : Set (NumberField.RingOfIntegers F)) := by
  apply fractionalIdealQuotient_isTorsionBySet m
  · rw [traceNumerator_eq m, traceDenominator_eq]
    exact rayDualResidue_denominator_le m 1 hm one_ne_zero
  · rw [traceNumerator_eq m, traceDenominator_eq, mul_comm]
    exact rayDualResidue_mul_eq m 1 hm one_ne_zero

def rayTraceQuotientDualResidueEquiv
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    letI := rayTraceQuotientModule m hm
    rayTraceQuotient m ≃ₗ[NumberField.RingOfIntegers F ⧸ m]
      rayDualResidueModule m (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) := by
  letI := rayTraceQuotientModule m hm
  letI := (traceQuotient_torsion m hm).isScalarTower (S := NumberField.RingOfIntegers F)
  letI := (rayDualResidueModule_isTorsionBySet m 1).isScalarTower
    (S := NumberField.RingOfIntegers F)
  exact LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (quotientPresentationEquiv _ _ _ _ (traceNumerator_eq m) traceDenominator_eq)

@[simp] theorem rayTraceQuotientDualResidueEquiv_mk
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (β : ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
      codifferentFractionalIdeal F).coeToSubmodule) :
    rayTraceQuotientDualResidueEquiv m hm
      (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β) =
      Submodule.Quotient.mk (p := rayDualResidueDenominator m 1)
        ⟨(β : F), by
          rw [rayDualResidueNumerator_one]
          exact β.property⟩ := by
  exact quotientPresentationEquiv_mk _ _ _ _ (traceNumerator_eq m) traceDenominator_eq β

def rayTraceQuotientGenerator
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) : rayTraceQuotient m :=
  (rayTraceQuotientDualResidueEquiv m hm).symm
    (rayDualResidueGenerator m 1 hm one_ne_zero)

theorem rayTraceQuotientGenerator_bijective
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    letI := rayTraceQuotientModule m hm
    Function.Bijective (LinearMap.toSpanSingleton (NumberField.RingOfIntegers F ⧸ m)
      (rayTraceQuotient m) (rayTraceQuotientGenerator m hm)) := by
  letI := rayTraceQuotientModule m hm
  have he : (LinearMap.toSpanSingleton (NumberField.RingOfIntegers F ⧸ m)
      _ (rayTraceQuotientGenerator m hm) : _ → _) =
      (rayTraceQuotientDualResidueEquiv m hm).symm ∘
        LinearMap.toSpanSingleton (NumberField.RingOfIntegers F ⧸ m) _
          (rayDualResidueGenerator m 1 hm one_ne_zero) := by
    funext k
    exact ((rayTraceQuotientDualResidueEquiv m hm).symm.map_smul k _).symm
  rw [he]
  exact (rayTraceQuotientDualResidueEquiv m hm).symm.bijective.comp
    (rayDualResidueGenerator_bijective m 1 hm one_ne_zero)

def rayTraceGeneratorChar
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (z : rayTraceQuotient m) : AddChar (NumberField.RingOfIntegers F ⧸ m) ℂ :=
  rayTraceQuotientPairingTransposeEquiv m hm z

@[simp] theorem rayTraceGeneratorChar_apply
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (z : rayTraceQuotient m) (k : NumberField.RingOfIntegers F ⧸ m) :
    rayTraceGeneratorChar m hm z k = rayTraceQuotientPairing m hm k z := by
  exact rayTraceQuotientPairingTransposeEquiv_apply m hm z k

theorem rayTraceGeneratorChar_primitive
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    letI := rayTraceQuotientModule m hm
    ∀ (z : rayTraceQuotient m)
      (hz : Function.Bijective (LinearMap.toSpanSingleton (NumberField.RingOfIntegers F ⧸ m)
        (rayTraceQuotient m) z)) (J : Ideal (NumberField.RingOfIntegers F ⧸ m)),
      (∀ k ∈ J, rayTraceGeneratorChar m hm z k = 1) → J = ⊥ := by
  letI := rayTraceQuotientModule m hm
  intro z hz J hJ
  apply balancedPairingGeneratorChar_primitive (rayTraceQuotientPairing m hm)
    (rayTraceQuotientPairing_zero_left m hm)
    (rayTraceQuotientPairing_add_left m hm)
    (rayTraceQuotientPairing_balance m hm)
    (fun k h => (rayTraceQuotientPairing_left_radical m hm k).mp h) z hz.2 J
  intro k hk
  simpa only [balancedPairingGeneratorChar_apply, rayTraceGeneratorChar_apply] using hJ k hk

theorem rayTraceQuotientGenerator_lift_coprime
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) :
    letI := rayTraceQuotientModule m hm
    ∀ (z : rayTraceQuotient m)
      (hz : Function.Bijective (LinearMap.toSpanSingleton (NumberField.RingOfIntegers F ⧸ m)
        (rayTraceQuotient m) z))
      (β : ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F).coeToSubmodule),
      fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β = z →
      (β : F) ≠ 0 ∧ ∃ b : Ideal (NumberField.RingOfIntegers F),
        b ≠ ⊥ ∧ m ⊔ b = ⊤ ∧
        (b : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
          FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (β : F) *
            (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) * rayDifferentFrac F ∧
        FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (β : F) =
          (b : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) *
            ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
              codifferentFractionalIdeal F) := by
  letI := rayTraceQuotientModule m hm
  intro z hz β hlift
  let e := rayTraceQuotientDualResidueEquiv m hm
  have hz' : Function.Surjective (fun k : NumberField.RingOfIntegers F ⧸ m => k • e z) := by
    intro y
    obtain ⟨k, hk⟩ := hz.2 (e.symm y)
    refine ⟨k, ?_⟩
    change k • z = e.symm y at hk
    change k • e z = y
    rw [← e.map_smul, hk, e.apply_symm_apply]
  have hβ : (β : F) ∈ rayDualResidueNumerator m 1 := by
    rw [rayDualResidueNumerator_one]
    exact β.property
  have hlift' : Submodule.Quotient.mk (p := rayDualResidueDenominator m 1)
      ⟨(β : F), hβ⟩ = e z := by
    rw [← rayTraceQuotientDualResidueEquiv_mk m hm β, hlift]
  simpa only [one_mul, rayDualResidueNumerator_one, rayCodifferent,
    codifferentFractionalIdeal, traceDualFractionalIdeal] using
    rayDualResidueGenerator_lift_coprime m 1 hm hm1 one_ne_zero (e z) hz'
      (β : F) hβ hlift'

theorem rayTraceQuotientGenerator_exists_coprime_lift
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) (hm1 : m ≠ ⊤) :
    ∃ (β : ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F).coeToSubmodule) (b : Ideal (NumberField.RingOfIntegers F)),
      fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β =
        rayTraceQuotientGenerator m hm ∧
      (β : F) ≠ 0 ∧ b ≠ ⊥ ∧ m ⊔ b = ⊤ ∧
      (b : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
        FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (β : F) *
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) * rayDifferentFrac F ∧
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (β : F) =
        (b : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) *
          ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
            codifferentFractionalIdeal F) := by
  obtain ⟨β, hlift⟩ := fractionalIdealQuotientMk_surjective _ _
    (rayTraceQuotientGenerator m hm)
  obtain ⟨hn, b, hb0, hcop, hb, hp⟩ := rayTraceQuotientGenerator_lift_coprime
    m hm hm1 (rayTraceQuotientGenerator m hm)
      (rayTraceQuotientGenerator_bijective m hm) β hlift
  exact ⟨β, b, hlift, hn, hb0, hcop, hb, hp⟩

end DedekindZetaZeroFree.Hecke

end
