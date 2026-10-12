module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.IdealRatioEquivalence
public import DedekindZetaZeroFree.Arithmetic.Ideals.TracePhaseAnnihilator

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

theorem conductorScaledIdeal_ne_zero
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≠ 0 := by
  exact mul_ne_zero ha (FractionalIdeal.coeIdeal_ne_zero.mpr hm)

theorem conductorScaledIdeal_le
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≤ a := by
  simpa only [mul_one] using
    mul_le_mul_right (FractionalIdeal.coeIdeal_le_one (I := m)) a

theorem traceDualFractionalIdeal_le_conductorScaled
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    traceDualFractionalIdeal a ≤
      traceDualFractionalIdeal (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) := by
  exact (FractionalIdeal.dual_le_dual ℤ ℚ ha
    (conductorScaledIdeal_ne_zero m hm a ha)).mpr (conductorScaledIdeal_le m hm a ha)

theorem traceDualFractionalIdeal_conductorScaled_mul
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    traceDualFractionalIdeal (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) *
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
        traceDualFractionalIdeal a := by
  unfold traceDualFractionalIdeal
  rw [FractionalIdeal.dual_eq_mul_inv, FractionalIdeal.dual_eq_mul_inv ℤ ℚ a,
    mul_inv, mul_assoc, mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hm), mul_one]

theorem conductorIdealQuotient_finite
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    Finite (fractionalIdealQuotient a
      (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))) := by
  exact fractionalIdealQuotient_finite_of_ratio m hm a _ ha
    (conductorScaledIdeal_le m hm a ha) rfl

theorem conductorTraceQuotient_finite
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    Finite (fractionalIdealQuotient
      (traceDualFractionalIdeal (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)))
      (traceDualFractionalIdeal a)) := by
  exact fractionalIdealQuotient_finite_of_ratio m hm _ _
    (traceDualFractionalIdeal_ne_zero _ (conductorScaledIdeal_ne_zero m hm a ha))
    (traceDualFractionalIdeal_le_conductorScaled m hm a ha)
    (traceDualFractionalIdeal_conductorScaled_mul m hm a ha)

theorem conductorIdealQuotient_card
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    Nat.card (fractionalIdealQuotient a
      (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))) = Ideal.absNorm m := by
  exact fractionalIdealQuotient_card_of_ratio m hm a _ ha
    (conductorScaledIdeal_le m hm a ha) rfl

theorem conductorTraceQuotient_card
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (a : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (ha : a ≠ 0) :
    Nat.card (fractionalIdealQuotient
      (traceDualFractionalIdeal (a * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)))
      (traceDualFractionalIdeal a)) = Ideal.absNorm m := by
  exact fractionalIdealQuotient_card_of_ratio m hm _ _
    (traceDualFractionalIdeal_ne_zero _ (conductorScaledIdeal_ne_zero m hm a ha))
    (traceDualFractionalIdeal_le_conductorScaled m hm a ha)
    (traceDualFractionalIdeal_conductorScaled_mul m hm a ha)

theorem traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) =
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F := by
  unfold traceDualFractionalIdeal codifferentFractionalIdeal
  rw [FractionalIdeal.dual_eq_mul_inv, mul_comm]
  rfl

end DedekindZetaZeroFree.Hecke

end
