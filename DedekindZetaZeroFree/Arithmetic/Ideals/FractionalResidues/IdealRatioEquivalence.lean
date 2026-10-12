module

public import DedekindZetaZeroFree.Arithmetic.Ideals.UnitFractionalIdealResidueEquivalence

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

def idealRatioResidueEquiv
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    fractionalIdealQuotient I J ≃ₗ[NumberField.RingOfIntegers F]
      (NumberField.RingOfIntegers F ⧸ m) := by
  exact (FractionalIdeal.quotientEquiv I J 1
    (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (by simpa using hratio) hJI (residueFractionalIdeal_le_one m)
    ((residueFractionalIdeal_ne_zero_iff m).2 hm) hI).trans
    (residueFractionalOneEquiv m).symm

theorem fractionalIdealQuotient_finite_of_ratio
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    Finite (fractionalIdealQuotient I J) := by
  letI : Finite (NumberField.RingOfIntegers F ⧸ m) :=
    m.finiteQuotientOfFreeOfNeBot hm
  exact Finite.of_equiv (NumberField.RingOfIntegers F ⧸ m)
    (idealRatioResidueEquiv m hm I J hI hJI hratio).symm.toEquiv

theorem fractionalIdealQuotient_card_of_ratio
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    Nat.card (fractionalIdealQuotient I J) = Ideal.absNorm m := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (idealRatioResidueEquiv m hm I J hI hJI hratio).toEquiv

end DedekindZetaZeroFree.Hecke

end
