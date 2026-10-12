module

public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceQuotientPairing

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

variable (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hJI : J ≤ I)

theorem traceQuotientPairing_left_radical
    (x : fractionalIdealQuotient I J) :
    (∀ y : fractionalIdealQuotient
        (traceDualFractionalIdeal J) (traceDualFractionalIdeal I),
      traceQuotientPairing I J hI hJ hJI x y = 1) ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := fractionalIdealQuotientMk_surjective I J x
    apply (fractionalIdealQuotientMk_eq_zero_iff I J a).mpr
    rw [← traceDualFractionalIdeal_traceDualFractionalIdeal J hJ]
    apply (mem_traceDualFractionalIdeal_iff_tracePhase_eq_one
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal_ne_zero J hJ) (a : F)).mpr
    intro b hb
    simpa only [traceQuotientPairing_mk, mul_comm] using
      hx (fractionalIdealQuotientMk
        (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) ⟨b, hb⟩)
  · rintro rfl y
    exact traceQuotientPairing_zero_left I J hI hJ hJI y

theorem traceQuotientPairing_right_radical
    (y : fractionalIdealQuotient
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    (∀ x : fractionalIdealQuotient I J,
      traceQuotientPairing I J hI hJ hJI x y = 1) ↔ y = 0 := by
  constructor
  · intro hy
    obtain ⟨b, rfl⟩ := fractionalIdealQuotientMk_surjective
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
    apply (fractionalIdealQuotientMk_eq_zero_iff
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) b).mpr
    apply (mem_traceDualFractionalIdeal_iff_tracePhase_eq_one I hI (b : F)).mpr
    intro a ha
    simpa only [traceQuotientPairing_mk] using
      hy (fractionalIdealQuotientMk I J ⟨a, ha⟩)
  · rintro rfl x
    exact traceQuotientPairing_zero_right I J hI hJ hJI x

theorem traceQuotientPairing_injective :
    Function.Injective (traceQuotientPairing I J hI hJ hJI) := by
  apply (traceQuotientPairing I J hI hJ hJI).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  apply (traceQuotientPairing_left_radical I J hI hJ hJI x).mp
  intro y
  have h : traceQuotientPairing I J hI hJ hJI x = 0 := hx
  simpa only [h, AddChar.zero_apply]

def traceQuotientPairingTranspose :
    fractionalIdealQuotient
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) →+
        AddChar (fractionalIdealQuotient I J) ℂ where
  toFun y :=
    { toFun := fun x => traceQuotientPairing I J hI hJ hJI x y
      map_zero_eq_one' := traceQuotientPairing_zero_left I J hI hJ hJI y
      map_add_eq_mul' := fun x x' => traceQuotientPairing_add_left I J hI hJ hJI x x' y }
  map_zero' := by
    ext x
    exact traceQuotientPairing_zero_right I J hI hJ hJI x
  map_add' := by
    intro y y'
    ext x
    exact traceQuotientPairing_add_right I J hI hJ hJI x y y'

@[simp] theorem traceQuotientPairingTranspose_apply
    (y : fractionalIdealQuotient
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I))
    (x : fractionalIdealQuotient I J) :
    traceQuotientPairingTranspose I J hI hJ hJI y x =
      traceQuotientPairing I J hI hJ hJI x y := by
  rfl

theorem traceQuotientPairingTranspose_injective :
    Function.Injective (traceQuotientPairingTranspose I J hI hJ hJI) := by
  apply (traceQuotientPairingTranspose I J hI hJ hJI).ker_eq_bot_iff.mp
  apply bot_unique
  intro y hy
  apply (traceQuotientPairing_right_radical I J hI hJ hJI y).mp
  intro x
  have h : traceQuotientPairingTranspose I J hI hJ hJI y = 0 := hy
  change traceQuotientPairingTranspose I J hI hJ hJI y x = 1
  simpa only [h, AddChar.zero_apply]

end DedekindZetaZeroFree.Hecke

end
