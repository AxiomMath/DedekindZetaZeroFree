module

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

def quotientChar {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (χ : AddChar M ℂ) (h : ∀ x ∈ p, χ x = 1) :
    AddChar (M ⧸ p) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift p.toAddSubgroup χ.toAddMonoidHom (by
      intro x hx
      change χ x = 1
      exact h x hx))

def representativeChar
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (x : F) :
    AddChar (traceDualFractionalIdeal J).coeToSubmodule ℂ where
  toFun y := rationalTracePhase (Algebra.trace ℚ F (x * (y : F)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro y z
    simp only [Submodule.coe_add, mul_add, map_add, AddChar.map_add_eq_mul]

def rightDescendedChar
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (x : I.coeToSubmodule) :
    AddChar (fractionalIdealQuotient
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) ℂ :=
  quotientChar
    ((traceDualFractionalIdeal I).coeToSubmodule.comap
      (traceDualFractionalIdeal J).coeToSubmodule.subtype)
    (representativeChar J (x : F)) (by
      intro y hy
      exact tracePhase_eq_one_of_mem_dual I hI x.property hy)

def representativePairing
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hI : I ≠ 0) :
    I.coeToSubmodule →+ AddChar (fractionalIdealQuotient
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) ℂ where
  toFun := rightDescendedChar I J hI
  map_zero' := by
    apply AddChar.ext
    intro y
    obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
    change rationalTracePhase (Algebra.trace ℚ F ((0 : F) * (y : F))) = 1
    simp
  map_add' := by
    intro x z
    apply AddChar.ext
    intro y
    obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective
      (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
    change rationalTracePhase (Algebra.trace ℚ F (((x : F) + (z : F)) * (y : F))) =
      rationalTracePhase (Algebra.trace ℚ F ((x : F) * (y : F))) *
      rationalTracePhase (Algebra.trace ℚ F ((z : F) * (y : F)))
    rw [add_mul, map_add, AddChar.map_add_eq_mul]

def traceQuotientPairing
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hJI : J ≤ I) :
    fractionalIdealQuotient I J →+
      AddChar (fractionalIdealQuotient
        (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) ℂ := by
  exact QuotientAddGroup.lift
    (J.coeToSubmodule.comap I.coeToSubmodule.subtype).toAddSubgroup
    (representativePairing I J hI) (by
      intro x hx
      apply AddChar.ext
      intro y
      obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective
        (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
      change rationalTracePhase (Algebra.trace ℚ F ((x : F) * (y : F))) = 1
      exact tracePhase_eq_one_of_mem_dual J hJ hx y.property)

variable (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hJI : J ≤ I)

@[simp] theorem traceQuotientPairing_mk
    (x : I.coeToSubmodule) (y : (traceDualFractionalIdeal J).coeToSubmodule) :
    traceQuotientPairing I J hI hJ hJI
      (fractionalIdealQuotientMk I J x)
      (fractionalIdealQuotientMk
        (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y) =
      rationalTracePhase (Algebra.trace ℚ F ((x : F) * (y : F))) := by
  rfl

theorem traceQuotientPairing_balance
    (r : NumberField.RingOfIntegers F) (x : fractionalIdealQuotient I J)
    (y : fractionalIdealQuotient (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    traceQuotientPairing I J hI hJ hJI (r • x) y =
      traceQuotientPairing I J hI hJ hJI x (r • y) := by
  obtain ⟨x, rfl⟩ := fractionalIdealQuotientMk_surjective I J x
  obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective
    (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
  rw [← fractionalIdealQuotientMk_smul, ← fractionalIdealQuotientMk_smul,
    traceQuotientPairing_mk, traceQuotientPairing_mk]
  congr 2
  change ((r : F) * (x : F)) * (y : F) = (x : F) * ((r : F) * (y : F))
  ring

@[simp] theorem traceQuotientPairing_add_left
    (x x' : fractionalIdealQuotient I J)
    (y : fractionalIdealQuotient (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    traceQuotientPairing I J hI hJ hJI (x + x') y =
      traceQuotientPairing I J hI hJ hJI x y *
        traceQuotientPairing I J hI hJ hJI x' y := by
  rw [map_add, AddChar.add_apply]

@[simp] theorem traceQuotientPairing_add_right
    (x : fractionalIdealQuotient I J)
    (y y' : fractionalIdealQuotient (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    traceQuotientPairing I J hI hJ hJI x (y + y') =
      traceQuotientPairing I J hI hJ hJI x y *
        traceQuotientPairing I J hI hJ hJI x y' := by
  exact AddChar.map_add_eq_mul _ _ _

@[simp] theorem traceQuotientPairing_zero_left
    (y : fractionalIdealQuotient (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    traceQuotientPairing I J hI hJ hJI 0 y = 1 := by
  rw [map_zero, AddChar.zero_apply]

@[simp] theorem traceQuotientPairing_zero_right (x : fractionalIdealQuotient I J) :
    traceQuotientPairing I J hI hJ hJI x 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp] theorem norm_traceQuotientPairing
    (x : fractionalIdealQuotient I J)
    (y : fractionalIdealQuotient (traceDualFractionalIdeal J) (traceDualFractionalIdeal I)) :
    ‖traceQuotientPairing I J hI hJ hJI x y‖ = 1 := by
  obtain ⟨x, rfl⟩ := fractionalIdealQuotientMk_surjective I J x
  obtain ⟨y, rfl⟩ := fractionalIdealQuotientMk_surjective
    (traceDualFractionalIdeal J) (traceDualFractionalIdeal I) y
  rw [traceQuotientPairing_mk, norm_rationalTracePhase]

end DedekindZetaZeroFree.Hecke

end
