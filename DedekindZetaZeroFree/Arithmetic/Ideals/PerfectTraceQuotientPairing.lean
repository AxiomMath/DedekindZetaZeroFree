module

public import DedekindZetaZeroFree.Arithmetic.Ideals.TracePairingRadicals
public import DedekindZetaZeroFree.Arithmetic.Ideals.ResidueModuleTracePairing

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [NumberField F]

@[reducible] def rayTraceQuotient (m : Ideal (NumberField.RingOfIntegers F)) :=
  fractionalIdealQuotient
    ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
      codifferentFractionalIdeal F)
    (codifferentFractionalIdeal F)

def quotientCongr
    (I I' J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (h : I = I') :
    fractionalIdealQuotient I J ≃ₗ[NumberField.RingOfIntegers F]
      fractionalIdealQuotient I' J := by
  subst I'
  exact LinearEquiv.refl _ _

private theorem quotientCongr_mk
    (I I' J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (h : I = I')
    (x : I.coeToSubmodule) :
    quotientCongr I I' J h (fractionalIdealQuotientMk I J x) =
      fractionalIdealQuotientMk I' J ⟨(x : F), h ▸ x.property⟩ := by
  subst I'
  rfl

def rayTraceQuotientEquiv
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    rayTraceQuotient m ≃ₗ[NumberField.RingOfIntegers F]
      fractionalIdealQuotient
        (traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
        (traceDualFractionalIdeal (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) := by
  exact quotientCongr _ _ _
    (traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent m hm).symm

@[simp] theorem rayTraceQuotientEquiv_mk
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (β : ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
      codifferentFractionalIdeal F).coeToSubmodule) :
    rayTraceQuotientEquiv m hm
      (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β) =
      fractionalIdealQuotientMk _ (traceDualFractionalIdeal 1)
        ⟨(β : F), by
          rw [traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent m hm]
          exact β.property⟩ := by
  exact quotientCongr_mk _ _ _
    (traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent m hm).symm β

@[instance_reducible] def rayTraceQuotientModule
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    Module (NumberField.RingOfIntegers F ⧸ m) (rayTraceQuotient m) := by
  apply fractionalIdealQuotientResidueModule m _ _
  · rw [← traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent m hm]
    simpa only [one_mul, codifferentFractionalIdeal] using
      traceDualFractionalIdeal_le_conductorScaled m hm 1 one_ne_zero
  · rw [← traceDualFractionalIdeal_coeIdeal_eq_inv_mul_codifferent m hm]
    simpa only [one_mul, codifferentFractionalIdeal] using
      traceDualFractionalIdeal_conductorScaled_mul m hm 1 one_ne_zero

def rayTraceQuotientPairing
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    (NumberField.RingOfIntegers F ⧸ m) → rayTraceQuotient m → ℂ :=
  fun k t => residueTraceQuotientPairing m hm k (rayTraceQuotientEquiv m hm t)

variable (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)

local notation "R" => NumberField.RingOfIntegers F ⧸ m
local notation "T" => rayTraceQuotient m
local notation "B" => rayTraceQuotientPairing m hm

@[simp] theorem rayTraceQuotientPairing_mk
    (α : NumberField.RingOfIntegers F)
    (β : ((m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)⁻¹ *
      codifferentFractionalIdeal F).coeToSubmodule) :
    B (Ideal.Quotient.mk m α)
      (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        (((Algebra.trace ℚ F ((α : F) * (β : F))) : ℝ) : ℂ)) := by
  simp only [rayTraceQuotientPairing, rayTraceQuotientEquiv_mk,
    residueTraceQuotientPairing, residueFractionalOneEquiv_apply_mk,
    traceQuotientPairing_mk, rationalTracePhase_apply_real]

@[simp] theorem rayTraceQuotientPairing_add_left (k k' : R) (t : T) :
    B (k + k') t = B k t * B k' t := by
  simp [rayTraceQuotientPairing, residueTraceQuotientPairing]

@[simp] theorem rayTraceQuotientPairing_add_right (k : R) (t t' : T) :
    B k (t + t') = B k t * B k t' := by
  simp [rayTraceQuotientPairing, residueTraceQuotientPairing]

@[simp] theorem rayTraceQuotientPairing_zero_left (t : T) : B 0 t = 1 := by
  simp [rayTraceQuotientPairing, residueTraceQuotientPairing]

@[simp] theorem rayTraceQuotientPairing_zero_right (k : R) : B k 0 = 1 := by
  simp [rayTraceQuotientPairing, residueTraceQuotientPairing]

theorem rayTraceQuotientPairing_balance :
    letI := rayTraceQuotientModule m hm
    ∀ (r k : R) (t : T), B (r * k) t = B k (r • t) := by
  intro r k t
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change residueTraceQuotientPairing m hm (r • k) (rayTraceQuotientEquiv m hm t) =
    residueTraceQuotientPairing m hm k (rayTraceQuotientEquiv m hm (r • t))
  rw [(rayTraceQuotientEquiv m hm).map_smul]
  exact residueTraceQuotientPairing_balance m hm (Ideal.Quotient.mk m r) k
    (rayTraceQuotientEquiv m hm t)

@[simp] theorem norm_rayTraceQuotientPairing (k : R) (t : T) : ‖B k t‖ = 1 := by
  exact norm_traceQuotientPairing _ _ _ _ _ _ _

theorem rayTraceQuotientPairing_left_radical (k : R) :
    (∀ t : T, B k t = 1) ↔ k = 0 := by
  constructor
  · intro h
    have h' : ∀ y, traceQuotientPairing 1 _ one_ne_zero
        ((residueFractionalIdeal_ne_zero_iff m).mpr hm)
        (residueFractionalIdeal_le_one m) (residueFractionalOneEquiv m k) y = 1 := by
      intro y
      obtain ⟨t, rfl⟩ := (rayTraceQuotientEquiv m hm).surjective y
      exact h t
    exact (residueFractionalOneEquiv m).injective
      ((traceQuotientPairing_left_radical _ _ _ _ _ _).mp h' |>.trans
        (residueFractionalOneEquiv m).map_zero.symm)
  · rintro rfl t
    exact rayTraceQuotientPairing_zero_left m hm t

def charCongr {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) : AddChar H ℂ ≃+ AddChar G ℂ where
  toFun χ := χ.compAddMonoidHom e.toAddMonoidHom
  invFun χ := χ.compAddMonoidHom e.symm.toAddMonoidHom
  left_inv χ := by ext x; simp
  right_inv χ := by ext x; simp
  map_add' χ ψ := by ext x; rfl

def oneTraceEquiv (hm : m ≠ ⊥) :
    fractionalIdealQuotient (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) ≃+
    AddChar (fractionalIdealQuotient (traceDualFractionalIdeal
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
      (traceDualFractionalIdeal 1)) ℂ := by
  exact AddEquiv.ofBijective
    (traceQuotientPairing 1 _ one_ne_zero
      ((residueFractionalIdeal_ne_zero_iff m).mpr hm) (residueFractionalIdeal_le_one m))
    (by
      letI : Finite (fractionalIdealQuotient
          (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) := by
        simpa only [one_mul] using conductorIdealQuotient_finite m hm 1 one_ne_zero
      letI : Finite (fractionalIdealQuotient (traceDualFractionalIdeal
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
          (traceDualFractionalIdeal 1)) := by
        simpa only [one_mul] using conductorTraceQuotient_finite m hm 1 one_ne_zero
      letI := Fintype.ofFinite (fractionalIdealQuotient
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
      letI := Fintype.ofFinite (fractionalIdealQuotient (traceDualFractionalIdeal
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) (traceDualFractionalIdeal 1))
      apply (Fintype.bijective_iff_injective_and_card _).mpr
      refine ⟨traceQuotientPairing_injective _ _ _ _ _, ?_⟩
      rw [AddChar.card_eq, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      have hA : Nat.card (fractionalIdealQuotient
          (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) = Ideal.absNorm m := by
        simpa only [one_mul] using conductorIdealQuotient_card m hm 1 one_ne_zero
      have hT : Nat.card (fractionalIdealQuotient (traceDualFractionalIdeal
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
          (traceDualFractionalIdeal 1)) = Ideal.absNorm m := by
        simpa only [one_mul] using conductorTraceQuotient_card m hm 1 one_ne_zero
      exact hA.trans hT.symm)

def oneTraceTransposeEquiv (hm : m ≠ ⊥) :
    fractionalIdealQuotient (traceDualFractionalIdeal
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
      (traceDualFractionalIdeal 1) ≃+
    AddChar (fractionalIdealQuotient (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) ℂ := by
  exact AddEquiv.ofBijective
    (traceQuotientPairingTranspose 1 _ one_ne_zero
      ((residueFractionalIdeal_ne_zero_iff m).mpr hm) (residueFractionalIdeal_le_one m))
    (by
      letI : Finite (fractionalIdealQuotient
          (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) := by
        simpa only [one_mul] using conductorIdealQuotient_finite m hm 1 one_ne_zero
      letI : Finite (fractionalIdealQuotient (traceDualFractionalIdeal
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
          (traceDualFractionalIdeal 1)) := by
        simpa only [one_mul] using conductorTraceQuotient_finite m hm 1 one_ne_zero
      letI := Fintype.ofFinite (fractionalIdealQuotient
        (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
      letI := Fintype.ofFinite (fractionalIdealQuotient (traceDualFractionalIdeal
        (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) (traceDualFractionalIdeal 1))
      apply (Fintype.bijective_iff_injective_and_card _).mpr
      refine ⟨traceQuotientPairingTranspose_injective _ _ _ _ _, ?_⟩
      rw [AddChar.card_eq, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      have hA : Nat.card (fractionalIdealQuotient
          (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) = Ideal.absNorm m := by
        simpa only [one_mul] using conductorIdealQuotient_card m hm 1 one_ne_zero
      have hT : Nat.card (fractionalIdealQuotient (traceDualFractionalIdeal
          (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
          (traceDualFractionalIdeal 1)) = Ideal.absNorm m := by
        simpa only [one_mul] using conductorTraceQuotient_card m hm 1 one_ne_zero
      exact hT.trans hA.symm)

private theorem oneTraceTransposeEquiv_apply
    (x : fractionalIdealQuotient (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
    (y : fractionalIdealQuotient (traceDualFractionalIdeal
      (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
      (traceDualFractionalIdeal 1)) :
    oneTraceTransposeEquiv m hm y x = traceQuotientPairing 1 _ one_ne_zero
      ((residueFractionalIdeal_ne_zero_iff m).mpr hm)
      (residueFractionalIdeal_le_one m) x y := by
  rfl

def rayTraceQuotientPairingTransposeEquiv (hm : m ≠ ⊥) : T ≃+ AddChar R ℂ :=
  (rayTraceQuotientEquiv m hm).toAddEquiv |>.trans
    ((oneTraceTransposeEquiv m hm).trans (charCongr (residueFractionalOneEquiv m).toAddEquiv))

@[simp] theorem rayTraceQuotientPairingTransposeEquiv_apply (t : T) (k : R) :
    rayTraceQuotientPairingTransposeEquiv m hm t k = B k t := by
  exact oneTraceTransposeEquiv_apply m hm _ _

end DedekindZetaZeroFree.Hecke

end
