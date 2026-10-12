module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ConductorTraceQuotientCardinalities
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

theorem fractionalIdealQuotient_isTorsionBySet
    (m : Ideal (NumberField.RingOfIntegers F))
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    Module.IsTorsionBySet (NumberField.RingOfIntegers F)
      (fractionalIdealQuotient I J) (m : Set (NumberField.RingOfIntegers F)) := by
  apply (Module.isTorsionBySet_quotient_iff _ _).mpr
  intro x r hr
  change (r • (x : F)) ∈ J
  rw [← hratio]
  simpa only [Algebra.smul_def, mul_comm] using
    FractionalIdeal.mul_mem_mul x.property
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr, rfl⟩)

@[instance_reducible] def fractionalIdealQuotientResidueModule
    (m : Ideal (NumberField.RingOfIntegers F))
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    Module (NumberField.RingOfIntegers F ⧸ m) (fractionalIdealQuotient I J) :=
  (fractionalIdealQuotient_isTorsionBySet m I J hJI hratio).module

@[simp] theorem fractionalIdealQuotient_mk_smul
    (m : Ideal (NumberField.RingOfIntegers F))
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    letI := fractionalIdealQuotientResidueModule m I J hJI hratio
    ∀ (r : NumberField.RingOfIntegers F) (x : fractionalIdealQuotient I J),
      Ideal.Quotient.mk m r • x = r • x := by
  exact (fractionalIdealQuotient_isTorsionBySet m I J hJI hratio).mk_smul

def idealRatioResidueLinearEquiv
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J) :
    letI := fractionalIdealQuotientResidueModule m I J hJI hratio
    fractionalIdealQuotient I J ≃ₗ[NumberField.RingOfIntegers F ⧸ m]
      (NumberField.RingOfIntegers F ⧸ m) :=
  letI := fractionalIdealQuotientResidueModule m I J hJI hratio
  { (idealRatioResidueEquiv m hm I J hI hJI hratio).toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (idealRatioResidueEquiv m hm I J hI hJI hratio) (r • x) = r • (idealRatioResidueEquiv m hm I J hI hJI hratio) x
      exact (idealRatioResidueEquiv m hm I J hI hJI hratio).map_smul r x }

@[simp] theorem idealRatioResidueLinearEquiv_apply
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥)
    (I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (hI : I ≠ 0) (hJI : J ≤ I)
    (hratio : I * (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J)
    (x : fractionalIdealQuotient I J) :
    idealRatioResidueLinearEquiv m hm I J hI hJI hratio x =
      idealRatioResidueEquiv m hm I J hI hJI hratio x := rfl

@[instance_reducible] def residueTraceQuotientModule
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    Module (NumberField.RingOfIntegers F ⧸ m)
      (fractionalIdealQuotient
        (traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
        (traceDualFractionalIdeal (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))) :=
  fractionalIdealQuotientResidueModule m _ _
    (by simpa only [one_mul] using
      traceDualFractionalIdeal_le_conductorScaled m hm 1 one_ne_zero)
    (by simpa only [one_mul] using
      traceDualFractionalIdeal_conductorScaled_mul m hm 1 one_ne_zero)

def residueTraceQuotientPairing
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    (NumberField.RingOfIntegers F ⧸ m) →
      fractionalIdealQuotient
        (traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
        (traceDualFractionalIdeal (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) → ℂ :=
  fun k t => traceQuotientPairing 1 _ one_ne_zero
    ((residueFractionalIdeal_ne_zero_iff m).mpr hm)
    (residueFractionalIdeal_le_one m) (residueFractionalOneEquiv m k) t

theorem residueTraceQuotientPairing_balance
    (m : Ideal (NumberField.RingOfIntegers F)) (hm : m ≠ ⊥) :
    letI := residueTraceQuotientModule m hm
    ∀ (r k : NumberField.RingOfIntegers F ⧸ m)
      (t : fractionalIdealQuotient
        (traceDualFractionalIdeal (m : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))
        (traceDualFractionalIdeal (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F))),
      residueTraceQuotientPairing m hm (r * k) t =
        residueTraceQuotientPairing m hm k (r • t) := by
  intro r k t
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change traceQuotientPairing 1 _ one_ne_zero
      ((residueFractionalIdeal_ne_zero_iff m).mpr hm)
      (residueFractionalIdeal_le_one m) (residueFractionalOneEquiv m (r • k)) t =
    traceQuotientPairing 1 _ one_ne_zero
      ((residueFractionalIdeal_ne_zero_iff m).mpr hm)
      (residueFractionalIdeal_le_one m) (residueFractionalOneEquiv m k) (r • t)
  rw [(residueFractionalOneEquiv m).map_smul]
  exact traceQuotientPairing_balance _ _ _ _ _ r _ t

end DedekindZetaZeroFree.Hecke

end
