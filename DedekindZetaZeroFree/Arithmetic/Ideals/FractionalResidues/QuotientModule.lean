module

public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

abbrev fractionalResidueDenominator (m : Ideal R) (I : FractionalIdeal R⁰ K) :
    Submodule R (I : Submodule R K) :=
  Submodule.comap (I : Submodule R K).subtype
    (((m : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K)

abbrev fractionalResidueModule (m : Ideal R) (I : FractionalIdeal R⁰ K) :=
  (I : Submodule R K) ⧸ fractionalResidueDenominator m I

theorem fractionalResidue_mul_le (m : Ideal R) (I : FractionalIdeal R⁰ K) :
    (((m : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K) ≤
      (I : Submodule R K) := by
  change (m : FractionalIdeal R⁰ K) * I ≤ I
  apply FractionalIdeal.mul_le.mpr
  intro a ha b hb
  obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
  change (algebraMap R K) r * b ∈ (I : Submodule R K)
  simpa only [Algebra.smul_def] using (I : Submodule R K).smul_mem r hb

theorem fractionalResidueModule_isTorsionBySet (m : Ideal R)
    (I : FractionalIdeal R⁰ K) :
    Module.IsTorsionBySet R (fractionalResidueModule m I) (m : Set R) := by
  apply (Module.isTorsionBySet_quotient_iff _ _).mpr
  intro x r hr
  change (r • (x : K)) ∈ (m : FractionalIdeal R⁰ K) * I
  simpa only [Algebra.smul_def] using
    FractionalIdeal.mul_mem_mul
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr, rfl⟩) x.property

noncomputable instance fractionalResidueModuleModule (m : Ideal R)
    (I : FractionalIdeal R⁰ K) : Module (R ⧸ m) (fractionalResidueModule m I) :=
  (fractionalResidueModule_isTorsionBySet m I).module

@[simp] theorem fractionalResidueModule_mk_smul_mk (m : Ideal R)
    (I : FractionalIdeal R⁰ K) (r : R) (x : (I : Submodule R K)) :
    Ideal.Quotient.mk m r •
        Submodule.Quotient.mk (p := fractionalResidueDenominator m I) x =
      Submodule.Quotient.mk (p := fractionalResidueDenominator m I) (r • x) := by
  rw [(fractionalResidueModule_isTorsionBySet m I).mk_smul]
  rfl

end

end DedekindZetaZeroFree.Hecke
