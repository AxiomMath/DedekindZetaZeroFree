module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalResidues.QuotientModule

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

def oneEquiv : R ≃ₗ[R] ((1 : FractionalIdeal R⁰ K) : Submodule R K) :=
  LinearEquiv.ofBijective
    ((Algebra.linearMap R K).codRestrict _ (fun r =>
      (FractionalIdeal.mem_one_iff R⁰).mpr ⟨r, rfl⟩)) (by
      constructor
      · intro x y h
        exact IsFractionRing.injective R K (congrArg Subtype.val h)
      · intro x
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff R⁰).mp x.property
        exact ⟨r, Subtype.ext hr⟩)

theorem oneEquiv_map (m : Ideal R) :
    Submodule.map (oneEquiv (R := R) (K := K)).toLinearMap (m : Submodule R R) =
      fractionalResidueDenominator m (1 : FractionalIdeal R⁰ K) := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change algebraMap R K r ∈ (((m : FractionalIdeal R⁰ K) * 1) : FractionalIdeal R⁰ K)
    simpa using (FractionalIdeal.mem_coeIdeal_of_mem R⁰ hr : algebraMap R K r ∈ (m : FractionalIdeal R⁰ K))
  · intro hx
    change (x : K) ∈ (((m : FractionalIdeal R⁰ K) * 1) : FractionalIdeal R⁰ K) at hx
    rw [mul_one] at hx
    obtain ⟨r, hr, he⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hx
    exact ⟨r, hr, Subtype.ext he⟩

def rankEquivR (m : Ideal R) (I : FractionalIdeal R⁰ K)
    (hm : m ≠ ⊥) (hI : I ≠ 0) : (R ⧸ m) ≃ₗ[R] fractionalResidueModule m I := by
  let e := Submodule.Quotient.equiv m (fractionalResidueDenominator m (1 : FractionalIdeal R⁰ K))
    (oneEquiv (R := R) (K := K)) (oneEquiv_map m)
  let e' : fractionalResidueModule m (1 : FractionalIdeal R⁰ K) ≃ₗ[R]
      fractionalResidueModule m I := by
    unfold fractionalResidueModule fractionalResidueDenominator
    rw [mul_one]
    exact (FractionalIdeal.quotientEquiv 1 m I (m * I)
        (by simp [mul_comm]) FractionalIdeal.coeIdeal_le_one
        (fractionalResidue_mul_le m I)
        (mul_ne_zero (fun h => hm (FractionalIdeal.coeIdeal_eq_zero.mp h)) hI) one_ne_zero)
  exact e.trans e'

theorem residue_smul (m : Ideal R) (I : FractionalIdeal R⁰ K)
    (r : R) (x : fractionalResidueModule m I) :
    Ideal.Quotient.mk m r • x = r • x := by
  induction x using Submodule.Quotient.induction_on
  rename_i x
  rw [fractionalResidueModule_mk_smul_mk, Submodule.Quotient.mk_smul]

noncomputable def fractionalResidueEquiv (m : Ideal R) (I : FractionalIdeal R⁰ K)
    (hm : m ≠ ⊥) (hI : I ≠ 0) :
    (R ⧸ m) ≃ₗ[R ⧸ m] fractionalResidueModule m I := by
  let e := rankEquivR m I hm hI
  refine LinearEquiv.ofBijective
    { toFun := e
      map_add' := e.map_add
      map_smul' := ?_ } e.bijective
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e ((Ideal.Quotient.mk m) r • x) = (Ideal.Quotient.mk m) r • e x
  rw [residue_smul]
  rw [← e.map_smul]
  congr 1

end

end DedekindZetaZeroFree.Hecke
