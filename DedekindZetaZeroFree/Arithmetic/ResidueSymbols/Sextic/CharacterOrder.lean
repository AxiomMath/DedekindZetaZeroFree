module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.Residues.UnitReduction

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSumCompatibility
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

 instance primeMaximal (p : ExteriorPrime A) :
    (A.extendIdeal (primeIdeal p)).IsMaximal := by
  letI : (primeIdeal p).val.IsMaximal := p.val.isMaximal
  letI := Ideal.Quotient.field (primeIdeal p).val
  exact Ideal.Quotient.maximal_of_isField _
    ((ArithGaussCRT.exteriorQuotientEquiv A (primeIdeal p)).symm.toMulEquiv.isField
      (Field.toIsField _))
 instance primeField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _
 instance primeFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _

theorem intrinsic_chi_order (p : ExteriorPrime A) : orderOf (chi (σ := σ) p) = 6 := by
  have hchi (u : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ) :
      chi (σ := σ) p u = σ (A.sexticResidueFamily (primeIdeal p) u : F) := by
    simp [chi, SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent,
      MulChar.ofUnitHom_coe]
  have h6 : chi (σ := σ) p ^ 6 = 1 := by
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hchi, ← map_pow]
    have h := congrArg Units.val (A.sexticResidueFamily_normalized.1 (primeIdeal p) u)
    exact (congrArg σ h).trans (map_one σ)
  have hd : 6 ∣ Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) - 1 := by
    rw [A.exteriorResidue_card]
    have hm := A.exterior_norm_mod_twelve p.val (exterior_notMem p)
    change 6 ∣ Ideal.absNorm p.val.asIdeal - 1
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ)
  have hgc : orderOf g = Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) - 1 := by
    rw [hg, Nat.card_units]
  have hk : orderOf (g ^ ((Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) - 1) / 6)) = 6 := by
    rw [← hgc]
    apply orderOf_pow_orderOf_div
    · rw [hgc]
      have hn := Finite.one_lt_card (α := A.R ⧸ A.extendIdeal (primeIdeal p))
      omega
    · rwa [hgc]
  have hdiv : 6 ∣ orderOf (chi (σ := σ) p) := by
    obtain ⟨j, hj, he, hr⟩ := A.sexticResidueFamily_normalized.2.1
      (primeIdeal p) p.val rfl g
    have hv : (A.sexticResidueFamily (primeIdeal p) g : F) ^
        orderOf (chi (σ := σ) p) = 1 := by
      apply σ.injective
      rw [map_pow, map_one, ← hchi, ← MulChar.pow_apply_coe]
      rw [pow_orderOf_eq_one, MulChar.one_apply_coe]
    rw [he] at hv
    have hz : (A.primitive_zeta12.toInteger ^ (2 * j)) ^
        orderOf (chi (σ := σ) p) = (1 : 𝓞 F) := by
      apply RingOfIntegers.ext
      change (((A.primitive_zeta12.toInteger : 𝓞 F) : F) ^ (2 * j)) ^
        orderOf (chi (σ := σ) p) = 1
      exact (congrArg (fun z : F => (z ^ (2 * j)) ^ orderOf (chi (σ := σ) p))
        A.primitive_zeta12.coe_toInteger).trans hv
    have hrpow := congrArg (fun z : A.R ⧸ A.extendIdeal (primeIdeal p) =>
        z ^ orderOf (chi (σ := σ) p)) hr
    rw [← map_pow, ← map_pow, hz, map_one, map_one] at hrpow
    have hp : (g ^ ((Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) - 1) / 6)) ^
        orderOf (chi (σ := σ) p) = 1 := by
      apply Units.ext
      exact hrpow.symm
    rw [← hk]
    exact orderOf_dvd_of_pow_eq_one hp
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h6) hdiv
end DedekindZetaZeroFree.LocalFiniteSumCompatibility

end
