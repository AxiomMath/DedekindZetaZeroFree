module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.LocalCharacterCompatibility
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacters.GlobalCompatibility
public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticCharacterTable

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.CanonicalLocalGaussTable
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

instance primeResidueMaximal (p : ExteriorPrime A) :
    (A.extendIdeal (primeIdeal p)).IsMaximal := by
  letI : (primeIdeal p).val.IsMaximal := p.val.isPrime.isMaximal p.val.ne_bot
  letI := Ideal.Quotient.field (primeIdeal p).val
  exact Ideal.Quotient.maximal_of_isField _
    ((ArithGaussCRT.exteriorQuotientEquiv A (primeIdeal p)).symm.toMulEquiv.isField
      (Field.toIsField _))

local instance primeResidueField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _
local instance primeResidueFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _
local instance primeResidueFintype (p : ExteriorPrime A) :
    Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) := Fintype.ofFinite _

def depthOneEquiv (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) :
    Residue C p 1 ≃+* (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Ideal.quotEquivOfEq (by
    change Ideal.span {(generator C p ^ 1 : A.R)} = A.extendIdeal (primeIdeal p)
    simpa using (generator_generates C p).2)

def primeTrace (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) :
    AddChar (A.R ⧸ A.extendIdeal (primeIdeal p)) ℂ :=
  Circle.coeHom.compAddChar
    ((quotientTrace C p 1).compAddMonoidHom (depthOneEquiv C p).symm.toAddMonoidHom)

theorem primeTrace_ne_one (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) :
    primeTrace C p ≠ 1 := by
  have hx : (1 : Residue C p 1) ≠ 0 := by
    intro h
    have hh := congrArg (depthOneEquiv C p) h
    simpa using hh
  obtain ⟨y, hy⟩ := LocalFiniteSumCompatibility.quotientTrace_primitive C p 1 1 hx
  intro h
  apply hy
  have he := congrArg (fun f : AddChar (A.R ⧸ A.extendIdeal (primeIdeal p)) ℂ =>
    f (depthOneEquiv C p y)) h
  apply Circle.coe_injective
  change (quotientTrace C p 1 ((depthOneEquiv C p).symm (depthOneEquiv C p y)) : ℂ) = 1 at he
  simpa using he

theorem T_eq_finiteField (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (y : Residue C p 1) :
    T C p a y = FiniteGaussTable.T (chi (σ := σ) p) (primeTrace C p)
      (SArithmeticData.sexticExponent a) (depthOneEquiv C p y) := by
  have hr (x : Residue C p 1) : reduction C p 1 (by decide) x = depthOneEquiv C p x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  unfold T FiniteGaussTable.T
  apply Fintype.sum_equiv (depthOneEquiv C p).toEquiv
  intro x
  rw [LocalFiniteSumCompatibility.maskedPower_eq_reduction C p 1 (by decide), hr]
  congr 1
  change (quotientTrace C p 1 (y * x) : ℂ) =
    (quotientTrace C p 1 ((depthOneEquiv C p).symm
      (depthOneEquiv C p y * depthOneEquiv C p x)) : ℂ)
  rw [← map_mul, RingEquiv.symm_apply_apply]

private theorem exponent_dvd (a : ℤ) :
    (6 : ℕ) ∣ SArithmeticData.sexticExponent a ↔ (6 : ℤ) ∣ a := by
  have h₀ := Int.emod_nonneg a (by decide : (6 : ℤ) ≠ 0)
  have h₁ := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 6)
  have he : SArithmeticData.sexticExponent a < 6 := by
    unfold SArithmeticData.sexticExponent
    omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt he]
  unfold SArithmeticData.sexticExponent
  rw [Int.toNat_eq_zero]
  constructor
  · intro h
    exact Int.dvd_of_emod_eq_zero (by omega)
  · intro h
    rw [Int.emod_eq_zero_of_dvd h]

private theorem prime_card (p : ExteriorPrime A) :
    (Fintype.card (A.R ⧸ A.extendIdeal (primeIdeal p)) : ℝ) = Q p := by
  rw [← Nat.card_eq_fintype_card, A.exteriorResidue_card]
  rfl

theorem T_zero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (a : ℤ) :
    T C p a 0 = if (6 : ℤ) ∣ a then (Q p : ℂ) - 1 else 0 := by
  rw [T_eq_finiteField, map_zero, FiniteGaussTable.T_zero _ _
    (LocalFiniteSumCompatibility.chi_exact_order p) (primeTrace_ne_one C p)]
  have hc : (Fintype.card (A.R ⧸ A.extendIdeal (primeIdeal p)) : ℂ) = (Q p : ℂ) := by
    exact_mod_cast prime_card p
  simp only [exponent_dvd, hc]

theorem chi_unit_sixth (p : ExteriorPrime A)
    (x : A.R ⧸ A.extendIdeal (primeIdeal p)) (hx : IsUnit x) :
    chi (σ := σ) p x ^ 6 = 1 := by
  rw [← hx.unit_spec]
  unfold chi
  rw [SArithmeticData.sexticResiduePowerChar, show SArithmeticData.sexticExponent 1 = 1 by decide,
    pow_one, MulChar.ofUnitHom_coe]
  change σ ((A.sexticResidueFamily (primeIdeal p) hx.unit : Fˣ) : F) ^ 6 = 1
  rw [← map_pow]
  have h := congrArg (fun x : Fˣ => (x : F))
    (A.sexticResidueFamily_normalized.1 (primeIdeal p) hx.unit)
  simpa using congrArg σ h

theorem T_ne_zero (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (a : ℤ) (y : Residue C p 1) (hy : y ≠ 0) :
    T C p a y = (chi (σ := σ) p (depthOneEquiv C p y))⁻¹ ^ a * tau C p a := by
  have hy' : depthOneEquiv C p y ≠ 0 := by
    intro h
    apply hy
    exact (depthOneEquiv C p).injective (h.trans (map_zero _).symm)
  let u := Units.mk0 (depthOneEquiv C p y) hy'
  let v := (chi (σ := σ) p).toUnitHom u
  have hv : v ^ (6 : ℕ) = 1 := by
    apply Units.ext
    change (chi (σ := σ) p (depthOneEquiv C p y)) ^ 6 = 1
    exact
      chi_unit_sixth (σ := σ) p (depthOneEquiv C p y) (isUnit_iff_ne_zero.mpr hy')
  have hp : (chi (σ := σ) p (depthOneEquiv C p y))⁻¹ ^ SArithmeticData.sexticExponent a =
      (chi (σ := σ) p (depthOneEquiv C p y))⁻¹ ^ a := by
    have h := zpow_eq_zpow_emod' a (show (v⁻¹) ^ (6 : ℕ) = 1 by rw [inv_pow, hv, inv_one])
    have he : (SArithmeticData.sexticExponent a : ℤ) = a % 6 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    change v⁻¹ ^ a = v⁻¹ ^ (a % 6) at h
    rw [← he, zpow_natCast] at h
    have hh := congrArg (fun z : ℂˣ => (z : ℂ)) h
    simpa [v, u] using hh.symm
  rw [T_eq_finiteField, FiniteGaussTable.T_ne_zero _ _
    (LocalFiniteSumCompatibility.chi_exact_order p) (primeTrace_ne_one C p) _ _ hy',
    MulChar.star_apply', MulChar.inv_apply_eq_inv', hp]
  congr 1
  unfold tau FiniteGaussTable.tau
  rw [T_eq_finiteField, map_one]

theorem norm_tau_of_not_six_dvd (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (ha : ¬ (6 : ℤ) ∣ a) :
    ‖tau C p a‖ = Real.sqrt (Q p) := by
  unfold tau
  rw [T_eq_finiteField, map_one]
  change ‖FiniteGaussTable.tau (chi (σ := σ) p) (primeTrace C p)
    (SArithmeticData.sexticExponent a)‖ = Real.sqrt (Q p)
  rw [FiniteGaussTable.norm_tau_of_not_six_dvd _ _
    (LocalFiniteSumCompatibility.chi_exact_order p) (primeTrace_ne_one C p) _
    (fun h => ha ((exponent_dvd a).mp h)), prime_card]

theorem T_generator_power (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (n : ℕ) :
    T C p a (residueMap C p 1 (generator C p ^ n)) =
      if n = 0 then tau C p a
      else if (6 : ℤ) ∣ a then (Q p : ℂ) - 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [tau]
  · rw [if_neg hn]
    have hg : residueMap C p 1 (generator C p) = 0 := by
      change Ideal.Quotient.mk (Ideal.span {generator C p ^ 1}) (generator C p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa using Ideal.subset_span (Set.mem_singleton (generator C p))
    rw [map_pow, hg, zero_pow hn, T_zero]

theorem chi_neg_one (p : ExteriorPrime A) : chi (σ := σ) p (-1) = 1 := by
  have h := congrArg σ (A.sexticResidue_neg_one (primeIdeal p))
  unfold SArithmeticData.sexticResidue SArithmeticData.residueValue at h
  rw [map_neg (Ideal.Quotient.mk _), map_one (Ideal.Quotient.mk _)] at h
  unfold chi SArithmeticData.sexticResiduePowerChar
  rw [show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one]
  change (MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp
    (A.sexticResidueFamily (primeIdeal p)))) ((-1 : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ) : _) = 1
  rw [MulChar.ofUnitHom_coe]
  rw [show (-1 : A.R ⧸ A.extendIdeal (primeIdeal p)) =
    ((-1 : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ) : _) by simp, MulChar.ofUnitHom_coe] at h
  change σ ((A.sexticResidueFamily (primeIdeal p) (-1) : Fˣ) : F) = 1
  simpa only [map_one] using h

end DedekindZetaZeroFree.CanonicalLocalGaussTable

end
