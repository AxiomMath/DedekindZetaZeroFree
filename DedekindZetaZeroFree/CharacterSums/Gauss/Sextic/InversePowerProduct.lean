module

public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.LocalTable

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.CanonicalGaussInversePower
open LocalFiniteSums CanonicalLocalGaussTable

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance exteriorPrimeResidueField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Ideal.Quotient.field _

local instance exteriorPrimeResidueFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  A.exteriorResidue_finite (primeIdeal p)

local instance exteriorPrimeResidueFintype (p : ExteriorPrime A) :
    Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Fintype.ofFinite _

private theorem Q_nonneg (p : ExteriorPrime A) : 0 ≤ Q p := by
  change 0 ≤ (Ideal.absNorm (primeIdeal p).val : ℝ)
  exact_mod_cast Nat.zero_le _

private theorem tau_eq_gaussSum (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) :
    tau C p a = gaussSum ((chi (σ := σ) p) ^ (SArithmeticData.sexticExponent a))
      (primeTrace C p) := by
  unfold tau
  rw [T_eq_finiteField, map_one]
  simp only [FiniteGaussTable.T, gaussSum, one_mul]

private theorem chi_inv_neg_one (p : ExteriorPrime A) :
    (chi (σ := σ) p)⁻¹ (-1) = 1 := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : A.R ⧸ A.extendIdeal (primeIdeal p)) = -1 := by
    rw [Ring.inverse_eq_inv, inv_neg_one]
  rw [this, chi_neg_one (σ := σ) p]

theorem tau_five_eq_star_tau_one (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    tau C p 5 = star (tau C p 1) := by
  have h1 : SArithmeticData.sexticExponent (1 : ℤ) = 1 := by decide
  have h5 : SArithmeticData.sexticExponent (5 : ℤ) = 5 := by decide
  have hχ6 : (chi (σ := σ) p) ^ 6 = 1 := by
    rw [← LocalFiniteSumCompatibility.chi_exact_order (σ := σ) p]
    exact pow_orderOf_eq_one _
  have hχ5 : (chi (σ := σ) p) ^ 5 = (chi (σ := σ) p)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ', show (5 : ℕ) + 1 = 6 by norm_num]
    exact hχ6
  have hinvneg : (chi (σ := σ) p)⁻¹ (-1) = 1 := chi_inv_neg_one (σ := σ) p
  have hneg : ∀ x : A.R ⧸ A.extendIdeal (primeIdeal p),
      (chi (σ := σ) p)⁻¹ (-x) = (chi (σ := σ) p)⁻¹ x := by
    intro x
    rw [show -x = (-1) * x by ring, map_mul, hinvneg, one_mul]
  rw [tau_eq_gaussSum C p 5, tau_eq_gaussSum C p 1, h5, h1, pow_one,
    star_gaussSum_eq, hχ5]
  rw [gaussSum, gaussSum]
  simp only [AddChar.inv_apply]
  rw [← Equiv.sum_comp (Equiv.neg (A.R ⧸ A.extendIdeal (primeIdeal p)))
    (fun x => (chi (σ := σ) p)⁻¹ x * (primeTrace C p) (-x))]
  simp only [Equiv.neg_apply, neg_neg, hneg]

theorem tau_one_mul_tau_five (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) :
    tau C p 1 * tau C p 5 = (Q p : ℂ) := by
  rw [tau_five_eq_star_tau_one C p]
  have h : tau C p 1 * star (tau C p 1) = (↑(Q p) : ℂ) := by
    rw [RCLike.star_def, Complex.mul_conj',
      norm_tau_of_not_six_dvd C p 1 (by norm_num), ← Complex.ofReal_pow,
      Real.sq_sqrt (Q_nonneg p)]
  exact h

end DedekindZetaZeroFree.CanonicalGaussInversePower

end
