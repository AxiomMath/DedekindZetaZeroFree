module

public import DedekindZetaZeroFree.Theta.Unfolding.UnitOrbitNormSummability
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.PrincipalExteriorCharacter

@[expose] public section

namespace DedekindZetaZeroFree.ProbeJointNormMassTransfer
noncomputable section
open scoped NumberField Classical
open NumberField

variable {F : Type} [Field F] [NumberField F]

theorem finiteCoefficient_gamma_invariant (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior)
    (h : A.R) (γ : ProbeOrbitNormSum.Gamma A) :
    comparisonPoissonFiniteCoefficient F A P.coefficients c n s
      ((A.unitEquiv γ.val : A.R) * h) =
      comparisonPoissonFiniteCoefficient F A P.coefficients c n s h := by
  have hchars (a : A.R) (ha : a ≠ 0) : P.coefficients.character a ^ 6 = 1 := by
    let I : A.Exterior := A.exteriorIdealEquiv.symm
      ⟨Ideal.span {a}, Ideal.span_singleton_eq_bot.not.mpr ha⟩
    have hI : A.Generates I a := by
      refine ⟨ha, ?_⟩
      rw [← A.exteriorIdealEquiv_apply]
      exact (congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply
        ⟨Ideal.span {a}, Ideal.span_singleton_eq_bot.not.mpr ha⟩)).symm
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe,
      P.character_eq_sexticResiduePowerChar A ι η hS I a hI]
    let e := Ideal.quotientEquivAlgOfEq A.R hI.2
    let u := Units.map e.toRingEquiv.toMonoidHom x
    change A.sexticResiduePowerChar ι I 1 (u : A.R ⧸ A.extendIdeal I) ^ 6 = 1
    rw [SArithmeticData.sexticResiduePowerChar,
      show SArithmeticData.sexticExponent 1 = 1 by decide, pow_one,
      MulChar.ofUnitHom_coe]
    change ι ((A.sexticResidueFamily I u : Fˣ) : F) ^ 6 = 1
    rw [← map_pow]
    have h6 := congrArg (fun z : Fˣ => (z : F))
      (A.sexticResidueFamily_normalized.1 I u)
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h6
    rw [h6, map_one]
  have he : FiniteTransform.IsTrivialOn A.R.toSubring P.coefficients.additiveCharacter := by
    intro x
    rw [P.sameTrace]
    exact P.traceCompatible x
  obtain ⟨ε, hε⟩ := γ.property
  have hε' : ε ^ 6 = γ.val := hε
  rw [← hε', map_pow]
  letI := P.coefficients.finiteResidue (P.coefficients.generator s)
    (P.coefficients.generates s).1
  letI := P.coefficients.finiteResidue
    (P.coefficients.generator c.val * P.coefficients.generator n ^ 3)
    (mul_ne_zero (P.coefficients.generates c.val).1
      (pow_ne_zero _ (P.coefficients.generates n).1))
  unfold comparisonPoissonFiniteCoefficient
  exact FiniteTransform.finiteCoefficient_sixth_unit_invariant A.R.toSubring
    (P.coefficients.generator s)
    (P.coefficients.generator c.val * P.coefficients.generator n ^ 3) h
    (P.coefficients.generates s).1
    (mul_ne_zero (P.coefficients.generates c.val).1
      (pow_ne_zero _ (P.coefficients.generates n).1))
    _ _ (hchars _ (P.coefficients.generates s).1)
    (hchars _ (mul_ne_zero (P.coefficients.generates c.val).1
      (pow_ne_zero _ (P.coefficients.generates n).1)))
    _ he (A.unitEquiv ε)

end
end DedekindZetaZeroFree.ProbeJointNormMassTransfer
