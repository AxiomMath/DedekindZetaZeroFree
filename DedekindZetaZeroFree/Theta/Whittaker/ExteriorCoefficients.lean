module

public import DedekindZetaZeroFree.Theta.Periods.NonzeroTensorProductDetection
public import DedekindZetaZeroFree.Theta.Whittaker.TameNonnegativeShells
public import DedekindZetaZeroFree.Arithmetic.LocalFields.RationalCompletionDecomposition
public import DedekindZetaZeroFree.Theta.Digits.ChineseRemainderCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem exterior_whittaker_value_generator_pow (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N)
    (hW : ExteriorWhittakerEquivariance R C) (p : ThetaBranch.ExteriorPrime R.A) (e : ℤ) :
    exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ e) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) e := by
  by_cases he : e < 0
  · rw [exterior_whittaker_value_eq_zero_of_neg R C hW p e he]
    simp [sexticSphericalCoefficient, he]
  · have he0 : 0 ≤ e := le_of_not_gt he
    simpa only [Int.toNat_of_nonneg he0] using
      exterior_whittaker_value_generator_pow_nat R hR C hW p e.toNat

theorem exterior_whittaker_value_generator_pow_mul_unit (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (hW : ExteriorWhittakerEquivariance R C)
    (p : ThetaBranch.ExteriorPrime R.A) (e : ℤ)
    (u : (p.val.adicCompletion F)ˣ) (t : 𝓞 F)
    (ht : ‖(u : p.val.adicCompletion F) - algebraMap (𝓞 F) (p.val.adicCompletion F) t‖ < 1)
    (hu : valuation (p.val.adicCompletion F) (u : p.val.adicCompletion F) = 1) :
    exteriorWhittakerValue R C p (exteriorCompletionGenerator R p ^ e * u) =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p) e *
        ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal t) ^ (2 * e) := by
  rw [exterior_whittaker_value_unit_covariance R hR C p e u t ht hu,
    exterior_whittaker_value_generator_pow R hR C hW p e]

theorem exterior_rational_value_eq_spherical_factor (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (hW : ExteriorWhittakerEquivariance R C)
    (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    C.factorization.exteriorValue R p x =
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x := by
  obtain ⟨u, t, he, ht, hu, hr⟩ := exterior_rational_completion_decomposition R p x
  change exteriorWhittakerValue R C p (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) = _
  rw [he, exterior_whittaker_value_generator_pow_mul_unit R hR C hW p _ u t ht hu, hr]
  rfl

theorem exterior_coefficients
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R) (N : TraceHaarTransport R)
    (prior : Nonempty (JointHaarFactorizedSources R N)) : Nonempty (JointExteriorCoefficientSources R N) := by
  obtain ⟨C⟩ := prior
  have hW := exterior_whittaker_equivariance R C
  refine ⟨{ C with exterior := {
    rational_exact := exterior_rational_value_eq_spherical_factor R hR C hW
    crt_product := ?_
    local_exact := ?_ } }⟩
  · intro c n P hc hn
    dsimp only
    calc
      (∏ p ∈ P, C.factorization.exteriorValue R p
        (∏ q ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A q) ^
          (idealPrimeExponent q.val.asIdeal c.val.val + 3 * idealPrimeExponent q.val.asIdeal n.val))) =
        (∏ p ∈ P, ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p
          (∏ q ∈ P, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A q) ^
            (idealPrimeExponent q.val.asIdeal c.val.val + 3 * idealPrimeExponent q.val.asIdeal n.val))) :=
        Finset.prod_congr rfl (fun p _ => exterior_rational_value_eq_spherical_factor R hR C hW p _)
      _ = _ := exterior_spherical_factors_crt R c n P hc hn
  · intro p e u t ht hu
    exact exterior_whittaker_value_generator_pow_mul_unit R hR C hW p e u t ht hu

end DedekindZetaZeroFree.ThetaExpansion

end
