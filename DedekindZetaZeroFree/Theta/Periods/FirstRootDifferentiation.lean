module

public import DedekindZetaZeroFree.Theta.Whittaker.RootDerivativePeriods

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_derivative_period (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B) :
    (∀ v g, Integrable (fun q => firstRootDerivatives R J.cutoffs (J.base.realization.theta v)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) J.base.sources.dq) ∧
    (∀ v y, fourier R J.base.sources.dq
      (firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) (diagonal R y) =
        firstRootMultiplier R J.cutoffs y *
          fourier R J.base.sources.dq (J.base.realization.theta v) (diagonal R y)) := by
  exact ⟨RootDerivatives.firstRootDerivatives_integrable R N A B J,
    RootDerivatives.firstRootDerivatives_period R N A B J⟩

end DedekindZetaZeroFree.ThetaExpansion

end
