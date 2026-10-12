module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalFactorCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.Regularity.FiniteQuotient

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
set_option backward.isDefEq.respectTransparency false

theorem actualCoreResidue_regular (N : MomentSources.TraceHaarTransport R)
    (x : RestrictedTensorSimple.Core
      (MomentSources.actualLocal R (actualImageData R P C μ hμ))
      (actualReference R P C μ hμ) (bad R.A P C)) :
    actualCoreResidue R P C μ hμ N x ∈ MomentSources.regularResidualFunctions R := by
  exact finiteCoreResidue_regular R P C μ hμ N
    ((actualCoreEquiv R P C μ hμ).symm x)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
