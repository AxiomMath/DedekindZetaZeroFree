module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LocalFactorCovariance

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
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actualCoreResidue_quotient (N : MomentSources.TraceHaarTransport R)
    (x : RestrictedTensorSimple.Core (Plus R.A P C)
      (plusReference R.A P C) (bad R.A P C)) :
    actualCoreResidue R P C μ hμ N
      (actualCoreEquiv R P C μ hμ (finiteCoreQuotient R P C μ hμ x)) =
        coreResidue R P C x := by
  change finiteCoreResidue R P C μ hμ N
    ((actualCoreEquiv R P C μ hμ).symm
      (actualCoreEquiv R P C μ hμ (finiteCoreQuotient R P C μ hμ x))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact finiteCoreResidue_quotient R P C μ hμ N x

theorem actualCoreResidue_range_eq (N : MomentSources.TraceHaarTransport R) :
    (actualCoreResidue R P C μ hμ N).range = (coreResidue R P C).range := by
  ext f
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := finiteCoreQuotient_surjective R P C μ hμ
      ((actualCoreEquiv R P C μ hμ).symm y)
    refine ⟨x, ?_⟩
    rw [← actualCoreResidue_quotient R P C μ hμ N x, hx,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨actualCoreEquiv R P C μ hμ (finiteCoreQuotient R P C μ hμ x),
      actualCoreResidue_quotient R P C μ hμ N x⟩

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
