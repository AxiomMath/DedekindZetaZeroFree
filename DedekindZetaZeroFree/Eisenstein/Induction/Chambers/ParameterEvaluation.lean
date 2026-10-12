module

public import DedekindZetaZeroFree.Eisenstein.Induction.Chambers.LocalParameterValues

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem chamber_parameterValue (p : KPHilbert.Place F) (y : KPAdeles F)
    (a : Raw R) (z : ℂ) :
    parameterValue R N P C (chamberRaw F ζ hζ y * a) z p =
      parameterKernel R N P C (fullCompact R P C) p (a p) z (rootCoordinate R y p) := by
  apply LinearMap.ext
  intro f
  cases p with
  | inl w => exact chamber_parameterValue_complex R N P C w y a z f
  | inr q => exact chamber_parameterValue_finite R N P C q y a z f

theorem current_chamber_stage
    (s : RestrictedTensorSimple.Level (bad R P C)) (y : KPAdeles F) (a : Raw R)
    (hval : ∀ p, p ∉ s.val → localValue R N P C p ((chamberRaw F ζ hζ y * a) p)
      (plusReference R N P C p) = reference R P C p)
    (hlog : ∀ p, p ∉ s.val → localLog R P C (chamberRaw F ζ hζ y * a) p = 0)
    (z : ℂ) (v : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    (LiteralSource.coreFlatInsertion R P C
      (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (chamberRaw F ζ hζ y * a))) =
      parameterStageIntegrand R N P C (fullCompact R P C) s a 1 z v
        (fun j => rootCoordinate R y j.val) := by
  rw [← sourceFlat_value_eq, sourceFlat_parameter_raw R N P C s _ hval hlog]
  have hm : (fun j : s.val => parameterValue R N P C (chamberRaw F ζ hζ y * a) z j.val) =
      (fun j : s.val => parameterKernel R N P C (fullCompact R P C) j.val
        (a j.val) z (rootCoordinate R y j.val)) := by
    funext j
    exact chamber_parameterValue R N P C j.val y a z
  rw [hm]
  rfl

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
