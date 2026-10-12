module

public import DedekindZetaZeroFree.Eisenstein.Induction.ParameterBoxIntegral

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem current_source_box_integral
    (s : RestrictedTensorSimple.Level (bad R P C))
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ E : Finset (KPFinitePlace F), ∃ hsE : s.val.toRight ⊆ E, ∃ hCE : C.exceptional ⊆ E,
      ∀ Q (hEQ : E ⊆ Q), ∀ a ∈ K, ∀ z ∈ KPContinuation.spectralDomain,
      ∀ v : RestrictedTensorSimple.Stage (Plus R N P C) s.val,
        Integrable (fun y : KPGlobalTorusFunctionData.Adeles F =>
          (LiteralSource.coreFlatInsertion R P C
            (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
            (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a))))
          ((KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) ∧
        (∫ y : KPGlobalTorusFunctionData.Adeles F,
          (LiteralSource.coreFlatInsertion R P C
            (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
            (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a)))
          ∂(KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)) =
          (parameterStage R N P C (fullCompact R P C)
            (fullLevel R P C Q (hCE.trans hEQ)) a z
            (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
              (bad R P C) s (fullLevel R P C Q (hCE.trans hEQ))
              (sourceStage_le_fullLevel R P C s Q _ (hsE.trans hEQ)) v)).val.val 1 := by
  obtain ⟨E,hsE,hCE,hbox⟩ := compact_box_stage R N P C s K hK
  let D := (finite_localDifferentSupport F).toFinset
  let T := E ∪ D
  have hET : E ⊆ T := Finset.subset_union_left
  refine ⟨T,hsE.trans hET,hCE.trans hET,?_⟩
  intro Q hTQ a ha z hz v
  have hEQ : E ⊆ Q := hET.trans hTQ
  have hCQ : C.exceptional ⊆ Q := hCE.trans hEQ
  have hD : localDifferentSupport F ⊆ (Q : Set _) := by
    intro q hq
    exact hTQ (Finset.mem_union_right E ((finite_localDifferentSupport F).mem_toFinset.mpr hq))
  let w := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s (fullLevel R P C Q hCQ)
      (sourceStage_le_fullLevel R P C s Q hCQ (hsE.trans hEQ)) v
  have hi := parameter_box_integrable_and_integral R N P C Q hCQ hD
    (fullCompact R P C) a 1 z hz w
  have hp := hbox Q hEQ a ha
  have he : (fun y : KPGlobalTorusFunctionData.Adeles F =>
      (LiteralSource.coreFlatInsertion R P C
        (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a)))) =ᵐ[
          (KPAdditiveHaar.adelicMeasure F).restrict (TraceBox.adelicBox F Q)]
      (fun y => parameterStageIntegrand R N P C (fullCompact R P C)
        (fullLevel R P C Q hCQ) a 1 z w (fun j => rootCoordinate R y j.val)) := by
    filter_upwards [ae_restrict_mem (FullSourceExhaustion.adelicBox_measurable F Q)] with y hy
    exact hp y hy z v
  exact ⟨hi.1.congr he.symm, (integral_congr_ae he).trans hi.2⟩

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
