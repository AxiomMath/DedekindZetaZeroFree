module

public import DedekindZetaZeroFree.Eisenstein.Induction.ParameterBoxes.ReferenceAndLogarithmicTails

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

theorem sourceStage_le_fullLevel
    (s : RestrictedTensorSimple.Level (bad R P C))
    (Q : Finset (KPFinitePlace F)) (hQ : C.exceptional ⊆ Q) (hs : s.val.toRight ⊆ Q) :
    s ≤ fullLevel R P C Q hQ := by
  intro p hp
  cases p with
  | inl w => simp [fullLevel,LiteralSource.cofactorSourceLevel]
  | inr q =>
    simpa [fullLevel,LiteralSource.cofactorSourceLevel] using hs (Finset.mem_toRight.mpr hp)

theorem compact_box_stage
    (s : RestrictedTensorSimple.Level (bad R P C))
    (K : Set (FaithfulSource.RepairedInducing.Raw R)) (hK : IsCompact K) :
    ∃ E : Finset (KPFinitePlace F), ∃ hsE : s.val.toRight ⊆ E, ∃ hCE : C.exceptional ⊆ E,
      ∀ Q (hEQ : E ⊆ Q), ∀ a ∈ K, ∀ y ∈ TraceBox.adelicBox F Q, ∀ z : ℂ,
      ∀ v : RestrictedTensorSimple.Stage (Plus R N P C) s.val,
        (LiteralSource.coreFlatInsertion R P C
          (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))).val z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ (chamberRaw F ζ hζ y * a))) =
        parameterStageIntegrand R N P C (fullCompact R P C)
          (fullLevel R P C Q (hCE.trans hEQ)) a 1 z
          (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C)
            s (fullLevel R P C Q (hCE.trans hEQ))
            (sourceStage_le_fullLevel R P C s Q _ (hsE.trans hEQ)) v)
          (fun j => rootCoordinate R y j.val) := by
  obtain ⟨E,hsE,hCE,hKtail⟩ := compact_split_tail R P C K hK s.val.toRight
  refine ⟨E,hsE,hCE,?_⟩
  intro Q hEQ a ha y hy z v
  have hCQ : C.exceptional ⊆ Q := hCE.trans hEQ
  have hsQ : s.val.toRight ⊆ Q := hsE.trans hEQ
  let t := fullLevel R P C Q hCQ
  have hst : s ≤ t := sourceStage_le_fullLevel R P C s Q hCQ hsQ
  have hat : ∀ q, q ∉ Q → KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    intro q hq
    exact hKtail a ha q (fun h => hq (hEQ h))
  have h := current_chamber_stage R N P C t y a
    (box_right_reference_tail R N P C Q hCQ y hy a hat)
    (box_right_log_tail R P C Q hCQ y hy a hat) z
    (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C) (bad R P C) s t hst v)
  have he : RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C)
      (bad R P C) t (RestrictedTensorSimple.transition _ _ _ s t hst v) =
      RestrictedTensorSimple.stageInclusion _ _ _ s v := Module.DirectLimit.of_f
  rw [he] at h
  exact h

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
