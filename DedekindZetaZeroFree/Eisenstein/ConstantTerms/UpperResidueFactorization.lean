module

public import DedekindZetaZeroFree.Eisenstein.Continuation.DenominatorClearingValues
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.NormalizedScattering
public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.MeromorphicNumerators

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology TensorProduct
open NumberField MeasureTheory Filter
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
set_option maxHeartbeats 1500000

theorem current_upper_residue_factorization
    (s : RestrictedTensorSimple.Level (bad R P C))
    (K : Set (Raw R)) (hK : IsCompact K) :
    ∃ E : Finset (KPFinitePlace F), ∃ hsE : s.val.toRight ⊆ E, ∃ hCE : C.exceptional ⊆ E,
      ∀ a ∈ K, ∀ v : RestrictedTensorSimple.Stage (Plus R N P C) s.val,
        (∫ u : KPAdditiveQuotient F,
          LiteralSource.coreResidue R P C
            (coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v))
            (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out u) *
              scalarQuotient F ζ hζ (amalgamation F ζ hζ a))
          ∂KPWildKernelUpperBound.quotientHaar F) =
        KPGlobalFiniteSIntertwiner.residueNormalizer F  ζ hζ E *
          (parameterStage R N P C (fullCompact R P C) (fullLevel R P C E hCE) a 0
            (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
              (bad R P C) s (fullLevel R P C E hCE)
              (sourceStage_le_fullLevel R P C s E hCE hsE) v)).val.val 1 := by
  obtain ⟨E,hsE,hCE,hfactor⟩ := current_normalized_scattering R N P C  s K hK
  refine ⟨E,hsE,hCE,?_⟩
  intro a ha v
  let x := coreEquiv R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s v)
  let g := scalarQuotient F ζ hζ (amalgamation F ζ hζ a)
  let ve := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s (fullLevel R P C E hCE)
    (sourceStage_le_fullLevel R P C s E hCE hsE) v
  let b := fun z => (parameterStage R N P C (fullCompact R P C)
    (fullLevel R P C E hCE) a z ve).val.val 1
  have hb : AnalyticOnNhd ℂ b KPContinuation.spectralDomain :=
    parameterStage_analytic R N P C (fullCompact R P C) (fullLevel R P C E hCE) a 1 ve
  obtain ⟨M,B,r,hM,hMch,hr,hrb,hB,hclear,hcenter⟩ :=
    LiteralSource.core_scattering_continuation R P C x g
  have h0 : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
    norm_num [KPContinuation.spectralDomain]
  have hnear : B =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z * M z := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hz0
    exact hclear z hz hz0
  have hv := clearing_value_on_domain F ζ hζ  E hM.meromorphicOn
    (fun z hz => (hb z hz).meromorphicAt)
    KPContinuation.spectralDomain_isConnected
    KPContinuation.convergenceHalfPlane_subset_spectralDomain h0
    (hb 0 h0).continuousAt (hB 0 (Metric.mem_ball_self hr)).continuousAt
    (fun z hz => (hMch z hz).trans (hfactor a ha z hz v)) hnear
  exact hcenter.symm.trans hv

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
