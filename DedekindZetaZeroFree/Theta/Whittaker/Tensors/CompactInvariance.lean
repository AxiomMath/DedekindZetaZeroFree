module

public import DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.CompactParameterIntegrals

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators
open NumberField MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPRankOneShellContinuation KPRankOneShellRepair KPRankOneTameSphericalFactor
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem parameterStage_compact_euler_enlargement
    (s t : RestrictedTensorSimple.Level (bad R P C)) (hst : s ≤ t)
    (a : Raw R)
    (ha : ∀ q : KPFinitePlace F, Sum.inr q ∈ t.val → Sum.inr q ∉ s.val →
      KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) (a (.inr q)) ∈
        (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain)
    (y : RestrictedTensorSimple.Stage (Plus R N P C) s.val) :
    parameterStage R N P C (fullCompact R P C) t a z
      (RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
        (bad R P C) s t hst y) =
    (∏ p ∈ t.val \ s.val, exteriorFactor R N z p) •
      parameterStage R N P C (fullCompact R P C) s a z y := by
  let A := parameterOutput R N P C (fullCompact R P C)
  have hA (p : KPHilbert.Place F) (hpt : p ∈ t.val) (hps : p ∉ s.val) :
      A p (a p) z (plusReference R N P C p) =
        exteriorFactor R N z p • reference R P C p := by
    cases p with
    | inl w => exact False.elim (hps (s.property (arch_bad R P C w)))
    | inr q =>
      exact parameterOutput_exterior_compact R N P C q
        (fun h => hps (s.property h)) (a (.inr q)) (ha q hpt hps) z hz
  have hv := congrArg (comparisonSmooth R P C)
    (euler_core_insertion (Plus R N P C) (Fiber R P C)
      (plusReference R N P C) (reference R P C) (bad R P C) s t hst
      (fun p => A p (a p) z) (exteriorFactor R N z) hA y)
  simpa only [parameterStage, LinearMap.comp_apply, map_smul] using hv

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
