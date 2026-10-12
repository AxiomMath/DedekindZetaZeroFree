module

public import DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.IntegralEulerEnlargement

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

theorem exterior_parameter_compact (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (z : ℂ)
    (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q)
    (k : (C.canonical q).iwasawa.compact.toOpenSubgroup) :
    (finiteParameterInput R N P C q (fullCompact R P C q) z
      (plusReference R N P C (.inr q))).val (g * k.val) =
    (finiteParameterInput R N P C q (fullCompact R P C q) z
      (plusReference R N P C (.inr q))).val g := by
  rw [exterior_parameter_input R N P C q hq, exterior_parameter_input R N P C q hq]
  exact congrArg (fun f : sectionSpace (C.canonical q).borel (C.polarization q) .plus z => f.val g)
    ((exteriorProfile_spherical R N P C q hq).2 z k)

theorem parameterKernel_exterior_compact (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inr q))
    (ha : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (z : ℂ) (x : RootPoint R (.inr q)) :
    parameterKernel R N P C (fullCompact R P C) (.inr q) a z x (plusReference R N P C (.inr q)) =
    parameterKernel R N P C (fullCompact R P C) (.inr q) 1 z x (plusReference R N P C (.inr q)) := by
  have h := exterior_parameter_compact R N P C q hq z
    ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x))
    ⟨_, ha⟩
  simpa only [parameterKernel, LinearMap.coe_mk, AddHom.coe_mk, map_one, mul_one] using h

theorem parameterOutput_exterior_compact (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (.inr q))
    (ha : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain) :
    parameterOutput R N P C (fullCompact R P C) (.inr q) a z (plusReference R N P C (.inr q)) =
    exteriorFactor R N z (.inr q) • reference R P C (.inr q) := by
  rw [← parameterOutput_exterior R N P C (.inr q) hq z hz]
  apply (inducingCoordinates R P C (.inr q)).injective
  funext j
  rw [← parameterKernel_integral R N P C (fullCompact R P C) (.inr q) a z hz,
    ← parameterKernel_integral R N P C (fullCompact R P C) (.inr q) 1 z hz]
  simp_rw [parameterKernel_exterior_compact R N P C q hq a ha]

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
