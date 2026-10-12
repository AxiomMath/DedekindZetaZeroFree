module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactTranslationBounds
public import DedekindZetaZeroFree.Theta.Whittaker.FourierVanishingAndRootInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open ThetaExpansion MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

local notation "dq" => KPWildKernelUpperBound.quotientHaar F
local notation "V" => RestrictedTensorSimple.Core (LiteralSource.Plus R.A P C)
  (LiteralSource.plusReference R.A P C) (LiteralSource.bad R.A P C)

theorem core_period_integrable (z : V) (g : MomentSources.Group R) :
    Integrable (fun q : KPAdditiveQuotient F => LiteralSource.coreResidue R P C z
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)*
      star (adelicTraceQuotientCharacter F q : ℂ)) dq :=
  (KPLiteralPeriod.haar_fourier_vanishing_forces_root_invariance F ζ hζ
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    dq inferInstance _ (LiteralSource.coreResidue_raw_automorphic R P C z)).2.2.1 g

def corePeriod (g : MomentSources.Group R) : V →ₗ[ℂ] ℂ where
  toFun z := MomentSources.fourier R dq (LiteralSource.coreResidue R P C z) g
  map_add' z y := by
    simp only [MomentSources.fourier,map_add,Pi.add_apply,add_mul]
    exact integral_add (core_period_integrable R P C z g) (core_period_integrable R P C y g)
  map_smul' c z := by
    simp only [MomentSources.fourier,map_smul,Pi.smul_apply,smul_eq_mul,mul_assoc]
    exact integral_const_mul c _

def restrictedSlotPeriod
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val) (g : MomentSources.Group R) :
    complexCore →ₗ[ℂ] ℂ :=
  (corePeriod R P C g).comp (restrictedSlotTensor R.A P C s x w hw)

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
