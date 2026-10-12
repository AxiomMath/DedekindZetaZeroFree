module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.AverageMass
public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.SphericalAverages
public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.BetaIntegral

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable {HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12}
variable {HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12}
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
variable (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] [dk.IsHaarMeasure]

theorem spherical_boundary_full_law (hU : cofinalLevel F ζ hζ U = U)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U) (x : Core)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C x (g*u)=coreResidue R P C x g) :
    ((fullMass M).toReal : ℂ) *
      (∫ω, boundaryFullAverage R P C (nativeDatum F ζ hζ) dk v.val x ω ∂fullNu M) =
    ∫ω,
      (KPContFlatSourceRecipe.flatR F ζ hζ 0 v.val).val
        (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ D HR HP
          (nativeFamily F ζ hζ HR HP) U ω.1 1).val *
      star (∫k, KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
        (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x)
        ((KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ D HR HP
          (nativeFamily F ζ hζ HR HP) U ω.1 1).val *
          KPMsGreenFlux.compactInsertion F ζ hζ k) ∂dk)
      ∂((nativeFamily F ζ hζ HR HP).disintegration
        (EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U)).beta := by
  have hf : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      v.val.val.val (g*u)=v.val.val.val g := fun g u hu => (v.property.1 g ⟨u,hu⟩).1
  rw [boundary_full_mass_eq_beta R P C M U dk v.val x hf hx]
  calc
    _ = ∫ω, boundaryAverage R P C dk v.val x
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U) ω.1).val
        ∂(nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).beta := by
      apply integral_congr_ae
      filter_upwards with ω
      apply integral_congr_ae
      filter_upwards with k
      have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
        F ζ hζ (fun w => (k w).val)
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U) ω.1)
      exact congrArg (boundaryProduct R P C v.val x) hc.eq
    _ = _ := by
      rw [ResidualNativeBetaBinding.native_beta_integral F ζ hζ D HR HP U hU]
      apply integral_congr_ae
      filter_upwards with ω
      exact boundaryAverage_spherical R P C U dk v x _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
