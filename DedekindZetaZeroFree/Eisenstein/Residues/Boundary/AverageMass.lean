module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.CompactRightNormalization
public import DedekindZetaZeroFree.Theta.Periods.Cusps.CrossTestFrameIdentity
public import DedekindZetaZeroFree.Theta.Periods.Cusps.CrossMassCancellation
public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.QuotientAverages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open CurrentBoundaryShapeTransport
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
local notation "Source" => KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)
variable {HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12}
variable {HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12}
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
variable (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] [dk.IsHaarMeasure]
theorem boundaryFullAverage_ae_cross (f : Source) (x : Core)
    (hf : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U → f.val.val (g*u)=f.val.val g)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U → coreResidue R P C x (g*u)=coreResidue R P C x g) :
    boundaryFullAverage R P C (nativeDatum F ζ hζ) dk f x =ᵐ[fullNu M]
      fun ω => ∫k, crossTest (R:=HR) (P:=HP) U (boundaryProduct R P C f x)
        (M.shape U (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ U) ω),k) ∂dk := by
  let : BorelSpace (FullOmega F ζ hζ (nativeDatum F ζ hζ)) := ⟨rfl⟩
  have ht : Continuous (fun ω : KPMsFixedHaarDisintegration.Omega
      (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U) =>
      ∫k, crossTest (R:=HR) (P:=HP) U (boundaryProduct R P C f x) (ω,k) ∂dk) := by
    apply continuous_sigma
    intro j
    dsimp only [crossTest]
    exact continuous_const
  have hm := ht.measurable.comp ((M.shape_measurable U).comp
    (KPMsActualAngularShellSource.fullToLevel_measurable _ _))
  obtain ⟨Y,hYpos,hY⟩ := exists_offset_admissible F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U
  apply ae_fullNu_of_shells M U Y hY _
    (measurableSet_eq_fun (boundaryFullAverage_continuous R P C _ dk f x).measurable hm)
  intro j
  filter_upwards [ae_restrict_mem (FullSupportGeometry.cuspShell_measurable
    (nativeRecipe F ζ hζ HR HP) U j Y hY)] with y hy
  change (∫k, boundaryProduct R P C f x
    (framedNormalization F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).cuspAtlas j.1).representative j.2))
      (actualFrame F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U j Y y) *
      KPMsGreenFlux.compactInsertion F ζ hζ k) ∂dk) = _
  trans (∫k, boundaryProduct R P C f x
    (framedNormalization F ζ hζ (nativeDatum F ζ hζ)
      (nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).radial
      (KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).cuspAtlas j.1).representative j.2))
      (actualFrame F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U j Y y *
        KPMsGreenFlux.compactInsertion F ζ hζ k)) ∂dk)
  · apply integral_congr_ae
    filter_upwards with k
    rw [CurrentNativeBoundaryFrame.normalization_right_compact]
  exact frame_eq_crossTest M U (boundaryProduct R P C f x)
    (boundaryProduct_arch_covariance R P C f x)
    (boundaryProduct_unipotent R P C f x)
    (boundaryProduct_central R P C f x)
    (boundaryProduct_right_level R P C U f x hf hx) dk j Y hY y hy

theorem boundary_full_mass_eq_beta (f : Source) (x : Core)
    (hf : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U → f.val.val (g*u)=f.val.val g)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U → coreResidue R P C x (g*u)=coreResidue R P C x g) :
    ((fullMass M).toReal : ℂ) *
      (∫ω,boundaryFullAverage R P C (nativeDatum F ζ hζ) dk f x ω ∂fullNu M) =
    ∫ω, ∫k, boundaryProduct R P C f x
      (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U) ω.1).val) ∂dk
      ∂(nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) U).beta := by
  rw [integral_congr_ae (boundaryFullAverage_ae_cross R P C M U dk f x hf hx)]
  exact full_mass_cross_cancel M U _ (boundaryProduct_continuous R P C f x) dk
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
