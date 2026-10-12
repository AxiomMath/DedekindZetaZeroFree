module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Bruhat.TwoCellUnfolding
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.KernelTorus.AdelicPeriodIdentity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspidalOrthogonality.CommutatorFibers
public import DedekindZetaZeroFree.Eisenstein.Continuation.Resolvent.CutoffAndClearedGerms
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslations.MovingCompactJetBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open _root_.DedekindZetaZeroFree.KPContActualChamberCasimirJets.CuspAnalytic renaming scalar_cusp_frame → scalar_cusp_frame

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection

section Actual
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Hilbert" => KPContActualAllCuspSource.Sector F ζ hζ C R P H U

variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (f : ℂ → S)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

end Actual

open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open Filter
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open MeasureTheory Filter
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

section ActualSourceChamberPin
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (hι : Function.Injective ι)
variable (f : ℂ → S) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer KPContinuation.spectralDomain f χ)
variable (V : ℂ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
variable (hV : KPContActualCutoffPlusClearedGerm.Properties F ζ hζ C R P H U R.adelicHaar R.adelic_isHaar rfl
  ι KPContinuation.spectralDomain f χ realization buffer source V)

end ActualSourceChamberPin

section ActualKernelPeriodTransport

open NumberField
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (Z : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
local notation "lZ" => KPContActualCommonDiskRightHolomorphy.lift F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val
variable (a : Cusps F ζ hζ C R P H U) (t : ℝ) (b : KPCuspCharts.Shape F)
 theorem section_localGroup_frame (x : KPCuspCharts.Horizontal F) :
    lZ (localGroup F ζ hζ C R P H U a t x b 1) =
      KPContActualCutoffSmoothDescent.frameValue F ζ hζ C R P H U Z a ((x,b),t) := by
  let e := (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (atlasLevel F ζ hζ C R P H U) R P H Z.val)
  unfold KPContActualCommonDiskRightHolomorphy.lift
  rw [localGroup, KPContSectorScalarLineAlgebra.group_lift_formula,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  rw [scalar_cusp_frame F ζ hζ C R P H U a e _ 1]
  simp only [map_one, Units.val_one, one_mul]
  dsimp only [e]
  rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  rfl
 theorem section_arch_root_orbit (x : InfiniteAdeleRing F) :
    lZ (KPGlobalTorusFunctionData.N F ζ hζ (x,0) * localGroup F ζ hζ C R P H U a t 0 b 1) =
    lZ (localGroup F ζ hζ C R P H U a t
      (KPContinuation.ChamberOutgoingSource.mixedToHorizontal F (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) b 1) := by
  rw [root_arch_insertion, localGroup, localGroup, ← mul_assoc,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  unfold KPContActualCommonDiskRightHolomorphy.lift
  rw [KPContSectorScalarLineAlgebra.group_lift_formula, KPContSectorScalarLineAlgebra.group_lift_formula]
  rw [archBasepoint_mul, KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  apply congrArg _
  apply Prod.ext
  · funext i
    change KPArch.action (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ _)).out _ = _
    rw [projective_action_mk, upper_root_action]
    apply Prod.ext
    · change 0 + complexParameter F ζ hζ x (KPCusp.complexPlace F i) = _
      rw [zero_add]
      rfl
    · rfl
  · rfl
 theorem section_finite_root_orbit
    (z : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hz : (finiteRepresentative F ζ hζ C R P H U a 1)⁻¹ * finiteRoot F ζ hζ z *
      finiteRepresentative F ζ hζ C R P H U a 1 ∈ (atlasLevel F ζ hζ C R P H U).toOpenSubgroup)
    (x : KPGlobalTorusFunctionData.Adeles F) :
    lZ (KPGlobalTorusFunctionData.N F ζ hζ (x + finiteParameter F z) * localGroup F ζ hζ C R P H U a t 0 b 1) =
    lZ (KPGlobalTorusFunctionData.N F ζ hζ x * localGroup F ζ hζ C R P H U a t 0 b 1) := by
  let c := finiteRepresentative F ζ hζ C R P H U a 1
  let u := c⁻¹ * finiteRoot F ζ hζ z * c
  have hg : KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z) * localGroup F ζ hζ C R P H U a t 0 b 1 =
      localGroup F ζ hζ C R P H U a t 0 b 1 * u.val := by
    unfold localGroup
    change (finiteRoot F ζ hζ z).val * (_ * _) = _
    rw [← mul_assoc, (insertion_commutes_cover F ζ hζ _ (finiteRoot F ζ hζ z)).symm.eq, mul_assoc]
    have he : (finiteRoot F ζ hζ z).val * c.val = c.val * u.val := by
      change ((finiteRoot F ζ hζ z) * c).val = (c * u).val
      congr 1
      dsimp only [u]
      group
    change _ * ((finiteRoot F ζ hζ z).val * c.val) = _
    rw [he, mul_assoc]
  rw [KPGlobalTorusFunctionData.N_add, mul_assoc, hg, ← mul_assoc]
  exact ActualMovingCompactGeometry.section_lift_finite_level F ζ hζ _ R P H Z.val _ ⟨u,hz⟩

end ActualKernelPeriodTransport

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CommonSphericalDisk.PolarDetection

end
