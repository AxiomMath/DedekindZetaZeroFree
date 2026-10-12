module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteAverages.SliceLinearity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.DifferentialWordBoundaryPairing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
open KPContSectorCoveredQuotientVocabulary KPContFlatCuspIncomingEvaluation
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "Core" => RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
variable (D : KPGlobalTorusInducingPlan.ModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (HR : KPSmoothLocalQuotientCharts.HaarRecipe F R.A.zeta12 R.A.primitive_zeta12)
variable (HP : KPMsFixedHaarDisintegration.SphericalTransport F R.A.zeta12 R.A.primitive_zeta12)
variable (M : NativeMeasuredSource F R.A.zeta12 R.A.primitive_zeta12 HR HP)
variable (U : Level F R.A.zeta12 R.A.primitive_zeta12)
local notation "H" => nativeFamily F ζ hζ HR HP
local notation "V" => EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U
local instance ResidualFiniteBoundarySliceLinearityMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualFiniteBoundarySliceLinearityBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

theorem finiteBoundaryPair_source_sum_of_slices
    (Vnew : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk]
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (φ : ι → KPLiteralRaw.G F ζ hζ → ℂ)
    (hφ : ∀i j, Continuous (fun k : KPMsGreenFlux.K F =>
      φ i (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) j).val))) (x : Core) :
    finiteBoundaryPair R HR HP Vnew dk (fun g => ∑i, a i * φ i g) (coreResidue R P C x) =
      ∑i, a i * finiteBoundaryPair R HR HP Vnew dk (φ i) (coreResidue R P C x) := by
  let ct := KPGlobalResidualConstruction.upperConstantTerm F ζ hζ
    (KPWildKernelUpperBound.quotientHaar F) (coreResidue R P C x)
  have hct : Continuous ct := ResidualBoundaryInvariance.upper_continuous _
    (coreResidue_raw_automorphic R P C x).1.1 (coreResidue_rational_subgroup R P C x)
  have he := ResidualFiniteAnchor.anchorIntegral_sum_of_slices (R:=HR) (P:=HP) Vnew dk a
    (fun i g => φ i g * star (ct g)) (by
      intro i j
      have hk : Continuous (KPMsGreenFlux.compactInsertion F ζ hζ) :=
        (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
          (continuous_pi (fun a => continuous_subtype_val.comp (continuous_apply a)))
      let : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
        (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
      exact (hφ i j).mul (hct.comp (hk.mul continuous_const)).star)
  simpa only [finiteBoundaryPair, ResidualFiniteAnchor.anchorAverage, ct,
    KPGlobalResidualConstruction.upperConstantTerm, Finset.sum_mul, mul_assoc] using he

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
