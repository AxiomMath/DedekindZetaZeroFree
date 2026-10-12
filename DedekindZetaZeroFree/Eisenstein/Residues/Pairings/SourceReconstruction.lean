module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.FiniteCenterPairing
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteRefinedBoundaryCenters
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.SourceDifferentialWordSum
public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.CoreCompactCovariance

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
local instance ResidualSourceReconstructionPairingMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualSourceReconstructionPairingBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

theorem finiteBoundaryPair_source_reconstruction
    (n : ℕ) (Us : Fin n → Level F ζ hζ) (m : Fin n → ℕ)
    (v : ∀i, Fin (m i) → KPContActualSphericalFlatStage.Stage F ζ hζ (Us i))
    (w : ∀i, Fin (m i) → List (Fin (groupDimension F)))
    (a : ∀i, Fin (m i) → ℂ)
    (Vnew : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk]
    (x : Core)
    (hs : ∀g, quotientCoreEvaluator R.A P C x g =
      ∑i, ∑j, a i j * actualRightWord F ζ hζ (w i j)
        (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val g) :
    finiteBoundaryPair R HR HP Vnew dk (quotientCoreEvaluator R.A P C x) (coreResidue R P C x) =
      ∑i, ∑j, a i j * finiteBoundaryPair R HR HP Vnew dk
        (actualRightWord F ζ hζ (w i j) (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val)
        (coreResidue R P C x) := by
  have hzero (i : Fin n) (j : Fin (m i)) :
      (KPContFlatSourceRecipe.flatR F ζ hζ 0 (v i j).val).val = (v i j).val.val.val := by
    funext g
    simp only [KPContFlatSourceRecipe.flatR_formula,zero_mul,Complex.exp_zero,one_mul]
  simp_rw [hzero] at hs ⊢
  have hfun : quotientCoreEvaluator R.A P C x =
      fun g => ∑ij : Σi, Fin (m i), a ij.1 ij.2 *
        actualRightWord F ζ hζ (w ij.1 ij.2) (v ij.1 ij.2).val.val.val g := by
    funext g
    simpa only [Fintype.sum_sigma] using hs g
  rw [hfun]
  have he := finiteBoundaryPair_source_words_sum R P C HR HP Vnew dk
    (fun ij : Σi, Fin (m i) => a ij.1 ij.2)
    (fun ij => (v ij.1 ij.2).val) (fun ij => w ij.1 ij.2) x
  simpa only [Fintype.sum_sigma] using he

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
