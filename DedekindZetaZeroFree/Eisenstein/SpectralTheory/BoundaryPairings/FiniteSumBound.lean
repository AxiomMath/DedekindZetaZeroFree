module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.DifferentialWordBoundaryPairing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
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
local instance ResidualFiniteBoundaryBoundMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualFiniteBoundaryBoundBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

theorem finiteBoundaryPair_bound (Vnew : Level F ζ hζ)
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk]
    (f g : KPLiteralRaw.G F ζ hζ → ℂ) (A B : ℝ) (hA : 0 ≤ A)
    (hf : ∀j k, ‖f (KPMsGreenFlux.compactInsertion F ζ hζ k *
      (KPBoundedCuspFrames.actualFiniteRepresentative
        (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) j).val)‖ ≤ A)
    (hg : ∀j k, ‖∫q : KPAdditiveQuotient F, g (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
      (KPMsGreenFlux.compactInsertion F ζ hζ k *
        (KPBoundedCuspFrames.actualFiniteRepresentative
          (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) j).val))
      ∂KPWildKernelUpperBound.quotientHaar F‖ ≤ B) :
    ‖finiteBoundaryPair R HR HP Vnew dk f g‖ ≤ A * B *
      (nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew).beta.real Set.univ := by
  letI := (nativeDisintegration F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew).finite_beta
  unfold finiteBoundaryPair
  apply norm_integral_le_of_norm_le_const
  filter_upwards with ω
  have hi := norm_integral_le_of_norm_le_const (μ:=dk)
    (Filter.Eventually.of_forall (fun k =>
      (by
        rw [norm_mul,norm_star]
        exact mul_le_mul (hf ω.1 k) (hg ω.1 k) (norm_nonneg _) hA :
        ‖f (KPMsGreenFlux.compactInsertion F ζ hζ k *
          (KPBoundedCuspFrames.actualFiniteRepresentative
            (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1).val) *
          star (∫q : KPAdditiveQuotient F, g (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
            (KPMsGreenFlux.compactInsertion F ζ hζ k *
              (KPBoundedCuspFrames.actualFiniteRepresentative
                (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1).val))
            ∂KPWildKernelUpperBound.quotientHaar F)‖ ≤ A*B)))
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using hi

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
