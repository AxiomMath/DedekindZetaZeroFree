module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryPairings.FiniteCenterPairing
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteRefinedBoundaryCenters
public import DedekindZetaZeroFree.Eisenstein.Residues.Source.UpperWordHaarAdjoint
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
local instance ResidualBoundaryWordAdjointMeasurable (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance ResidualBoundaryWordAdjointBorel (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

open ResidualWeakEnergy KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge

open _root_.DedekindZetaZeroFree.KPMsAngularSourceRecipe renaming finitePart_eq_finiteCover → finitePart_eq_finiteCover

theorem finiteBoundaryPair_word_adjoint (N : MomentSources.TraceHaarTransport R)

    (Vnew : Level F ζ hζ) (dk : Measure (KPMsGreenFlux.K F))
    [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (x : Core) (f : smoothAllWordL2 HR)
    (hfx : ∀g, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=coreResidue R P C x g)
    (w : List (Fin (groupDimension F))) :
    finiteBoundaryPair R HR HP Vnew dk t.val.val
      (actualRightWord F ζ hζ w.reverse (coreResidue R P C x)) =
    (-1 : ℂ)^w.length * finiteBoundaryPair R HR HP Vnew dk
      (actualRightWord F ζ hζ w t.val.val) (coreResidue R P C x) := by
  unfold finiteBoundaryPair
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  let c := KPBoundedCuspFrames.actualFiniteRepresentative
    (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1
  let cfin : KPGlobalTorusFunctionData.finitePart F ζ hζ := ⟨c.val, by
    rw [finitePart_eq_finiteCover F ζ hζ]; exact c.property⟩
  exact ResidualPrincipalSlices.compact_source_upper_word_adjoint_haar R N P C  dk
    t x cfin _ (nativeAtlas F ζ hζ HR HP (nativeRecipe F ζ hζ HR HP) Vnew) ω.1
    f.val (fun v => (f.property v).1) hfx w

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
