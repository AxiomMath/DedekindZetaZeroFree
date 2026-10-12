module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.NoncuspidalEigentests
public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.AveragedBoundaryInnerProduct
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.FullBoundaryPairing

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
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

theorem spherical_original_boundary_pairing (hU : cofinalLevel F ζ hζ U = U)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (Z : KPContActualAllCuspSource.SmoothSections F ζ hζ D HR HP H U)
    (z : KPContActualAllCuspSource.Sector F ζ hζ D HR HP H U)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V HR HP H Z.val z)
    (hb : SphericalBoundaryProperty R P C D HR HP H U v z)
    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (x : Core)
    (hx : ∀g u, u∈KPGlobalTorusFunctionData.globalLevel F ζ hζ U →
      coreResidue R P C x (g*u)=coreResidue R P C x g)
    (f : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ)
    (hf : MemLp f 2 HR.quotientHaar)
    (hfx : ∀g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) = coreResidue R P C x g) :
    (∫q, star (f q) * ResidualSphericalGeometry.originalScalar F ζ hζ V HR HP H Z q
      ∂ HR.quotientHaar) = ((fullMass M).toReal : ℂ) *
      (∫ω, boundaryFullAverage R P C (nativeDatum F ζ hζ) dk v.val x ω ∂fullNu M) := by
  have heq : f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ = coreResidue R P C x := funext hfx
  have hsm : KPLiteralRaw.Smooth F ζ hζ
      (f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := by
    rw [heq]
    exact (coreResidue_raw_automorphic R P C x).1
  have hc : ∀ ε g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε*g)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)*
        f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    intro ε g
    rw [hfx,hfx]
    exact (coreResidue_regular R P C x).2.2 ε g
  let eig := KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0
  have he (g) : KPMsGreenFlux.casimir F ζ hζ
      (f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) g =
      eig*f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
    rw [heq,hfx]
    exact coreResidue_native_eigen R P C x g
  obtain ⟨ν,hν,hleft,T,t,ht,hpin,hgraph⟩ :=
    ResidualAveragedEigentest.exists_averaged_graph_eigentest F ζ hζ D HR HP H U f hsm hc hf eig he
  let := hν
  let := hleft
  rw [ResidualHilbertCenters.original_pairing_eq_average_inner F ζ hζ V ν HR HP H
    Z T z t hz ht f hf hpin]
  apply spherical_boundary_full_pairing R P C D HR HP M U hU v z hb ν dk x hx T t
  · obtain ⟨htm,hte⟩ := ht
    rw [←hte]
    have hs : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ V HR HP H T.val).val =
        KPContActualCutoffSmoothDescent.scalar F ζ hζ D HR HP H U T := by
      rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    exact htm.coeFn_toLp.trans (Filter.Eventually.of_forall (congrFun hs))
  · have hdim := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1
    simpa only [eig,hdim,ResidualHilbertCenters.sourceLaplacian] using hgraph
  · funext g
    have hl : KPContActualCommonDiskRightHolomorphy.lift F ζ hζ V HR HP H T.val g =
        ResidualSphericalGeometry.originalScalar F ζ hζ V HR HP H T
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
      rw [KPContActualCommonDiskRightHolomorphy.lift,
        KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
      rfl
    exact hl.trans (by simpa only [heq] using hpin g)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
