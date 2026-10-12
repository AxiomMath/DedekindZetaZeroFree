module

public import DedekindZetaZeroFree.Eisenstein.Residues.Cuspidality.DifferentialWords
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.Orthogonality
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.EigenfunctionTests
public import DedekindZetaZeroFree.Metaplectic.Torus.ResidualRepresentations.GenuineCentralCharacter
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.Smoothness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.CasimirEigenvalue
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.PairingKernel
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.CuspidalOrthogonalCenters

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Classical NumberField Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy KPGlobalResidualConstruction
open KPMsClearedTruncationL2.NativeWordBridge
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable {n : ℕ} (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (m : Fin n → ℕ)
variable (w : ∀i,Fin (m i) → List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
variable (a : ∀i,Fin (m i) → ℂ)
variable (Z : ∀i,Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M R P H (U i))
 abbrev cuspKernelWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem finiteCenterSum_eq_zero_of_upper_zero
    (z : ∀i,Fin (m i) → KPContActualAllCuspSource.Sector F ζ hζ M R P H (U i))
    (hz : ∀i j,KPContActualSmoothLineGluing.Represents F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) R P H (Z i j).val (z i j))
    (horth : ∀i j,CuspEigentestOrthogonal F ζ hζ M R P H (U i) 0 (z i j))
    (he : ∀i j g,KPMsGreenFlux.casimir F ζ hζ
      (KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j)) g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
        KPContActualCutoffPlusClearedGerm.groupScalar F ζ hζ M R P H (U i) (Z i j) g)
    (hzero : ResidualCuspBoundary.UpperZero F ζ hζ
      (fun g => finiteCenterSum F ζ hζ M R P H U m w a Z
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))) :
    finiteCenterSum F ζ hζ M R P H U m w a Z = 0 := by
  let eig := KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0
  let total : smoothAllWordL2 R := ⟨finiteCenterSum F ζ hζ M R P H U m w a Z,
    finiteCenterSum_mem F ζ hζ M R P H U m w a Z z hz eig he⟩
  apply finiteCenterSum_eq_zero_of_pairings F ζ hζ M R P H U m w a Z z hz eig he
  intro i j
  let v := ((w i j).map (wordIndexEquiv F)).reverse
  let f := cuspKernelWordDerivative F ζ hζ v total.val
  have hf : KPLiteralRaw.Smooth F ζ hζ
      (f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    finiteCenterSum_word_raw_smooth F ζ hζ M R P H U m w a Z v
  have hc : ∀ ε g, f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) :=
    original_word_genuine_left F ζ hζ total.val (total.property []).1
      (finiteCenterSum_genuine F ζ hζ M R P H U m w a Z) v
  have h2 : MemLp f 2 R.quotientHaar := (total.property v).2
  have hct : ResidualCuspBoundary.UpperZero F ζ hζ
      (f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) := by
    intro g
    exact ResidualAllWordCusp.upper_word_zero
      (H.atlas (KPContActualAllCuspSource.level F ζ hζ M R P H (U i))) R total
      (KPWildKernelUpperBound.quotientHaar F) hzero v g
  have hfe : ∀g,KPMsGreenFlux.casimir F ζ hζ
      (f ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) g =
      eig * f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) :=
    finiteCenterSum_word_eigen F ζ hζ M R P H U m w a Z eig he v
  obtain ⟨ν,hν,hleft,T,t,ht,hpin,hcus,hgraph⟩ :=
    ResidualAveragedEigentest.exists_averaged_eigentest F ζ hζ M R P H (U i)
      f hf hc h2 hct eig hfe
  letI := hν
  letI := hleft
  have hdim : KPCuspLogShape.dimension F = Module.finrank ℚ F / 2 :=
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1
  have hinner : inner ℂ t (z i j) = 0 := by
    apply horth i j T t ht hcus
    simpa only [eig,hdim] using hgraph
  exact original_pairing_zero_of_average_orthogonal F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ M R P H (U i)) ν R P H
    (Z i j) T (z i j) t (hz i j) ht f h2 hpin hinner

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
