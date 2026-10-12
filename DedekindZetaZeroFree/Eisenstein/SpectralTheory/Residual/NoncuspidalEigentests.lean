module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.Cuspidality
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Casimir.L2GraphDomain
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.Eigenfunctions
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactProbabilityExistence
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.GradientL2
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.LaplacianEigenCenters
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothSphericalAveraging
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SphericalEigenfunctionDerivativeEnergy
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.L2Norms

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAveragedEigentest
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
open ResidualSphericalGeometry ResidualHilbertCenters
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Q" => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
local instance : MeasurableSpace (K_U F ζ hζ V) := borel (K_U F ζ hζ V)
local instance : BorelSpace (K_U F ζ hζ V) := ⟨rfl⟩

theorem exists_averaged_graph_eigentest (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : KPLiteralRaw.Smooth F ζ hζ (f ∘ Q))
    (hc : ∀ ε g, f (Q (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε*g)) =
      (chi F ζ hζ ε : ℂ)*f (Q g))
    (h2 : MemLp f 2 R.quotientHaar)
    (a : ℂ)
    (he : ∀g, KPMsGreenFlux.casimir F ζ hζ (f ∘ Q) g = a*f (Q g)) :
    ∃ ν : Measure (K_U F ζ hζ V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧
      ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
        KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z ∧
        (∀g, originalScalar F ζ hζ V R P H Z (Q g) =
          ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (f ∘ Q) g) ∧
        (z,a • z) ∈ (sourceLaplacian F ζ hζ C R P H U).graph := by
  obtain ⟨ν,hν,hleft⟩ := ResidualCompactProbability.exists_probability F ζ hζ V
  let := hν
  let := hleft
  have hr (γ : Gamma F ζ hζ) (g) : (f ∘ Q) (γ.val*g) = (f ∘ Q) g :=
    KPMsGreenFlux.IntrinsicAveraging.pullback_rational f γ g
  obtain ⟨Z,hZ⟩ := ResidualSphericalAverage.exists_smooth_average F ζ hζ V ν R P H
    (f ∘ Q) hf hr hc
  have hp (g) : originalScalar F ζ hζ V R P H Z (Q g) =
      ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (f ∘ Q) g := hZ g
  have hcont : Continuous f := continuous_coinduced_dom.mpr hf.1
  have hscalar : originalScalar F ζ hζ V R P H Z =
      ResidualQuotientAverage.average F ζ hζ (K_U F ζ hζ V) ν f := by
    funext x
    induction x using Quotient.inductionOn with
    | h g => exact hp g
  have hZ2 : MemLp (originalScalar F ζ hζ V R P H Z) 2 R.quotientHaar := by
    rw [hscalar]
    exact ResidualQuotientAverage.average_memLp F ζ hζ (K_U F ζ hζ V)
      (K_U_compact F ζ hζ V) ν R f hcont h2
  have hlift : originalScalar F ζ hζ V R P H Z ∘ Q =
      ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (f ∘ Q) := funext hp
  have hZe (g) : KPMsGreenFlux.casimir F ζ hζ
      (originalScalar F ζ hζ V R P H Z ∘ Q) g = a*originalScalar F ζ hζ V R P H Z (Q g) := by
    rw [hlift,hp]
    exact ResidualAverageEigen.average_native_eigen F ζ hζ (K_U F ζ hζ V)
      (K_U_compact F ζ hζ V) ν (f ∘ Q) hf a he g
  have hall := spherical_native_eigen_all_derivatives F ζ hζ C R P H U Z hZ2 a hZe
  have hg := ResidualGradientL2.squareFinite_of_first_derivatives F ζ hζ V R P H Z
    (fun b => hall [b])
  have h3 := ResidualSphericalThreeL2.threeL2_of_native F ζ hζ V R P H Z a hZ2 hg hZe
  obtain ⟨z,hrep,hgraph⟩ := ResidualAverageDomain.graph_eigen_of_threeL2
    F ζ hζ V R P H canonicalRealization Z a h3
    (ResidualSectionMetric.section_eigen_of_native F ζ hζ V R P H Z a hZe)
  exact ⟨ν,hν,hleft,Z,z,hrep,hp,hgraph⟩
end DedekindZetaZeroFree.FourierContinuation.ResidualAveragedEigentest

end
