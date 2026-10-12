module

public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.HilbertRepresentation
public import DedekindZetaZeroFree.Adeles.Quotients.Residual.FixedVectorAveragePairing
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothAutomorphicAveraging
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.CompactUnipotentInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
local instance : MeasurableSpace (K_U F ζ hζ V) := borel (K_U F ζ hζ V)
local instance : BorelSpace (K_U F ζ hζ V) := ⟨rfl⟩

theorem original_pairing_zero_of_average_orthogonal
    (ν : Measure (K_U F ζ hζ V)) [IsProbabilityMeasure ν]
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (Z T : smoothSections F ζ hζ V R P H)
    (z t : KPContSectorClosedLpSubspace.H F ζ hζ R V)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z)
    (ht : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H T.val t)
    (f : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ) (hf : MemLp f 2 R.quotientHaar)
    (hpin : ∀g, originalScalar F ζ hζ V R P H T
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν
        (fun a => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) g)
    (hi : inner ℂ t z = 0) :
    (∫x,star (originalScalar F ζ hζ V R P H Z x)*f x ∂ R.quotientHaar)=0 := by
  have hp : originalScalar F ζ hζ V R P H T =
      ResidualQuotientAverage.average F ζ hζ (K_U F ζ hζ V) ν f := by
    funext x
    induction x using Quotient.inductionOn with
    | h g => exact hpin g
  have hav := ResidualQuotientAveragePairing.fixed_pairing_average F ζ hζ
    (K_U F ζ hζ V) (K_U_compact F ζ hζ V) ν R
    (originalScalar F ζ hζ V R P H Z) f
    (represented_original_memLp F ζ hζ V R P H Z z hz) hf
    (originalScalar_KU_fixed F ζ hζ V R P H Z)
  rw [← hav,← hp]
  exact original_pairing_zero_of_reverse_inner_zero F ζ hζ V R P H Z T z t hz ht hi

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
