module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.SmoothDescent
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothAutomorphicAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalAverage
open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
local notation "G" => ActualCover F ζ hζ
local instance : MeasurableSpace (K_U F ζ hζ U) := borel (K_U F ζ hζ U)
local instance : BorelSpace (K_U F ζ hζ U) := ⟨rfl⟩

theorem exists_smooth_average (ν : Measure (K_U F ζ hζ U))
    [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (f : G → ℂ) (hf : KPLiteralRaw.Smooth F ζ hζ f)
    (hr : ∀ γ : Gamma F ζ hζ, ∀ g, f (γ.val*g)=f g)
    (hc : ∀ ε g, f (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (chi F ζ hζ ε : ℂ) * f g) :
    ∃ Z : smoothSections F ζ hζ U R P H, ∀ g,
      ((S F ζ hζ U R P H).symm Z.val).val
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      ResidualRawAverage.average F ζ hζ (K_U F ζ hζ U) ν f g := by
  let a := ResidualRawAverage.average F ζ hζ (K_U F ζ hζ U) ν f
  have ha := ResidualRawAverage.average_smooth F ζ hζ (K_U F ζ hζ U)
    (K_U_compact F ζ hζ U) ν f hf
  have har (γ : Gamma F ζ hζ) (g : G) : a (γ.val*g)=a g := by
    apply integral_congr_ae
    filter_upwards with k
    simpa only [mul_assoc] using hr γ (g*k.val)
  have hak (k : K_U F ζ hζ U) (g : G) : a (g*k.val)=a g :=
    ResidualRawAverage.average_fixed F ζ hζ _ ν f g k
  have hac (ε) (g : G) : a (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (chi F ζ hζ ε : ℂ) * a g := by
    dsimp [a, ResidualRawAverage.average]
    simp_rw [mul_assoc, hc]
    exact integral_const_mul _ _
  let d := ResidualAverageDescent.smoothDescent F ζ hζ U a ha.2.1 har hak hac
  refine ⟨smoothS F ζ hζ U R P H d, ?_⟩
  intro g
  rw [smoothS_apply, LinearEquiv.symm_apply_apply]
  exact ResidualAverageDescent.descend_pin F ζ hζ U a har hak g
end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalAverage

end
