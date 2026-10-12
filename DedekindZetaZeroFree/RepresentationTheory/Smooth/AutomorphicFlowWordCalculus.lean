module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DerivativeWordContinuity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicAveraging
open KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

def pullback (f : X F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)

theorem pullback_rational (f : X F ζ hζ → ℂ)
    (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (g : Cover F ζ hζ) :
    pullback f (γ.val * g) = pullback f g := by
  apply congrArg f
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa using γ.property

theorem pullback_word (f : X F ζ hζ → ℂ) (word : List (B F)) :
    word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) (pullback f) =
      pullback (wordDerivative F ζ hζ word f) := by
  funext g
  induction word generalizing g with
  | nil => rfl
  | cons b word ih =>
    change deriv _ 0 = deriv _ 0
    congr 1
    funext t
    exact ih _

theorem word_flow_hasDerivAt (f : X F ζ hζ → ℂ)
    (hf : SmoothAutomorphic F ζ hζ f) (word : List (B F)) (b : B F)
    (g : Cover F ζ hζ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pullback (wordDerivative F ζ hζ word f)
      (g * archimedeanInsertion F ζ hζ (flow F b s)))
      (pullback (wordDerivative F ζ hζ (b :: word) f)
        (g * archimedeanInsertion F ζ hζ (flow F b t))) t := by
  let y := g * archimedeanInsertion F ζ hζ (flow F b t)
  have hd : HasDerivAt (fun s : ℝ => pullback (wordDerivative F ζ hζ word f)
      (y * archimedeanInsertion F ζ hζ (flow F b s)))
      (pullback (wordDerivative F ζ hζ (b :: word) f) y) (t - t) := by
    rw [sub_self]
    exact KPMsClearedTruncationL2.ActualWordLinearity.word_hasDerivAt_flow
      F ζ hζ f hf word b (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ y)
  have hd' := hd.comp_sub_const t t
  convert hd' using 1
  funext s
  dsimp [y]
  rw [mul_assoc, ← (archimedean_insertion_properties F ζ hζ).2.1,
    ← (flow_properties F b).2.1, add_sub_cancel]

end DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicAveraging

end
