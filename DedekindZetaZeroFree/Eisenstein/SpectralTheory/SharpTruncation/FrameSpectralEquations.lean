module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.FiniteLevelFlowJets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicFrameSpectral

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem smooth_intrinsic_scalar
    (f : Cover F ζ hζ → ℂ) (hs : Smooth F ζ hζ f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
      f (γ.val * g) = f g) :
    ∃ f₀ : X F ζ hζ → ℂ, KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f₀ ∧
      IntrinsicAveraging.pullback f₀ = f := by
  let f₀ : X F ζ hζ → ℂ := Quotient.lift f (by
    intro a b hab
    have hm := QuotientGroup.rightRel_apply.mp hab
    have he := hr ⟨b * a⁻¹, hm⟩ a
    simpa using he.symm)
  have hp : IntrinsicAveraging.pullback f₀ = f := rfl
  refine ⟨f₀, ⟨?_, ?_⟩, hp⟩
  · letI := QuotientGroup.rightRel (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact hs.1
  · intro x
    induction x using Quotient.inductionOn with
    | h g => exact hs.2 g

 theorem finitePart_eq_chart : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ := by
  unfold KPGlobalTorusFunctionData.finitePart KPSmoothLocalQuotientCharts.finiteSubgroup
  congr 1
  ext x
  simp [KPSmoothLocalQuotientCharts.finiteTuples, Subgroup.mem_iInf, MonoidHom.mem_ker]

end DedekindZetaZeroFree.KPMsGreenFlux.IntrinsicFrameSpectral

end
