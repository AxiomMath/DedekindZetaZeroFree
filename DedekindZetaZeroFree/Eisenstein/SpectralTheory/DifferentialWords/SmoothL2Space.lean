module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ResidueCenter.AllDerivativeEigenrelations
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DerivativeWordAction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPSmoothActualFlowData
open KPMsClearedTruncationL2
open ActualWordLinearity
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualSmoothWordAction renaming word_append → word_append
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 theorem word_zero (w : List (B F)) :
    wordDerivative F ζ hζ w (0 : KPSmoothActualFlowData.X F ζ hζ → ℂ) = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    funext x
    simp only [wordDerivative, ih, flowDerivative, Pi.zero_apply, deriv_const]

def smoothAllWordL2 (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) :
    Submodule ℂ (KPSmoothActualFlowData.X F ζ hζ → ℂ) where
  carrier := {f | ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f) ∧
    MemLp (wordDerivative F ζ hζ w f) 2 R.quotientHaar}
  zero_mem' := by
    intro w
    rw [word_zero]
    exact ⟨⟨continuous_const, fun x => contDiff_const⟩, MemLp.zero⟩
  add_mem' := by
    intro f g hf hg w
    rw [word_add F ζ hζ f g (hf []).1 (hg []).1 w]
    exact ⟨⟨(hf w).1.1.add (hg w).1.1,
      fun x => ((hf w).1.2 x).add ((hg w).1.2 x)⟩, ((hf w).2).add (hg w).2⟩
  smul_mem' := by
    intro c f hf w
    rw [word_smul F ζ hζ c f (hf []).1 w]
    exact ⟨⟨continuous_const.smul (hf w).1.1,
      fun x => contDiff_const.smul ((hf w).1.2 x)⟩, ((hf w).2).const_smul c⟩

theorem word_mem_smoothAllWordL2
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    {U : Level F ζ hζ} (f : smoothSpace F ζ hζ U)
    (hf : ∀ w, MemLp (wordDerivative F ζ hζ w f.val) 2 R.quotientHaar)
    (w : List (B F)) : wordDerivative F ζ hζ w f.val ∈ smoothAllWordL2 R := by
  intro v
  rw [← word_append F ζ hζ v w f.val]
  exact ⟨(ActualSmoothWordAction.word_mem F ζ hζ U (v ++ w) f).1, hf (v ++ w)⟩

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
