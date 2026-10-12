module

public import DedekindZetaZeroFree.Eisenstein.Residues.Pairings.SelfPairingVanishing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev leftPairingWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem finite_word_pairing
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (f : ι → smoothAllWordL2 R) (g : smoothAllWordL2 R)
    (w : ι → List (KPSmoothActualFlowData.B F)) :
    (∫ x, star (∑ i ∈ s, a i * leftPairingWordDerivative (w i) (f i).val x) * g.val x ∂ R.quotientHaar) =
      ∑ i ∈ s, star (a i) * (-1 : ℂ)^(w i).length *
        ∫ x, star ((f i).val x) * leftPairingWordDerivative (w i).reverse g.val x ∂ R.quotientHaar := by
  rw [integral_pairing_finite_left R.quotientHaar s a _ g.val
    (fun i hi => ((f i).property (w i)).2) (g.property []).2]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := smooth_ordered_word_adjoint R (f i) g (w i) []
  simp only [List.append_nil, leftPairingWordDerivative, KPSmoothActualFlowData.wordDerivative] at hh
  rw [hh]
  ring

theorem finite_word_sum_zero_of_adjoint_pairings
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (f : ι → smoothAllWordL2 R) (g : smoothAllWordL2 R)
    (w : ι → List (KPSmoothActualFlowData.B F))
    (hrep : ∀ x, g.val x = ∑ i ∈ s, a i * leftPairingWordDerivative (w i) (f i).val x)
    (horth : ∀ i ∈ s,
      (∫ x, star ((f i).val x) * leftPairingWordDerivative (w i).reverse g.val x ∂ R.quotientHaar) = 0) :
    g.val = 0 := by
  apply original_zero_of_pairing_self_zero R g
  have he := finite_word_pairing R s a f g w
  have hp : (∫ x, star (g.val x) * g.val x ∂ R.quotientHaar) =
      ∫ x, star (∑ i ∈ s, a i * leftPairingWordDerivative (w i) (f i).val x) * g.val x ∂ R.quotientHaar := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hrep x]
  apply hp.trans (he.trans ?_)
  apply Finset.sum_eq_zero
  intro i hi
  rw [horth i hi, mul_zero]

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
