module

public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.TraceFourierNormalization

@[expose] public section

namespace DedekindZetaZeroFree.ComplexWeil

noncomputable section
open MeasureTheory

def FT (β : ℂ) (h : ℂ → ℂ) (y : ℂ) : ℂ :=
  (‖β‖ : ℂ) * ∫ z : ℂ, h z * psi β (-z * y) ∂(volume : Measure ℂ)

theorem FT_eq_F (β : ℂ) (h : ℂ → ℂ) (y : ℂ) :
    FT β h y = F β h y := by
  simp [FT, F, mu, integral_smul_measure, ENNReal.toReal_ofReal, norm_nonneg, smul_eq_mul]

end
end DedekindZetaZeroFree.ComplexWeil
