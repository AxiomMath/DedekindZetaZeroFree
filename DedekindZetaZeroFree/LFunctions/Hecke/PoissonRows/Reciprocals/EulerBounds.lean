module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Reciprocals.LogarithmicDiskBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReciprocalPrimitiveAux

noncomputable section

open DedekindZetaZeroFree NumberField

theorem euler_inverse_bound (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Detector.PrimitiveFrequencyCharacter F) (g : ℂ → ℂ),
      Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F ω.character s) →
      ∀ s : ℂ, (31 / 10 : ℝ) ≤ s.re → g s ≠ 0 ∧ ‖(g s)⁻¹‖ ≤ C := by
  obtain ⟨E, hE, hf⟩ := ReciprocalLogDiskAux.euler_log_facts F

  have key : ∀ ℓ : ℂ, ‖ℓ‖ ≤ E → ‖(Complex.exp ℓ)⁻¹‖ ≤ Real.exp E := by
    intro ℓ hℓ
    rw [← Complex.exp_neg, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [Complex.neg_re]
    have h1 : |ℓ.re| ≤ ‖ℓ‖ := Complex.abs_re_le_norm ℓ
    have h2 : -ℓ.re ≤ |ℓ.re| := neg_le_abs _
    linarith
  refine ⟨Real.exp E, Real.exp_pos E, ?_⟩
  intro ω g _hg hgL s hs
  obtain ⟨-, hexp, hbd⟩ := hf ω
  have hs1 : (1 : ℝ) < s.re := by linarith
  have hbd' := hbd s (by linarith)
  rw [hgL s hs1, ← hexp s hs1]
  exact ⟨Complex.exp_ne_zero _, key _ hbd'⟩

end

end DedekindZetaZeroFree.Quantitative.ReciprocalPrimitiveAux
