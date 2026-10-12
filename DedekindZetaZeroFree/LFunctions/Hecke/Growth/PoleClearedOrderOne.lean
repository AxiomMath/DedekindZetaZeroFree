module

public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.FunctionalEquationRemainder
public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.PoleClearedLogarithmicBound
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeakPairPoleClearing

@[expose] public section

namespace DedekindZetaZeroFree.Hecke.WeakFEPair

theorem orderOneBound_poleClear (P : _root_.WeakFEPair ℂ) (hk : P.k = 1)
    (hdecay : ∃ A a p : ℝ, 0 ≤ A ∧ 0 < a ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t →
        (‖P.f t - P.f₀‖ ≤ A * Real.exp (-a * Real.rpow t p) ∧
         ‖P.g t - P.g₀‖ ≤ A * Real.exp (-a * Real.rpow t p)))
    (E : ℂ → ℂ)
    (hE : ∀ s : ℂ,
      E s = s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.ε * P.g₀) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      ‖E s‖ ≤ C * Real.exp (Real.rpow ‖s‖ (1 + ε)) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := DedekindZetaZeroFree.Hecke.rlogrBound_poleClear P.Λ₀ P.f₀ P.g₀ P.ε
    (rlogrBound_Λ₀ P hk hdecay)
  apply DedekindZetaZeroFree.Hecke.orderOneBound_of_rlogr E C K hC hK
  intro s
  rw [hE s]
  exact hbound s

end DedekindZetaZeroFree.Hecke.WeakFEPair
