module

public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.PoleClearedOrderOne

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

theorem strongPair_orderOneBound (P : _root_.WeakFEPair ℂ) (hk : P.k = 1)
    (hP : IsStrongFEPair P)
    (hdecay : ∃ A a p : ℝ, 0 ≤ A ∧ 0 < a ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t →
        (‖P.f t - P.f₀‖ ≤ A * Real.exp (-a * Real.rpow t p) ∧
         ‖P.g t - P.g₀‖ ≤ A * Real.exp (-a * Real.rpow t p))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      ‖P.Λ s‖ ≤ C * Real.exp (‖s‖ ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := WeakFEPair.orderOneBound_Λ₀ P hk hdecay ε hε
  refine ⟨C, fun s => ?_⟩
  have hΛ : P.Λ s = P.Λ₀ s := by
    simp [_root_.WeakFEPair.Λ, hP.hf₀, hP.hg₀]
  rw [hΛ]
  exact hC s

end DedekindZetaZeroFree.Hecke
