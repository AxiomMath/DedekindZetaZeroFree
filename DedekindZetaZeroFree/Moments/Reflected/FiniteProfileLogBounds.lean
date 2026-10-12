module

public import DedekindZetaZeroFree.Moments.Reflected.SeparatedProfileExpansion

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinSource

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

theorem finiteProfileFamily_of_uniform_log_bounds
    (A : SArithmeticData F) [Finite A.UnitQuotient] [Finite A.V]
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hsmooth : ∀ u v, ContDiff ℝ 2 (logProfile (H u v)))
    (hbound : ∀ B : ℝ, 0 < B → ∀ j : ℕ, j ≤ 2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ u v x, 0 < x →
        ‖iteratedDeriv j (logProfile (H u v)) (Real.log x)‖ ≤
          K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B))) :
    RMSeparatedExpansion.FiniteProfileFamily A H := by
  letI : Fintype A.UnitQuotient := Fintype.ofFinite _
  letI : Fintype A.V := Fintype.ofFinite _
  refine ⟨Finset.univ, fun i => H i.val.1 i.val.2, ?_, ?_, ?_⟩
  · intro u v
    exact ⟨⟨(u, v), Finset.mem_univ _⟩, rfl⟩
  · intro i
    exact hsmooth i.val.1 i.val.2
  · intro B hB
    obtain ⟨K0, hK0, hb0⟩ := hbound B hB 0 (by norm_num)
    obtain ⟨K1, hK1, hb1⟩ := hbound B hB 1 (by norm_num)
    obtain ⟨K2, hK2, hb2⟩ := hbound B hB 2 (by norm_num)
    refine ⟨max (max K0 K1) K2 + 1, by
      have h0 : (0 : ℝ) ≤ max (max K0 K1) K2 :=
        le_trans hK0 (le_trans (le_max_left K0 K1) (le_max_left _ K2))
      linarith, ?_⟩
    intro i j hj x hx
    have hmin : 0 ≤ min (Real.rpow x (1 / 8)) (Real.rpow x (-B)) :=
      le_min (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
    have hle : ∀ K : ℝ, K ≤ max (max K0 K1) K2 →
        ‖iteratedDeriv j (logProfile (H i.val.1 i.val.2)) (Real.log x)‖ ≤
          K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B)) →
        ‖iteratedDeriv j (logProfile (H i.val.1 i.val.2)) (Real.log x)‖ ≤
          (max (max K0 K1) K2 + 1) *
            min (Real.rpow x (1 / 8)) (Real.rpow x (-B)) := by
      intro K hK h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hmin)
    interval_cases j
    · exact hle K0 (le_trans (le_max_left K0 K1) (le_max_left _ K2)) (hb0 _ _ x hx)
    · exact hle K1 (le_trans (le_max_right K0 K1) (le_max_left _ K2)) (hb1 _ _ x hx)
    · exact hle K2 (le_max_right _ K2) (hb2 _ _ x hx)

end
end DedekindZetaZeroFree.PrincipalMellinSource
