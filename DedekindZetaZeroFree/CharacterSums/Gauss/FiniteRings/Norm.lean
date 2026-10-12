module

public import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteRings.PrimitiveCharacterFourierTransform
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped BigOperators

variable {R : Type*} [CommRing R] [Fintype R] [hR : Nontrivial R]

include hR

theorem finiteRingGaussSum_norm_sq (e : AddChar R ℂ)
    (he : IsPrimitiveRingAddChar e) (χ : Rˣ →* ℂ)
    (hχ : IsPrimitiveRingUnitChar χ) :
    ‖finiteRingGaussSum e χ‖ ^ 2 = (Fintype.card R : ℝ) := by
  classical
  have hpos : 0 < ∑ x : R, ‖unitCharExtend χ x‖ ^ 2 := by
    apply Finset.sum_pos'
    · intro x hx
      positivity
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      have hone : unitCharExtend χ (1 : R) = 1 := by
        simpa using unitCharExtend_coe χ (1 : Rˣ)
      simp [hone]
  have hp := finiteRingFourier_parseval e he (unitCharExtend χ)
  have ht : (∑ k : R, ‖finiteRingFourier e (unitCharExtend χ) k‖ ^ 2) =
      (∑ k : R, ‖unitCharExtend χ k‖ ^ 2) * ‖finiteRingGaussSum e χ‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [primitiveUnitChar_fourier e he χ hχ k, norm_mul, Complex.norm_conj, mul_pow]
  rw [ht, mul_comm (Fintype.card R : ℝ)] at hp
  exact (mul_left_cancel₀ (ne_of_gt hpos) hp)

theorem finiteRingGaussSum_normalized_norm (e : AddChar R ℂ)
    (he : IsPrimitiveRingAddChar e) (χ : Rˣ →* ℂ)
    (hχ : IsPrimitiveRingUnitChar χ) :
    ‖finiteRingGaussSum e χ / (Real.sqrt (Fintype.card R : ℝ) : ℂ)‖ = 1 := by
  have hp : (0 : ℝ) < Fintype.card R := by
    exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt (Fintype.card R : ℝ) := Real.sqrt_pos.2 hp
  have hn : ‖finiteRingGaussSum e χ‖ = Real.sqrt (Fintype.card R : ℝ) := by
    have hsq := finiteRingGaussSum_norm_sq e he χ hχ
    have hsquare := Real.sq_sqrt (le_of_lt hp)
    nlinarith [norm_nonneg (finiteRingGaussSum e χ)]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, hn]
  exact div_self (ne_of_gt hs)

end

end DedekindZetaZeroFree.Hecke
