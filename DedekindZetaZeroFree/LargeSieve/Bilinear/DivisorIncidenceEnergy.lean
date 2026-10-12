module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.GcdTailAndMaskedShellBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient
open scoped NumberField Classical

theorem divisor_incidence_sum
    (F : Type) [Field F] [NumberField F] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (N : ℝ), 1 ≤ N →
      ∀ (S : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ),
        (∑ d ∈ S, gcdTailEnergy F c N d lam) ≤
          C * Real.rpow N ε * energy F c N lam := by
  obtain ⟨A, hA1, hA⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F ε hε
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  refine ⟨A * Real.rpow 2 ε, mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro c N hN S lam
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hinc : ∀ b ∈ paperShell F c N,
      ((S.filter (fun d => d ∣ b)).card : ℝ) ≤ A * Real.rpow 2 ε * Real.rpow N ε := by
    intro b hb
    have hm := (mem_paperShell F c N b).mp hb
    have hb0 : b ≠ ⊥ := by simpa [Ideal.zero_eq_bot] using hm.1.ne_zero
    have hc : (S.filter (fun d => d ∣ b)).card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisors b).card := by
      apply Finset.card_le_card
      intro d hd
      exact (DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hb0).mpr (Finset.mem_filter.mp hd).2
    calc ((S.filter (fun d => d ∣ b)).card : ℝ)
        ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount b : ℝ) := by exact_mod_cast hc
      _ ≤ A * (Ideal.absNorm b : ℝ) ^ ε := hA b
      _ ≤ A * (2 * N) ^ ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hm.2.2.2 hε.le) hA0
      _ = A * Real.rpow 2 ε * Real.rpow N ε := by
        change A * Real.rpow (2 * N) ε = A * Real.rpow 2 ε * Real.rpow N ε
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow (by norm_num) hNpos.le]; ring
  unfold gcdTailEnergy
  rw [Finset.sum_comm]
  calc (∑ b ∈ paperShell F c N, ∑ d ∈ S, if d ∣ b then ‖lam b‖ ^ 2 else 0)
      = ∑ b ∈ paperShell F c N, ((S.filter (fun d => d ∣ b)).card : ℝ) * ‖lam b‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← Finset.sum_filter]
        simp
    _ ≤ ∑ b ∈ paperShell F c N,
        (A * Real.rpow 2 ε * Real.rpow N ε) * ‖lam b‖ ^ 2 :=
        Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_right (hinc b hb) (sq_nonneg _)
    _ = A * Real.rpow 2 ε * Real.rpow N ε * energy F c N lam := by
        rw [energy, Finset.mul_sum]

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient

end
