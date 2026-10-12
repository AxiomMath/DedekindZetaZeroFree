module

public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

@[expose] public section

namespace DedekindZetaZeroFree

theorem detector_sz_gamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  exact gamma_norm_le_real hz

theorem detector_sz_gamma_decay (a b : ℝ) (hab : a ≤ b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 1 ≤ |t| →
        ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.rpow |t| (-(m : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-(a + m))
  have hpos : 0 < a + (m + n : ℕ) := by
    push_cast
    linarith
  obtain ⟨M, hM, hbound⟩ := gamma_real_interval_bound
    (a := a + (m + n : ℕ)) (b := b + (m + n : ℕ)) hpos
  refine ⟨M, hM, ?_⟩
  intro σ hσ t ht
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have him : z.im = t := by simp [z]
  have hshift : ∀ j : ℕ, |t| ^ j * ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (j : ℂ))‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hne : z + (j : ℂ) ≠ 0 := by
        intro h
        have : t = 0 := by
          have he := congrArg Complex.im h
          simpa [him] using he
        grind
      have hnorm : |t| ≤ ‖z + (j : ℂ)‖ := by
        simpa [him] using Complex.abs_im_le_norm (z + (j : ℂ))
      calc
        |t| ^ (j + 1) * ‖Complex.Gamma z‖ = |t| * (|t| ^ j * ‖Complex.Gamma z‖) := by ring
        _ ≤ |t| * ‖Complex.Gamma (z + (j : ℂ))‖ := mul_le_mul_of_nonneg_left ih (abs_nonneg _)
        _ ≤ ‖z + (j : ℂ)‖ * ‖Complex.Gamma (z + (j : ℂ))‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = ‖Complex.Gamma (z + ((j + 1 : ℕ) : ℂ))‖ := by
          rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]
  have hshift2 := gamma_norm_le_add_nat (s := z + (m : ℂ)) (by simpa [him] using ht) n
  have hre : (z + ((m + n : ℕ) : ℂ)).re = σ + (m + n : ℕ) := by simp [z]
  have hreal : 0 < (z + ((m + n : ℕ) : ℂ)).re := by
    rw [hre]
    linarith [hσ.1]
  have hb : Real.Gamma (z + ((m + n : ℕ) : ℂ)).re ≤ M := by
    apply hbound
    rw [hre]
    constructor <;> linarith [hσ.1, hσ.2]
  have hfinal : |t| ^ m * ‖Complex.Gamma z‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (z + (m : ℂ))‖ := hshift m
      _ ≤ ‖Complex.Gamma ((z + (m : ℂ)) + (n : ℂ))‖ := hshift2
      _ = ‖Complex.Gamma (z + ((m + n : ℕ) : ℂ))‖ := by simp [Nat.cast_add, add_assoc]
      _ ≤ Real.Gamma (z + ((m + n : ℕ) : ℂ)).re := detector_sz_gamma_norm_le_real _ hreal
      _ ≤ M := hb
  have hp : 0 < |t| ^ m := pow_pos (lt_of_lt_of_le zero_lt_one ht) _
  have hdiv : ‖Complex.Gamma z‖ ≤ M / |t| ^ m := (le_div_iff₀ hp).2 (by nlinarith [hfinal])
  change ‖Complex.Gamma z‖ ≤ M * |t| ^ (-(m : ℝ))
  rw [Real.rpow_neg (abs_nonneg t), Real.rpow_natCast]
  simpa [div_eq_mul_inv] using hdiv

end DedekindZetaZeroFree
