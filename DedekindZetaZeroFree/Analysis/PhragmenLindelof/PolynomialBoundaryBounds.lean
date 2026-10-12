module

public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.QuadraticGrowthStripBounds

@[expose] public section

namespace DedekindZetaZeroFree

theorem norm_le_on_closed_strip_of_polynomial_boundary
    (δ : ℝ) (hδpos : 0 < δ) (hδle : δ ≤ 1 / 10)
    (k : ℕ) (H : ℝ) (hH : 0 ≤ H) (f : ℂ → ℂ)
    (hhol : DiffContOnCl ℂ f {s : ℂ | -δ < s.re ∧ s.re < 1 + δ})
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) →
      ‖f s‖ ≤ H * (2 + |s.im|) ^ k) :
    ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
      ‖f s‖ ≤ 6 ^ k * H * (2 + |s.im|) ^ k := by

  have hden : ∀ s : ℂ, -δ ≤ s.re → 1 ≤ ‖s + 2‖ := by
    intro s hs
    have h1 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have h2 : 1 ≤ (s + 2).re := by rw [h1]; linarith
    exact le_trans h2 (Complex.re_le_norm (s + 2))
  have hden_ne : ∀ s : ℂ, -δ ≤ s.re → (s + 2) ^ k ≠ 0 := by
    intro s hs
    refine pow_ne_zero k ?_
    exact norm_pos_iff.mp (lt_of_lt_of_le one_pos (hden s hs))
  have hcl : closure {s : ℂ | -δ < s.re ∧ s.re < 1 + δ} ⊆ {s : ℂ | -δ ≤ s.re} :=
    closure_minimal (fun s hs => le_of_lt hs.1) (isClosed_Ici.preimage Complex.continuous_re)
  set g : ℂ → ℂ := fun s => f s / (s + 2) ^ k with hgdef
  have hg_apply : ∀ s : ℂ, g s = f s / (s + 2) ^ k := fun s => by rw [hgdef]
  have hgdiff : DiffContOnCl ℂ g {s : ℂ | -δ < s.re ∧ s.re < 1 + δ} := by
    refine ⟨?_, ?_⟩
    · exact (hhol.1.div ((differentiableOn_id.add_const 2).pow k)
        (fun s hs => hden_ne s (le_of_lt hs.1)))
    · exact (hhol.2.div (((continuous_id.add continuous_const).pow k).continuousOn)
        (fun s hs => hden_ne s (hcl hs)))

  have hgrowth_g : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hgr⟩ := hgrowth
    refine ⟨M, B, hM, hB, ?_⟩
    intro s hs
    have hden1 : 1 ≤ ‖s + 2‖ := hden s (le_of_lt hs.1)
    have hdiv : ‖g s‖ ≤ ‖f s‖ := by
      rw [hg_apply, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ hden1)
    exact le_trans hdiv (hgr s hs)

  have hbound_g : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) → ‖g s‖ ≤ 3 ^ k * H := by
    intro s hs
    have hre : -δ ≤ s.re := by rcases hs with h | h <;> linarith
    have hden1 : 1 ≤ ‖s + 2‖ := hden s hre
    have him : |s.im| ≤ ‖s + 2‖ := by
      simpa using Complex.abs_im_le_norm (s + 2)
    have h3 : 2 + |s.im| ≤ 3 * ‖s + 2‖ := by
      have h2 : (2 : ℝ) ≤ 2 * ‖s + 2‖ := by linarith
      linarith [him, h2, norm_nonneg (s + 2)]
    have hfb := hboundary s hs
    have hpos : 0 < ‖s + 2‖ ^ k := pow_pos (lt_of_lt_of_le one_pos hden1) k
    rw [hg_apply, norm_div, norm_pow, div_le_iff₀ hpos]
    calc ‖f s‖ ≤ H * (2 + |s.im|) ^ k := hfb
      _ ≤ H * (3 * ‖s + 2‖) ^ k := by
          refine mul_le_mul_of_nonneg_left ?_ hH
          exact pow_le_pow_left₀ (by positivity) h3 k
      _ = 3 ^ k * H * ‖s + 2‖ ^ k := by rw [mul_pow]; ring
  have hab : -δ < 1 + δ := by linarith
  have hquad := norm_le_on_closed_strip_of_quadratic_exp_growth (-δ) (1 + δ) (3 ^ k * H)
    hab g hgdiff hgrowth_g
    (fun s hs => hbound_g s (Or.inl hs)) (fun s hs => hbound_g s (Or.inr hs))
  intro s hs
  have hgb : ‖g s‖ ≤ 3 ^ k * H := hquad s hs
  have hden1 : 1 ≤ ‖s + 2‖ := hden s hs.1
  have hnorm : ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := by
    have hne : (s + 2) ^ k ≠ 0 := hden_ne s hs.1
    have h2 : g s * (s + 2) ^ k = f s := by rw [hg_apply, div_mul_cancel₀ _ hne]
    calc ‖f s‖ = ‖g s * (s + 2) ^ k‖ := by rw [h2]
      _ = ‖g s‖ * ‖s + 2‖ ^ k := by rw [norm_mul, norm_pow]
  have h3 : ‖s + 2‖ ≤ 2 * (2 + |s.im|) := by
    have hnormle := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre2 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have him2 : (s + 2).im = s.im := by simp [Complex.add_im]
    have hrepos : 0 ≤ s.re + 2 := by linarith [hs.1, hδpos]
    rw [hre2, him2, abs_of_nonneg hrepos] at hnormle
    have hle : s.re + 2 ≤ 3.1 := by linarith [hs.2, hδle]
    linarith [hnormle, hle, abs_nonneg s.im]
  calc ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := hnorm
    _ ≤ (3 ^ k * H) * (2 * (2 + |s.im|)) ^ k := by
        refine mul_le_mul hgb ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) h3 k
    _ = 6 ^ k * H * (2 + |s.im|) ^ k := by
        have h36 : (3 : ℝ) ^ k * 2 ^ k = 6 ^ k := by rw [← mul_pow]; norm_num
        rw [mul_pow, ← h36]; ring

end DedekindZetaZeroFree
