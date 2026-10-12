module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RegularizedGammaProduct

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem Gammaℂ_mul_originMellinQ_rapid_decay (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (u v : ℝ) (huv : u ≤ v) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ,
      u ≤ σ → σ ≤ v → 1 ≤ |t| →
        (1 + |t|) ^ k *
            ‖Complex.Gammaℂ ((σ : ℂ) + t * Complex.I) *
              originMellinQ h ((σ : ℂ) + t * Complex.I)‖ ≤ C := by

  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-u)
  set n : ℕ := max k n₀ with hn
  have hkn : k ≤ n := le_max_left k n₀
  have hn₀n : (n₀ : ℝ) ≤ (n : ℝ) := by
    rw [hn]; exact_mod_cast le_max_right k n₀
  have hnu : -((n : ℝ)) < u := by
    have : -u < (n : ℝ) := lt_of_lt_of_le hn₀ hn₀n
    linarith

  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    mellin_iteratedDeriv_positive_strip_bound hh hc n (u + (n : ℝ)) (v + (n : ℝ))
      (by linarith) (by linarith)
  refine ⟨2 ^ k * C₀ + 1, by positivity, ?_⟩
  intro σ t huσ hσv ht
  have ht1 : (1 : ℝ) ≤ |t| := ht
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht1
  have htne : t ≠ 0 := by
    intro h0; rw [h0, abs_zero] at ht1; linarith
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  have him : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  have hsre : -((n : ℝ)) < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [hre]; linarith
  have hsim : (((σ : ℂ) + (t : ℂ) * Complex.I)).im ≠ 0 := by
    rw [him]; exact htne

  have hnum :
      ‖mellin (iteratedDeriv n h) (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ))‖ ≤ C₀ := by
    have hre2 : (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ)).re = σ + n := by
      rw [Complex.add_re, hre, Complex.natCast_re]
    exact hC₀ _ (by rw [hre2]; linarith) (by rw [hre2]; linarith)

  have hden :
      |t| ^ n ≤ ‖∏ j ∈ Finset.range n,
        (((σ : ℂ) + (t : ℂ) * Complex.I) + (j : ℂ))‖ := by
    simpa only [Complex.ofReal_re, Complex.ofReal_im] using
      (rising_product_norm_lower_bound σ t n ht)

  have hnorm :
      ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I) *
          originMellinQ h ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₀ / |t| ^ n := by
    rw [Gammaℂ_mul_originMellinQ_eq_shift h hh hc n _ hsre hsim]
    rw [norm_div]
    have hone : ‖(-1 : ℂ) ^ n *
        mellin (iteratedDeriv n h) (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ))‖ =
        ‖mellin (iteratedDeriv n h) (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ))‖ := by
      simp
    rw [hone]
    have hPpos : 0 < ‖∏ j ∈ Finset.range n,
        (((σ : ℂ) + (t : ℂ) * Complex.I) + (j : ℂ))‖ :=
      lt_of_lt_of_le (pow_pos htpos n) hden
    calc ‖mellin (iteratedDeriv n h) (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ))‖ /
          ‖∏ j ∈ Finset.range n, (((σ : ℂ) + (t : ℂ) * Complex.I) + (j : ℂ))‖
        ≤ C₀ / ‖∏ j ∈ Finset.range n, (((σ : ℂ) + (t : ℂ) * Complex.I) + (j : ℂ))‖ :=
          div_le_div_of_nonneg_right hnum (le_of_lt hPpos)
      _ ≤ C₀ / |t| ^ n :=
          div_le_div_of_nonneg_left (le_of_lt hC₀pos) (pow_pos htpos n) hden

  have hpow : (1 + |t|) ^ k ≤ 2 ^ k * |t| ^ k := by
    calc (1 + |t|) ^ k ≤ (2 * |t|) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * |t| ^ k := by rw [mul_pow]
  have hmono : |t| ^ k ≤ |t| ^ n := pow_le_pow_right₀ ht1 hkn
  calc (1 + |t|) ^ k *
        ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I) *
          originMellinQ h ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (1 + |t|) ^ k * (C₀ / |t| ^ n) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 ^ k * C₀ := by
        rw [mul_div_assoc', div_le_iff₀ (pow_pos htpos n)]
        calc (1 + |t|) ^ k * C₀ ≤ (2 ^ k * |t| ^ k) * C₀ :=
              mul_le_mul_of_nonneg_right hpow (le_of_lt hC₀pos)
          _ = 2 ^ k * C₀ * |t| ^ k := by ring
          _ ≤ 2 ^ k * C₀ * |t| ^ n :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 2 ^ k * C₀ + 1 := by linarith

end DedekindZetaZeroFree.LargeSieve.Vendor

end
