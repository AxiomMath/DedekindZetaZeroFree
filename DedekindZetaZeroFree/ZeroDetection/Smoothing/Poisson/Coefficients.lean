module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorCoefficients

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private theorem a_eq_trunc (U V : ℝ) (n : Ideal (𝓞 F)) (hpos : 0 < Ideal.absNorm n)
    (hU : (Ideal.absNorm n : ℝ) ≤ U ^ qExp) (hV : (Ideal.absNorm n : ℝ) ≤ V ^ (2 : ℕ)) :
    a F U n = Detector.truncatedIdealMoebius F V n := by
  unfold a Detector.truncatedIdealMoebius
  apply finsum_congr
  intro d
  by_cases h : d ≠ ⊥ ∧ d ∣ n
  · have hle : (Ideal.absNorm d : ℝ) ≤ (Ideal.absNorm n : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm h.2)
    rw [if_pos ⟨h.1, h.2, hle.trans hU⟩, if_pos ⟨h.1, h.2, hle.trans hV⟩]
  · rw [if_neg (fun x => h ⟨x.1, x.2.1⟩), if_neg (fun x => h ⟨x.1, x.2.1⟩)]

theorem a_one (U : ℝ) (hU : 2 ≤ U) : a F U 1 = 1 := by
  have hpow : (1 : ℝ) ≤ U ^ qExp := Real.one_le_rpow (by linarith) (by unfold qExp; norm_num)
  rw [a_eq_trunc F U 2 1 (by simp) (by simp [hpow]) (by norm_num)]
  rw [Ideal.one_eq_top]
  exact Detector.truncatedIdealMoebius_top F 2 (le_refl _)

theorem a_eq_zero (U : ℝ) (hU : 2 ≤ U) (n : Ideal (𝓞 F))
    (hn1 : (1 : ℝ) < (Ideal.absNorm n : ℝ))
    (hn : (Ideal.absNorm n : ℝ) ≤ U ^ qExp) : a F U n = 0 := by
  have hpos : 0 < Ideal.absNorm n := by
    have : (0 : ℝ) < Ideal.absNorm n := by linarith
    exact_mod_cast this
  have hn0 : n ≠ ⊥ := by
    rintro rfl
    simp at hpos
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = max 2 (Ideal.absNorm n : ℝ) := ⟨_, rfl⟩
  have hV2 : 2 ≤ V := by rw [hVdef]; exact le_max_left _ _
  have hVn : (Ideal.absNorm n : ℝ) ≤ V := by rw [hVdef]; exact le_max_right _ _
  have hNV : (Ideal.absNorm n : ℝ) ≤ V ^ (2 : ℕ) := by nlinarith [hVn, hV2]
  rw [a_eq_trunc F U V n hpos hn hNV]
  exact Detector.truncatedIdealMoebius_eq_zero F V hV2 n hn0 hn1 hNV

private theorem abs_a_le_count (U : ℝ) (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    |a F U n| ≤ (Detector.idealDivisorCount F n : ℝ) := by
  classical
  let D := (Detector.ideal_divisors_finite F n hn).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n := Set.Finite.mem_toFinset _
  have hsupport : Function.support (fun d : Ideal (𝓞 F) =>
      if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ qExp then
        (Detector.idealMoebius F d : ℝ) else 0) ⊆ D := by
    intro d hd
    apply (hD d).mpr
    by_contra hd'
    simp only [Function.mem_support] at hd
    exact hd (if_neg (fun h => hd' ⟨h.1, h.2.1⟩))
  unfold a
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  calc _ ≤ ∑ d ∈ D, |(if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ qExp then
        (Detector.idealMoebius F d : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · unfold Detector.idealMoebius UniqueFactorizationMonoid.moebius
        split_ifs <;> simp [Int.cast_pow, abs_pow]
      · simp
    _ = (Detector.idealDivisorCount F n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      exact (Set.ncard_eq_toFinset_card _ (Detector.ideal_divisors_finite F n hn)).symm

theorem abs_a_le (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 2 ≤ U → ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      |a F U n| ≤ C * (Ideal.absNorm n : ℝ) ^ η := by
  obtain ⟨C, hC, hbound⟩ := Detector.ideal_divisor_bound F η hη
  exact ⟨C, hC, fun U _ n hn => (abs_a_le_count F U n hn).trans (hbound n hn)⟩

theorem energy_le (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 2 ≤ U → ∀ N : ℝ, 2 ≤ N →
      ∑ᶠ n : Ideal (𝓞 F),
        (if N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N then
          |a F U n| ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) else 0) ≤
        C * N ^ (1 - 2 * σ₀ + η) := by
  obtain ⟨C₁, hC₁, hA⟩ := abs_a_le F (η / 2) (by linarith)
  obtain ⟨C₂, hC₂1, hCnt, -⟩ := LargeSieve.exists_ideal_count_bound_finset F
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = η - 2 * σ₀ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ |t| := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hK1 : 1 ≤ K := by rw [hK]; exact Real.one_le_rpow (by norm_num) (abs_nonneg _)
  refine ⟨2 * C₁ ^ 2 * C₂ * K, by positivity, ?_⟩
  intro U hU N hN
  have hNpos : 0 < N := by linarith
  have hMpos : 0 ≤ C₁ ^ 2 * K * N ^ t := by
    have := Real.rpow_nonneg hNpos.le t
    positivity
  have hsupp : Function.support (fun n : Ideal (𝓞 F) =>
      if N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N then
        |a F U n| ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) else 0)
      ⊆ ↑(LargeSieve.boundedNormIdeals F (2 * N)) := by
    intro n hn
    simp only [Function.mem_support] at hn
    have hc : N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N := by
      by_contra hc
      exact hn (if_neg hc)
    rw [Finset.mem_coe, LargeSieve.mem_boundedNormIdeals]
    exact hc.2
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hterm : ∀ n ∈ LargeSieve.boundedNormIdeals F (2 * N),
      (if N < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * N then
        |a F U n| ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) else 0) ≤ C₁ ^ 2 * K * N ^ t := by
    intro n _
    split_ifs with hc
    · have h0 : (Ideal.absNorm (⊥ : Ideal (𝓞 F)) : ℝ) = 0 := by simp
      have hn0 : n ≠ ⊥ := by
        rintro rfl
        linarith [hc.1, h0]
      have hNn : (0 : ℝ) < Ideal.absNorm n := by linarith [hc.1]
      have hsq : |a F U n| ^ 2 ≤ (C₁ * (Ideal.absNorm n : ℝ) ^ (η / 2)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hA U hU n hn0) 2
      have hpow : ((Ideal.absNorm n : ℝ) ^ (η / 2)) ^ 2 = (Ideal.absNorm n : ℝ) ^ η := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNn.le]; norm_num
      have hcomb : (Ideal.absNorm n : ℝ) ^ η * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀)
          = (Ideal.absNorm n : ℝ) ^ t := by
        rw [← Real.rpow_add hNn, ht]
        congr 1
        ring
      have hr : (Ideal.absNorm n : ℝ) ^ t ≤ K * N ^ t := by
        rcases le_total t 0 with ht0 | ht0
        · have h1 : (Ideal.absNorm n : ℝ) ^ t ≤ N ^ t :=
            Real.rpow_le_rpow_of_nonpos hNpos hc.1.le ht0
          have h2 : (1 : ℝ) ≤ K := hK1
          calc (Ideal.absNorm n : ℝ) ^ t ≤ N ^ t := h1
            _ ≤ K * N ^ t := le_mul_of_one_le_left (Real.rpow_nonneg hNpos.le t) h2
        · have h1 : (Ideal.absNorm n : ℝ) ^ t ≤ (2 * N) ^ t :=
            Real.rpow_le_rpow hNn.le hc.2 ht0
          rw [Real.mul_rpow (by norm_num) hNpos.le] at h1
          have h2 : (2 : ℝ) ^ t ≤ K := by
            rw [hK]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self t)
          calc (Ideal.absNorm n : ℝ) ^ t ≤ (2 : ℝ) ^ t * N ^ t := h1
            _ ≤ K * N ^ t := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hNpos.le t)
      calc |a F U n| ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀)
          ≤ (C₁ * (Ideal.absNorm n : ℝ) ^ (η / 2)) ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) :=
            mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hNn.le _)
        _ = C₁ ^ 2 * ((Ideal.absNorm n : ℝ) ^ η * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀)) := by
            rw [mul_pow, hpow]; ring
        _ = C₁ ^ 2 * (Ideal.absNorm n : ℝ) ^ t := by rw [hcomb]
        _ ≤ C₁ ^ 2 * (K * N ^ t) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = C₁ ^ 2 * K * N ^ t := by ring
    · exact hMpos
  have hcard : ((LargeSieve.boundedNormIdeals F (2 * N)).card : ℝ) ≤ C₂ * (2 * N) :=
    hCnt (2 * N) (by linarith)
  have hexp : N ^ (1 - 2 * σ₀ + η) = N * N ^ t := by
    rw [show 1 - 2 * σ₀ + η = 1 + t by rw [ht]; ring, Real.rpow_add hNpos, Real.rpow_one]
  calc _ ≤ ∑ n ∈ LargeSieve.boundedNormIdeals F (2 * N), C₁ ^ 2 * K * N ^ t :=
        Finset.sum_le_sum hterm
    _ = ((LargeSieve.boundedNormIdeals F (2 * N)).card : ℝ) * (C₁ ^ 2 * K * N ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C₂ * (2 * N)) * (C₁ ^ 2 * K * N ^ t) :=
        mul_le_mul_of_nonneg_right hcard hMpos
    _ = 2 * C₁ ^ 2 * C₂ * K * N ^ (1 - 2 * σ₀ + η) := by
        rw [hexp]; ring

end

end DedekindZetaZeroFree.Quantitative.DetectorCoefficients
