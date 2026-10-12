module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeGcdDecomposition

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma squarefreeKernel_ne_bot {F : Type} [Field F] [NumberField F]
    {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : squarefreeKernel a ≠ ⊥ := by
  have h : squarefreeKernel a ≠ 0 := by
    rw [squarefreeKernel, if_neg ha, Finset.prod_ne_zero_iff]
    intro p hp
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors a :=
      UniqueFactorizationMonoid.mem_primeFactors.mp (Finset.mem_filter.mp hp).1
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor p hp').ne_zero
  rwa [Ideal.zero_eq_bot] at h

private lemma one_le_s {F : Type} [Field F] [NumberField F]
    {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : 1 ≤ s a := by
  have hz : Ideal.absNorm (squarefreeKernel a) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (squarefreeKernel_ne_bot ha)
  have h1 : 1 ≤ Ideal.absNorm (squarefreeKernel a) := Nat.one_le_iff_ne_zero.mpr hz
  unfold s
  exact_mod_cast h1

private lemma s_eq_one_iff {F : Type} [Field F] [NumberField F]
    {a : Ideal (𝓞 F)} : s a = 1 ↔ squarefreeKernel a = ⊤ := by
  unfold s
  rw [Nat.cast_eq_one, Ideal.absNorm_eq_one_iff]

private lemma prod_primes_eq_top {F : Type} [Field F] [NumberField F]
    {S : Finset (Ideal (𝓞 F))} (hS : ∀ p ∈ S, Prime p)
    (h : ∏ p ∈ S, p = ⊤) : S = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hdvd : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q => q) hp
  rw [h] at hdvd
  exact (hS p hp).not_unit (isUnit_of_dvd_one (by simpa [Ideal.one_eq_top] using hdvd))

private lemma exists_sq_of_squarefreeKernel_eq_top {F : Type} [Field F] [NumberField F]
    {a : Ideal (𝓞 F)} (h : squarefreeKernel a = ⊤) : ∃ t, t ^ 2 = a := by
  by_cases ha : a = ⊥
  · exact ⟨⊥, by rw [ha]; simp⟩
  have ha0 : a ≠ 0 := by simpa [Ideal.zero_eq_bot] using ha
  set s := UniqueFactorizationMonoid.normalizedFactors a with hs
  have hker : (∏ p ∈ s.toFinset.filter (fun p => s.count p % 2 = 1), p) = ⊤ := by
    simpa [squarefreeKernel, if_neg ha, hs] using h
  have hS : ∀ p ∈ s.toFinset.filter (fun p => s.count p % 2 = 1), Prime p := by
    intro p hp
    exact UniqueFactorizationMonoid.prime_of_normalized_factor p
      (by rw [← hs]; exact UniqueFactorizationMonoid.mem_primeFactors.mp (Finset.mem_filter.mp hp).1)
  have hempty := prod_primes_eq_top hS hker
  have heven : ∀ p ∈ s.toFinset, s.count p % 2 = 0 := by
    intro p hp
    by_contra hc
    have : p ∈ s.toFinset.filter (fun p => s.count p % 2 = 1) := by
      rw [Finset.mem_filter]; exact ⟨hp, by omega⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty p)
  refine ⟨∏ p ∈ s.toFinset, p ^ (s.count p / 2), ?_⟩
  have h1 : a = ∏ p ∈ s.toFinset, p ^ (s.count p) := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp
      (by simpa [hs] using (UniqueFactorizationMonoid.prod_normalizedFactors ha0).symm)
  rw [h1, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  have h2 : s.count p = 2 * (s.count p / 2) := by
    have := heven p hp
    omega
  rw [← pow_mul]
  congr 1
  omega

private lemma exists_weight_bound (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖W t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1/2:ℝ)) (b := (5/2:ℝ))).exists_bound_of_continuousOn
    hW.smooth.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1/2:ℝ) (5/2)
  · exact le_trans (hB t ht) (le_max_left _ _)
  · rw [hW.zero_outside t ht]; simp

def smallCutoffSquareRows (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (M : ℝ) : Finset (Ideal (𝓞 F)) :=
  (boundedNormIdeals F ((5 / 2) * M)).filter
    (fun a => a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ squarefreeKernel a = ⊤)

private lemma exists_squareRows_card_bound (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Ideal (𝓞 F)) (M : ℝ), 1 ≤ M →
      ((smallCutoffSquareRows F c M).card : ℝ) ≤ C * Real.sqrt M := by
  obtain ⟨C₀, hC₀, hglob, hfin⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  refine ⟨C₀ * Real.sqrt (5/2), by positivity, ?_⟩
  intro c M hM
  set X : ℝ := Real.sqrt ((5/2) * M) with hX
  have hX1 : 1 ≤ X := by
    rw [hX]; apply Real.one_le_sqrt.mpr; nlinarith [hM]
  have hsub : smallCutoffSquareRows F c M
      ⊆ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).image (fun t => t^2) := by
    intro a ha
    rw [smallCutoffSquareRows, Finset.mem_filter] at ha
    rcases ha with ⟨hain, hane, hac, hker⟩
    obtain ⟨t, ht⟩ := exists_sq_of_squarefreeKernel_eq_top hker
    rw [Finset.mem_image]
    refine ⟨t, ?_, ht⟩
    rw [DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
    have hna : (Ideal.absNorm a : ℝ) ≤ (5/2)*M := by
      rw [DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals] at hain; exact hain
    have hsqN : Ideal.absNorm (t^2) = Ideal.absNorm t * Ideal.absNorm t := by
      rw [sq]; exact map_mul Ideal.absNorm t t
    have hsq : (Ideal.absNorm t : ℝ) * (Ideal.absNorm t : ℝ) = (Ideal.absNorm a : ℝ) := by
      rw [← ht, hsqN]; push_cast; ring
    calc (Ideal.absNorm t : ℝ)
        = Real.sqrt ((Ideal.absNorm t : ℝ)^2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
      _ ≤ Real.sqrt ((5/2)*M) := Real.sqrt_le_sqrt (by nlinarith [hsq, hna])
      _ = X := hX.symm
  calc ((smallCutoffSquareRows F c M).card : ℝ)
      ≤ (((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).image (fun t => t^2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ ≤ C₀ * X := hglob X hX1
    _ = C₀ * Real.sqrt (5/2) * Real.sqrt M := by
        rw [hX, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5/2)]
        ring

theorem smallCutoff_T3_difference
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) (hK : 0 < K) (hK1 : K < 1)
    (d : Ideal (𝓞 F)) (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) :
    T3 F c Q W M N K d g lam - T3 F c Q W M N 1 d g lam =
      ∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N,
        if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
          lam b1 * (starRingEnd ℂ) (lam b2) *
            (∑ a ∈ smallCutoffSquareRows F c M,
              (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
                (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a))
        else 0 := by
  have hrow : ∀ a ∈ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5/2)*M),
      (a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < s a) ↔
      ((a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ 1 < s a) ∨ (a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ squarefreeKernel a = ⊤)) := by
    intro a ha
    constructor
    · rintro ⟨ha1, ha2, ha3⟩
      rcases lt_or_eq_of_le (one_le_s ha1) with h | h
      · exact Or.inl ⟨ha1, ha2, h⟩
      · exact Or.inr ⟨ha1, ha2, (s_eq_one_iff).mp h.symm⟩
    · rintro (⟨ha1, ha2, h⟩ | ⟨ha1, ha2, h⟩)
      · exact ⟨ha1, ha2, lt_trans hK1 h⟩
      · exact ⟨ha1, ha2, by rw [(s_eq_one_iff).mpr h]; exact hK1⟩
  have hA : kernelRows F c M K = kernelRows F c M 1 ∪ smallCutoffSquareRows F c M := by
    unfold kernelRows smallCutoffSquareRows
    rw [← Finset.filter_or]
    exact Finset.filter_congr hrow
  have hdisj : Disjoint (kernelRows F c M 1) (smallCutoffSquareRows F c M) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [kernelRows, Finset.mem_filter] at ha1
    rw [smallCutoffSquareRows, Finset.mem_filter] at ha2
    have h1 : 1 < s a := ha1.2.2.2
    have h2 : squarefreeKernel a = ⊤ := ha2.2.2.2
    rw [(s_eq_one_iff).mpr h2] at h1
    exact lt_irrefl 1 h1
  unfold T3
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b1 hb1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b2 hb2
  by_cases h : (b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g)
  · rw [if_pos h, if_pos h, if_pos h]
    rw [hA, Finset.sum_union hdisj]
    ring
  · rw [if_neg h, if_neg h, if_neg h]
    ring

theorem smallCutoff_T3_comparison
    (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
        (M N K : ℝ), 1 ≤ M → 1 ≤ N → 0 < K → K < 1 →
      ∀ (d : Ideal (𝓞 F)) (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
        ‖T3 F c Q W M N K d g lam - T3 F c Q W M N 1 d g lam‖ ≤
            C * Real.sqrt M * N * energy F c N lam := by
  obtain ⟨C₀, hC₀, hglob, hfin⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  obtain ⟨B, hBnn, hB⟩ := exists_weight_bound W hW
  obtain ⟨Cs, hCsnn, hCs⟩ := exists_squareRows_card_bound F
  refine ⟨B * Cs * (C₀ * 2), by positivity, ?_⟩
  intro c Q M N K hM hN hK hK1 d g lam
  rw [smallCutoff_T3_difference F c Q W M N K hK hK1 d g lam]
  set S := smallCutoffSquareRows F c M with hSdef
  set sh := paperShell F c N with hshdef
  have hinner : ∀ b1 ∈ sh, ∀ b2 ∈ sh,
      ‖∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
          (starRingEnd ℂ) ((Q.χ b2) a)‖ ≤ B * (S.card : ℝ) := by
    intro b1 hb1 b2 hb2
    have hb1sf : Squarefree b1 := ((mem_paperShell F c N b1).mp hb1).1
    have hb1c : b1 ⊔ c = ⊤ := ((mem_paperShell F c N b1).mp hb1).2.1
    have hb2sf : Squarefree b2 := ((mem_paperShell F c N b2).mp hb2).1
    have hb2c : b2 ⊔ c = ⊤ := ((mem_paperShell F c N b2).mp hb2).2.1
    calc ‖∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
            (starRingEnd ℂ) ((Q.χ b2) a)‖
        ≤ ∑ a ∈ S, ‖(W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
            (starRingEnd ℂ) ((Q.χ b2) a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ S, B := by
          apply Finset.sum_le_sum
          intro a _
          have hWle : ‖(W ((Ideal.absNorm a : ℝ) / M) : ℂ)‖ ≤ B := by
            simpa [Complex.norm_real, Real.norm_eq_abs] using hB _
          have hχ1 : ‖(Q.χ b1) a‖ ≤ 1 := quadraticFamily_norm_le_one Q hb1sf hb1c a
          have hχ2 : ‖(Q.χ b2) a‖ ≤ 1 := quadraticFamily_norm_le_one Q hb2sf hb2c a
          calc ‖(W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                  (starRingEnd ℂ) ((Q.χ b2) a)‖
              = ‖(W ((Ideal.absNorm a : ℝ) / M) : ℂ)‖ * ‖(Q.χ b1) a‖ *
                  ‖(starRingEnd ℂ) ((Q.χ b2) a)‖ := by rw [norm_mul, norm_mul]
            _ = ‖(W ((Ideal.absNorm a : ℝ) / M) : ℂ)‖ * ‖(Q.χ b1) a‖ *
                  ‖(Q.χ b2) a‖ := by rw [Complex.norm_conj]
            _ ≤ B * 1 * 1 := by gcongr
            _ = B := by ring
      _ = B * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hfac : (∑ b1 ∈ sh, ∑ b2 ∈ sh, ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ)))
      = (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖) * (∑ b ∈ sh, ‖lam b‖) := by
    have h1 : ∀ b1, (∑ b2 ∈ sh, ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ)))
        = ‖lam b1‖ * (∑ b2 ∈ sh, ‖lam b2‖) * (B * (S.card : ℝ)) := by
      intro b1
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    calc ∑ b1 ∈ sh, ∑ b2 ∈ sh, ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ))
        = ∑ b1 ∈ sh, ‖lam b1‖ * (∑ b2 ∈ sh, ‖lam b2‖) * (B * (S.card : ℝ)) := by
          apply Finset.sum_congr rfl; intro b1 _; exact h1 b1
      _ = (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖) * (∑ b ∈ sh, ‖lam b‖) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring
  have hCS : (∑ b ∈ sh, ‖lam b‖) ^ 2 ≤ (sh.card : ℝ) * energy F c N lam := by
    have h := sq_sum_le_card_mul_sum_sq (s := sh) (f := fun b => ‖lam b‖)
    simpa [energy, hshdef] using h
  have hSbound : (S.card : ℝ) ≤ Cs * Real.sqrt M := hCs c M hM
  have hshbound : (sh.card : ℝ) ≤ C₀ * (2 * N) := by
    have := hfin (2*N) (by linarith) (paperShell F c N)
      (fun b hb => ((mem_paperShell F c N b).mp hb).2.2.2)
    simpa [hshdef] using this
  have hstep : ‖∑ b1 ∈ sh, ∑ b2 ∈ sh, (if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
        then lam b1 * (starRingEnd ℂ) (lam b2) *
          (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
            (starRingEnd ℂ) ((Q.χ b2) a))
        else 0)‖
      ≤ (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖) * (∑ b ∈ sh, ‖lam b‖) := by
    calc ‖∑ b1 ∈ sh, ∑ b2 ∈ sh, (if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
          then lam b1 * (starRingEnd ℂ) (lam b2) *
            (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
              (starRingEnd ℂ) ((Q.χ b2) a))
          else 0)‖
        ≤ ∑ b1 ∈ sh, ‖∑ b2 ∈ sh, (if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
            then lam b1 * (starRingEnd ℂ) (lam b2) *
              (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                (starRingEnd ℂ) ((Q.χ b2) a))
            else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ b1 ∈ sh, ∑ b2 ∈ sh, ‖(if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
            then lam b1 * (starRingEnd ℂ) (lam b2) *
              (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                (starRingEnd ℂ) ((Q.χ b2) a))
            else 0)‖ := by
          apply Finset.sum_le_sum; intro b1 _; exact norm_sum_le _ _
      _ ≤ ∑ b1 ∈ sh, ∑ b2 ∈ sh, ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ)) := by
          apply Finset.sum_le_sum; intro b1 hb1
          apply Finset.sum_le_sum; intro b2 hb2
          have hite : ‖(if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
              then lam b1 * (starRingEnd ℂ) (lam b2) *
                (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                  (starRingEnd ℂ) ((Q.χ b2) a))
              else 0)‖
              ≤ ‖lam b1 * (starRingEnd ℂ) (lam b2) *
                (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                  (starRingEnd ℂ) ((Q.χ b2) a))‖ := by
            split_ifs with h
            · rfl
            · rw [norm_zero]; exact norm_nonneg _
          have hF1 : ‖lam b1 * (starRingEnd ℂ) (lam b2) *
                (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                  (starRingEnd ℂ) ((Q.χ b2) a))‖
              ≤ ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ)) := by
            calc ‖lam b1 * (starRingEnd ℂ) (lam b2) *
                    (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                      (starRingEnd ℂ) ((Q.χ b2) a))‖
                = ‖lam b1‖ * ‖(starRingEnd ℂ) (lam b2)‖ *
                    ‖(∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                      (starRingEnd ℂ) ((Q.χ b2) a))‖ := by rw [norm_mul, norm_mul]
              _ = ‖lam b1‖ * ‖lam b2‖ *
                    ‖(∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
                      (starRingEnd ℂ) ((Q.χ b2) a))‖ := by rw [Complex.norm_conj]
              _ ≤ ‖lam b1‖ * ‖lam b2‖ * (B * (S.card : ℝ)) := by
                  gcongr
                  exact hinner b1 hb1 b2 hb2
          exact le_trans hite hF1
      _ = (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖) * (∑ b ∈ sh, ‖lam b‖) := hfac
  calc ‖∑ b1 ∈ sh, ∑ b2 ∈ sh, (if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g
        then lam b1 * (starRingEnd ℂ) (lam b2) *
          (∑ a ∈ S, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) * (Q.χ b1) a *
            (starRingEnd ℂ) ((Q.χ b2) a))
        else 0)‖
      ≤ (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖) * (∑ b ∈ sh, ‖lam b‖) := hstep
    _ = (B * (S.card : ℝ)) * (∑ b ∈ sh, ‖lam b‖)^2 := by ring
    _ ≤ (B * (S.card : ℝ)) * ((sh.card : ℝ) * energy F c N lam) := by
        apply mul_le_mul_of_nonneg_left hCS
        exact mul_nonneg hBnn (Nat.cast_nonneg _)
    _ ≤ (B * (Cs * Real.sqrt M)) * ((C₀ * (2*N)) * energy F c N lam) := by
        have hEnn : 0 ≤ energy F c N lam := by
          unfold energy; exact Finset.sum_nonneg (fun b _ => by positivity)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hSbound hBnn
        · exact mul_le_mul_of_nonneg_right hshbound hEnn
        · exact mul_nonneg (Nat.cast_nonneg _) hEnn
        · exact mul_nonneg hBnn (mul_nonneg hCsnn (Real.sqrt_nonneg _))
    _ = B * Cs * (C₀ * 2) * Real.sqrt M * N * energy F c N lam := by ring

theorem smallCutoff_B3_comparison
    (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
        (M N K : ℝ), 1 ≤ M → 1 ≤ N → 0 < K → K < 1 →
      ∀ d : Ideal (𝓞 F),
          B3 F c Q W M N K d ≤ B3 F c Q W M N 1 d + C * Real.sqrt M * N := by
  obtain ⟨C₁, hC₁, hT3⟩ := smallCutoff_T3_comparison F W hW
  refine ⟨C₁, hC₁, ?_⟩
  intro c Q M N K hM hN hK hK1 d
  have hCnn : 0 ≤ C₁ * Real.sqrt M * N :=
    mul_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg M)) (by linarith)
  rw [show B3 F c Q W M N K d = sSup ({0} ∪ {x : ℝ | ∃ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
      energy F c N lam ≤ 1 ∧ x = ‖T3 F c Q W M N K d g lam‖}) from rfl]
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · intro x hx
    rcases hx with hx0 | ⟨g, lam, hen, rfl⟩
    · rw [Set.mem_singleton_iff] at hx0; rw [hx0]
      have := B3_nonneg Q W M N 1 d
      linarith
    · have hsplit : ‖T3 F c Q W M N K d g lam‖ ≤
          B3 F c Q W M N 1 d + C₁ * Real.sqrt M * N := by
        have hdecomp : T3 F c Q W M N K d g lam
            = T3 F c Q W M N 1 d g lam +
              (T3 F c Q W M N K d g lam - T3 F c Q W M N 1 d g lam) := by ring
        calc ‖T3 F c Q W M N K d g lam‖
            = ‖T3 F c Q W M N 1 d g lam +
                (T3 F c Q W M N K d g lam - T3 F c Q W M N 1 d g lam)‖ := by
                conv_lhs => rw [hdecomp]
          _ ≤ ‖T3 F c Q W M N 1 d g lam‖ +
                ‖T3 F c Q W M N K d g lam - T3 F c Q W M N 1 d g lam‖ := norm_add_le _ _
          _ ≤ B3 F c Q W M N 1 d * energy F c N lam +
                C₁ * Real.sqrt M * N * energy F c N lam :=
              add_le_add (norm_T3_le_B3_mul_energy Q W M N 1 d g lam)
                (hT3 c Q M N K hM hN hK hK1 d g lam)
          _ ≤ B3 F c Q W M N 1 d + C₁ * Real.sqrt M * N := by
              have hb : 0 ≤ B3 F c Q W M N 1 d := B3_nonneg Q W M N 1 d
              have h1 : B3 F c Q W M N 1 d * energy F c N lam ≤ B3 F c Q W M N 1 d :=
                mul_le_of_le_one_right hb hen
              have h2 : C₁ * Real.sqrt M * N * energy F c N lam ≤ C₁ * Real.sqrt M * N :=
                mul_le_of_le_one_right hCnn hen
              linarith
      exact hsplit

def smallCutoffEnvelope (α M N K : ℝ) : ℝ :=
  M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * N

theorem smallCutoff_range_bridge
    (ε M N K : ℝ) (hε : 0 < ε) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hK : 0 < K) (hK1 : K < 1)
    (hlower : (N ^ (2 : ℕ) / M) * Real.rpow (M * N) ε ≤ K)
    (hupper : K ≤ M * Real.rpow (M * N) (-ε)) :
    (N ^ (2 : ℕ) / M) * Real.rpow (M * N) ε ≤ 1 ∧
      1 ≤ M * Real.rpow (M * N) (-ε) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hMNpos : 0 < M * N := mul_pos hM0 hN0
  have hRpos : 0 < Real.rpow (M * N) ε := Real.rpow_pos_of_pos hMNpos ε
  have hN2pos : 0 < N ^ (2:ℕ) := by positivity
  have hApos : 0 < (N ^ (2:ℕ) / M) * Real.rpow (M*N) ε :=
    mul_pos (div_pos hN2pos hM0) hRpos
  have hAle1 : (N ^ (2:ℕ) / M) * Real.rpow (M*N) ε ≤ 1 := le_trans hlower (le_of_lt hK1)
  constructor
  · exact hAle1
  · have hN2ge1 : (1:ℝ) ≤ N ^ (2:ℕ) := by nlinarith [hN, sq_nonneg N]
    have hneg : (M*N).rpow (-ε) = ((M*N).rpow ε)⁻¹ := Real.rpow_neg hMNpos.le ε
    have hkey : M * Real.rpow (M*N) (-ε)
        = N^(2:ℕ) / ((N^(2:ℕ)/M) * Real.rpow (M*N) ε) := by
      rw [hneg]; field_simp
    rw [hkey]
    have hden : N^(2:ℕ) / ((N^(2:ℕ)/M) * Real.rpow (M*N) ε) ≥ N^(2:ℕ) := by
      rw [ge_iff_le, le_div_iff₀ hApos]
      nlinarith [hN2pos, hAle1]
    linarith

theorem smallCutoff_envelope_comparison
    (α M N K : ℝ) (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hK : 0 < K) (hK1 : K < 1) :
    smallCutoffEnvelope α M N 1 ≤ 2 * smallCutoffEnvelope α M N K ∧
      Real.sqrt M * N ≤ smallCutoffEnvelope α M N K := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hsMnn : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hMK : M ≤ M / K := by rw [le_div_iff₀ hK]; nlinarith [hM0, hK1, hK]
  have hsM_le : Real.sqrt M ≤ Real.sqrt (M/K) := Real.sqrt_le_sqrt hMK
  have hsMKnn : 0 ≤ Real.sqrt (M/K) := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.rpow K (α - 1/2) := Real.rpow_nonneg hK.le _
  have h2N : 1 + N ≤ 2*N := by linarith
  have hterm : Real.sqrt M + Real.sqrt M * N ≤ 2 * Real.sqrt (M/K) * N := by
    calc Real.sqrt M + Real.sqrt M * N = Real.sqrt M * (1+N) := by ring
      _ ≤ Real.sqrt M * (2*N) := mul_le_mul_of_nonneg_left h2N hsMnn
      _ ≤ 2 * Real.sqrt (M/K) * N := by nlinarith [hsM_le, hsMnn, hsMKnn, hN]
  have h1 : smallCutoffEnvelope α M N 1 = M + N + Real.sqrt M + Real.sqrt M * N := by
    simp [smallCutoffEnvelope]
  constructor
  · rw [h1]
    unfold smallCutoffEnvelope
    nlinarith [hterm, hr, hsMKnn, hN, hM0]
  · unfold smallCutoffEnvelope
    nlinarith [hsM_le, hsMnn, hsMKnn, hr, hN, hM0]

theorem smallCutoff_B3_bottom
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) :
    B3 F c Q W M N K ⊥ = 0 := by
  apply le_antisymm
  · unfold B3
    apply csSup_le
    · exact ⟨0, Or.inl rfl⟩
    · intro x hx
      rcases hx with hx0 | ⟨g, lam, _, rfl⟩
      · rw [Set.mem_singleton_iff] at hx0; rw [hx0]
      · have hT : T3 F c Q W M N K ⊥ g lam = 0 := by
          unfold T3
          apply Finset.sum_eq_zero
          intro b1 hb1
          apply Finset.sum_eq_zero
          intro b2 hb2
          rw [if_neg]
          rintro ⟨hsup, -, -⟩
          have hb1ne : b1 ≠ ⊥ :=
            SquarefreeGcd.ne_bot_of_squarefree ((mem_paperShell F c N b1).mp hb1).1
          exact hb1ne (sup_eq_bot_iff.mp hsup).1
        rw [hT]; simp
  · exact B3_nonneg Q W M N K ⊥

theorem smallCutoff_extend_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (α ε A : ℝ) (hα : 1 ≤ α) (hα2 : α ≤ 2) (hε : 0 < ε) (hA : 0 ≤ A)
    (hatOne : ∀ (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (N ^ (2 : ℕ) / M) * Real.rpow (M * N) ε ≤ 1 →
      1 ≤ M * Real.rpow (M * N) (-ε) →
      ∀ d : Ideal (𝓞 F), d ≠ ⊥ →
        B3 F c Q W M N 1 d ≤
          A * (Ideal.absNorm d : ℝ) ^ (4 : ℕ) * Real.rpow (M * N) ε *
            smallCutoffEnvelope α M N 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M N K : ℝ), 1 ≤ M → 1 ≤ N → 0 < K → K < 1 →
      (N ^ (2 : ℕ) / M) * Real.rpow (M * N) ε ≤ K →
      K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ d : Ideal (𝓞 F), d ≠ ⊥ →
        B3 F c Q W M N K d ≤
          C * (Ideal.absNorm d : ℝ) ^ (4 : ℕ) * Real.rpow (M * N) ε *
            smallCutoffEnvelope α M N K := by
  obtain ⟨Cb, hCb, hB3⟩ := smallCutoff_B3_comparison F W hW
  refine ⟨2*A + Cb, by linarith, ?_⟩
  intro M N K hM hN hK hK1 hl hu d hd
  have hbr := smallCutoff_range_bridge ε M N K hε hM hN hK hK1 hl hu
  have hb1 := hB3 c Q M N K hM hN hK hK1 d
  have hhat := hatOne M N hM hN hbr.1 hbr.2 d hd
  have henv := smallCutoff_envelope_comparison α M N K hα hα2 hM hN hK hK1
  have hNd : (1:ℝ) ≤ (Ideal.absNorm d : ℝ) := by
    have hz : Ideal.absNorm d ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hd
    have h1 : 1 ≤ Ideal.absNorm d := Nat.one_le_iff_ne_zero.mpr hz
    exact_mod_cast h1
  have hMN0 : 0 ≤ M * N := by nlinarith [hM, hN]
  have hMN : (1:ℝ) ≤ Real.rpow (M * N) ε := Real.one_le_rpow (by nlinarith [hM, hN]) hε.le
  have hNd4 : (1:ℝ) ≤ (Ideal.absNorm d : ℝ) ^ (4:ℕ) := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hNd 4
    simpa using this
  have hprod : (1:ℝ) ≤ (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε := by
    have := mul_le_mul hNd4 hMN (by norm_num : (0:ℝ) ≤ 1)
      (by positivity : (0:ℝ) ≤ (Ideal.absNorm d : ℝ) ^ (4:ℕ))
    simpa using this
  have hEnvKnn : 0 ≤ smallCutoffEnvelope α M N K := by
    unfold smallCutoffEnvelope
    have h1 : 0 ≤ M := by linarith
    have h2 : 0 ≤ N := by linarith
    have h3 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1/2) :=
      mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hK.le _)
    have h4 : 0 ≤ Real.sqrt (M/K) * N := mul_nonneg (Real.sqrt_nonneg _) h2
    linarith
  have hAenv : 0 ≤ A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε :=
    mul_nonneg (mul_nonneg hA (by positivity)) (Real.rpow_nonneg hMN0 _)
  calc B3 F c Q W M N K d
      ≤ B3 F c Q W M N 1 d + Cb * Real.sqrt M * N := hb1
    _ ≤ A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
          smallCutoffEnvelope α M N 1 + Cb * Real.sqrt M * N := by linarith [hhat]
    _ ≤ A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
          smallCutoffEnvelope α M N 1 + Cb * smallCutoffEnvelope α M N K := by
        have hCbN : Cb * Real.sqrt M * N ≤ Cb * smallCutoffEnvelope α M N K := by
          have := mul_le_mul_of_nonneg_left henv.2 hCb
          simpa [mul_assoc] using this
        linarith [hCbN]
    _ ≤ A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
          (2 * smallCutoffEnvelope α M N K) + Cb * smallCutoffEnvelope α M N K := by
        have hterm : A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
              smallCutoffEnvelope α M N 1
            ≤ A * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
              (2 * smallCutoffEnvelope α M N K) :=
          mul_le_mul_of_nonneg_left henv.1 hAenv
        linarith [hterm]
    _ ≤ (2*A + Cb) * (Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε *
          smallCutoffEnvelope α M N K := by
        have hCb_le : Cb ≤ Cb * ((Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε) := by
          have := mul_le_mul_of_nonneg_left hprod hCb
          simpa using this
        have h2 : Cb * smallCutoffEnvelope α M N K ≤
            Cb * ((Ideal.absNorm d : ℝ) ^ (4:ℕ) * Real.rpow (M * N) ε) *
              smallCutoffEnvelope α M N K :=
          mul_le_mul_of_nonneg_right hCb_le hEnvKnn
        nlinarith [h2, hAenv, hEnvKnn]

end DedekindZetaZeroFree.LargeSieve.Sieve

end
