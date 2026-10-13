module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.FrequencyHeightPrefix
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.FrequencyMaximalSieve
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Exponents
public import DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.RightHalfPlane
public import DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDetectorCount31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
  DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.DetectorPrefix DedekindZetaZeroFree.Quantitative.DetectorSieve
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
  DedekindZetaZeroFree.Quantitative.RawDetectorMaximal31
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private def pre (g : Ideal (𝓞 F) → ℂ) (a b : ℝ) : ℂ :=
  ∑ᶠ n : Ideal (𝓞 F),
    if a < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ b then g n else 0

private theorem pre_eq_sum (g : Ideal (𝓞 F) → ℂ) (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ c) :
    pre g a b = ∑ n ∈ (ball_finite F c).toFinset,
      if a < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ b then g n else 0 := by
  unfold pre
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Function.mem_support] at hn
  have h : a < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ b := by
    by_contra hc; exact hn (if_neg hc)
  rw [Set.Finite.coe_toFinset]
  refine ⟨?_, h.2.trans hb⟩
  rintro rfl
  have := h.1
  simp at this
  linarith

private theorem pre_add (g : Ideal (𝓞 F) → ℂ) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) : pre g a c = pre g a b + pre g b c := by
  rw [pre_eq_sum g c ha le_rfl, pre_eq_sum g c ha hbc, pre_eq_sum g c (ha.trans hab) le_rfl,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h1 : (Ideal.absNorm n : ℝ) ≤ b
  · by_cases h2 : a < (Ideal.absNorm n : ℝ)
    · simp [h1, h2, h1.trans hbc, not_lt.mpr h1]
    · simp [h2, not_lt.mpr h1]
  · have h3 : ¬ ((Ideal.absNorm n : ℝ) ≤ b) := h1
    by_cases h2 : (Ideal.absNorm n : ℝ) ≤ c
    · have : a < (Ideal.absNorm n : ℝ) := lt_of_le_of_lt hab (not_le.mp h1)
      simp [h2, this, h3, not_le.mp h1]
    · simp [h2, h3]

private def bco (U M : ℝ) : Ideal (𝓞 F) → ℂ := fun n =>
  if n ≠ ⊥ ∧ M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * M then
    ((DetectorDef.a F U n : ℝ) : ℂ) * (((Ideal.absNorm n : ℝ) ^ (-σ₀) : ℝ) : ℂ) else 0

private def gfun (U γ : ℝ) (ω : Ideal (𝓞 F) → ℂ) : Ideal (𝓞 F) → ℂ := fun n =>
  ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
        (Ideal.absNorm n : ℂ) ^ (-((σ₀ : ℂ) + (γ : ℂ) * Complex.I))

private theorem pre_eq_dyadic (U M y γ : ℝ) (hM : 0 ≤ M) (hy : y ≤ 2 * M)
    (ω : Ideal (𝓞 F) → ℂ) :
    pre (gfun U γ ω) M y = detectorDyadicPrefix F (bco U M) ω M y γ := by
  unfold pre gfun detectorDyadicPrefix
  apply finsum_congr
  intro n
  by_cases h : M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ y
  · have hn : n ≠ ⊥ := by
      rintro rfl
      have := h.1
      simp at this
      linarith
    have hpos : (0 : ℝ) < Ideal.absNorm n := lt_of_le_of_lt hM h.1
    have hc : n ≠ ⊥ ∧ M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ y := ⟨hn, h⟩
    rw [if_pos h, if_pos hc]
    simp only [bco]
    rw [if_pos ⟨hn, h.1, h.2.trans hy⟩]
    have hne : (Ideal.absNorm n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hexp : -((σ₀ : ℂ) + (γ : ℂ) * Complex.I) = ((-σ₀ : ℝ) : ℂ) + (-Complex.I * (γ : ℂ)) := by
      push_cast; ring
    have h2 : (((Ideal.absNorm n : ℝ) ^ (-σ₀) : ℝ) : ℂ) =
        (Ideal.absNorm n : ℂ) ^ ((-σ₀ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hpos.le, Complex.ofReal_natCast]
    rw [hexp, Complex.cpow_add _ _ hne, h2]
    ring
  · have hc : ¬ (n ≠ ⊥ ∧ M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ y) :=
      fun h' => h h'.2
    rw [if_neg h, if_neg hc]

private theorem hm_nonneg (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) :
    0 ≤ detectorHeightPrefixMaximum F b ω N T := by
  unfold detectorHeightPrefixMaximum
  apply Real.sSup_nonneg
  rintro x ⟨t, _, rfl⟩
  unfold detectorPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨y, _, rfl⟩
  positivity

private theorem key_le (U M y γ T : ℝ) (ω : Ideal (𝓞 F) → ℂ) (hM : 2 ≤ M) (hT : 1 ≤ T)
    (hy1 : M ≤ y) (hy2 : y ≤ 2 * M) (hγ : |γ| ≤ T) :
    ‖pre (gfun U γ ω) M y‖ ^ 2 ≤ detectorHeightPrefixMaximum F (bco U M) ω M T := by
  rw [pre_eq_dyadic U M y γ (by linarith) hy2 ω]
  obtain ⟨y0, hy0, -, hall⟩ := detectorPrefixMaximum_attained F (bco U M) ω M γ hM
  obtain ⟨t0, ht0, -, hall2⟩ := detectorHeightPrefixMaximum_attained F (bco U M) ω M T hM hT
  exact (hall y ⟨hy1, hy2⟩).trans (hall2 γ (Set.mem_Icc.mpr (abs_le.mp hγ)))

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem pre_self (g : Ideal (𝓞 F) → ℂ) (a : ℝ) : pre g a a = 0 := by
  unfold pre
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [if_neg]
  rintro ⟨h1, h2⟩
  linarith

private theorem split_lower (U m N y γ T δ : ℝ) (ω : Ideal (𝓞 F) → ℂ) (hm : 2 ≤ m)
    (hT : 1 ≤ T) (hγ : |γ| ≤ T) (hδ : 0 ≤ δ) (hmN : m ≤ N) (hN2 : N < 2 * m) (hNy : N ≤ y)
    (hy : y ≤ 2 * N) (hlow : 3 * δ ≤ ‖pre (gfun U γ ω) N y‖) :
    δ ^ 2 ≤ detectorHeightPrefixMaximum F (bco U m) ω m T ∨
      δ ^ 2 ≤ detectorHeightPrefixMaximum F (bco U (2 * m)) ω (2 * m) T := by
  have hm0 : 0 ≤ m := by linarith
  have e1 : pre (gfun U γ ω) N y = pre (gfun U γ ω) m (min y (2 * m)) -
      pre (gfun U γ ω) m N + pre (gfun U γ ω) (2 * m) (max y (2 * m)) := by
    by_cases hy2 : y ≤ 2 * m
    · rw [min_eq_left hy2, max_eq_right hy2, pre_self]
      have := pre_add (gfun U γ ω) hm0 hmN hNy
      rw [this]; ring
    · have hy2' : 2 * m ≤ y := by linarith
      rw [min_eq_right hy2', max_eq_left hy2']
      have h1 := pre_add (gfun U γ ω) hm0 hmN hN2.le
      have h2 := pre_add (gfun U γ ω) (hm0.trans hmN) hN2.le hy2'
      rw [h2, h1]; ring
  have hA := key_le U m (min y (2 * m)) γ T ω hm hT (le_min (hmN.trans hNy) (by linarith))
    (min_le_right _ _) hγ
  have hB := key_le U m N γ T ω hm hT hmN hN2.le hγ
  have hC := key_le U (2 * m) (max y (2 * m)) γ T ω (by linarith) hT (le_max_right _ _)
    (max_le (by linarith) (by linarith)) hγ
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have n1 := norm_nonneg (pre (gfun U γ ω) m (min y (2 * m)))
  have n2 := norm_nonneg (pre (gfun U γ ω) m N)
  have n3 := norm_nonneg (pre (gfun U γ ω) (2 * m) (max y (2 * m)))
  have l1 : ‖pre (gfun U γ ω) m (min y (2 * m))‖ < δ := by nlinarith
  have l2 : ‖pre (gfun U γ ω) m N‖ < δ := by nlinarith
  have l3 : ‖pre (gfun U γ ω) (2 * m) (max y (2 * m))‖ < δ := by nlinarith
  have := norm_add_le (pre (gfun U γ ω) m (min y (2 * m)) - pre (gfun U γ ω) m N)
    (pre (gfun U γ ω) (2 * m) (max y (2 * m)))
  have := norm_sub_le (pre (gfun U γ ω) m (min y (2 * m))) (pre (gfun U γ ω) m N)
  rw [e1] at hlow
  linarith

private theorem mass_eq (U M : ℝ) (hM : 2 ≤ M) :
    detectorDyadicCoefficientMass F (bco U M) M =
      ∑ᶠ n : Ideal (𝓞 F),
        (if M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * M then
          |DetectorDef.a F U n| ^ 2 * (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) else 0) := by
  unfold detectorDyadicCoefficientMass
  apply finsum_congr
  intro n
  by_cases h : M < (Ideal.absNorm n : ℝ) ∧ (Ideal.absNorm n : ℝ) ≤ 2 * M
  · have hn : n ≠ ⊥ := by
      rintro rfl
      have := h.1
      simp at this
      linarith
    have hx : (0 : ℝ) ≤ (Ideal.absNorm n : ℝ) := Nat.cast_nonneg _
    rw [if_pos ⟨hn, h⟩, if_pos h]
    simp only [bco]
    rw [if_pos ⟨hn, h⟩, norm_mul, mul_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _)]
    have h2 : ((Ideal.absNorm n : ℝ) ^ (-σ₀)) ^ 2 = (Ideal.absNorm n : ℝ) ^ (-2 * σ₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1
      push_cast
      ring
    rw [h2]
  · rw [if_neg h, if_neg (fun h' => h h'.2)]

theorem rawExceptionalSet_card (A ρ : ℝ) (hA : 0 ≤ A) (hρ : RawDetectorHeightPrefix31.HeightSpec D A ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      (FixedData.rawExceptionalSet D ρ U).Finite ∧
        ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨c₁, hc₁, U₁, hU₁, hpre⟩ := RawDetectorHeightPrefix31.detector_prefix D A ρ hρ
  obtain ⟨Clog, hClog, hsieve⟩ := RawDetectorMaximal31.detector_maximal_sieve D
  obtain ⟨Cs, hCs, hs⟩ := hsieve (1 / 100000) (by norm_num)
  obtain ⟨Ce, hCe, hen⟩ := DetectorCoefficients.energy_le F (1 / 100000) (by norm_num)
  obtain ⟨C₂, hC₂, U₂, hU₂, hasym⟩ :=
    DetectorExponentBookkeeping.detector_exponent_bookkeeping c₁ Cs Ce Clog ρ hc₁ hCs hCe hClog hρ.1 hρ.2.1
  refine ⟨C₂, hC₂, max (max U₁ U₂) 8, le_max_of_le_right (by norm_num), ?_⟩
  intro U hU
  have hUU₁ : U₁ ≤ U := (le_max_left _ _).trans ((le_max_left _ _).trans hU)
  have hUU₂ : U₂ ≤ U := (le_max_right _ _).trans ((le_max_left _ _).trans hU)
  have hU8 : 8 ≤ U := (le_max_right _ _).trans hU
  have hU2 : 2 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have hlog2 : 2 ≤ Real.log U := by
    have h1 : Real.log 8 ≤ Real.log U := Real.log_le_log (by norm_num) hU8
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 := Real.log_two_gt_d9
    linarith
  have hlogpos : 0 < Real.log U := by linarith
  have hρ0 : 0 < ρ := hρ.1
  have hT1 : 1 ≤ 4 * U ^ ρ := by
    have : 1 ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρ0.le
    linarith
  have hq : (1 : ℝ) ≤ qExp := by unfold qExp; norm_num
  have hUq : 8 ≤ U ^ qExp := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ U by linarith) hq
    rw [Real.rpow_one] at this
    linarith

  obtain ⟨M, hMdef⟩ : ∃ M : ℕ → ℝ, M = fun k => U ^ qExp / 2 * 2 ^ k := ⟨_, rfl⟩
  have hM0 : ∀ k, U ^ qExp / 2 ≤ M k := by
    intro k
    rw [hMdef]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h0 : 0 ≤ U ^ qExp / 2 := by linarith
    nlinarith
  have hM2 : ∀ k, 2 ≤ M k := fun k => by linarith [hM0 k]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 * Real.log U⌉₊ + 3 := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Finset ℕ,
      I = (Finset.range K).filter (fun k => M k ≤ 2 * U ^ r') := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = c₁ / (3 * Real.log U) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 4 * U ^ ρ := ⟨_, rfl⟩
  obtain ⟨Ek, hEk⟩ : ∃ Ek : ℕ → Set (Frequency D.recipe), Ek = fun k =>
      {u : Frequency D.recipe | u ≠ principalFrequency D.recipe ∧
        U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U ∧
        δ ^ 2 ≤ detectorHeightPrefixMaximum F (bco U (M k))
          (fun J => (FixedData.primMinus D u).character J) (M k) T} := ⟨_, rfl⟩

  have hEkfin : ∀ k, (Ek k).Finite := fun k => by
    rw [hEk]
    exact (card_dyad_le_rowMaximalSum D U (M k) T (δ ^ 2) (bco U (M k)) (by linarith)
      (sq_nonneg δ) _ (fun u hu => hu)).1
  have hEkcard : ∀ k, ((Ek k).ncard : ℝ) ≤
      (3 * Real.log U / c₁) ^ 2 *
        (Cs * (4 * U ^ ρ + 1) * (M k + U ^ 2) * (M k * U) ^ (1 / 100000 : ℝ) *
          Real.log (2 * M k) ^ Clog * (Ce * M k ^ (1 - 2 * σ₀ + 1 / 100000))) := by
    intro k
    have hcd := (card_dyad_le_rowMaximalSum D U (M k) T (δ ^ 2) (bco U (M k)) (by linarith)
      (sq_nonneg δ) (Ek k) (fun u hu => by rw [hEk] at hu; exact hu)).2
    have hsupp : detectorDyadicSupport F (bco U (M k)) (M k) := by
      intro J hJ
      simp only [bco]
      rw [if_neg hJ]
    have h1 := hs U (M k) T (bco U (M k)) hU2 (hM2 k) (by rw [hT]; exact hT1) hsupp
    have h2 := hen U hU2 (M k) (hM2 k)
    rw [← mass_eq U (M k) (hM2 k)] at h2
    have hMpos : 0 < M k := by linarith [hM2 k]
    have hfac : 0 ≤ Cs * (T + 1) * (M k + U ^ 2) * (M k * U) ^ (1 / 100000 : ℝ) *
        Real.log (2 * M k) ^ Clog := by
      have : 0 ≤ Real.log (2 * M k) := Real.log_nonneg (by linarith [hM2 k])
      have := Real.rpow_nonneg this Clog
      have h3 : 0 ≤ (M k * U) ^ (1 / 100000 : ℝ) := Real.rpow_nonneg (by positivity) _
      have : 0 ≤ T := by rw [hT]; positivity
      positivity
    have h3 : (Ek k).ncard * δ ^ 2 ≤ Cs * (T + 1) * (M k + U ^ 2) * (M k * U) ^ (1 / 100000 : ℝ) *
        Real.log (2 * M k) ^ Clog * (Ce * M k ^ (1 - 2 * σ₀ + 1 / 100000)) := by
      refine hcd.trans (h1.trans ?_)
      exact mul_le_mul_of_nonneg_left h2 hfac
    have h4 : ((Ek k).ncard : ℝ) =
        (Ek k).ncard * δ ^ 2 * (3 * Real.log U / c₁) ^ 2 := by
      rw [hδ]; field_simp
    rw [h4, mul_comm]
    rw [hT] at h3
    exact mul_le_mul_of_nonneg_left h3 (by positivity)

  have hMform : ∀ k, M k = U ^ qExp / 2 * 2 ^ k := fun k => by rw [hMdef]
  have hI_mem : ∀ k, k ∈ I ↔ k < K ∧ M k ≤ 2 * U ^ r' := fun k => by
    rw [hI, Finset.mem_filter, Finset.mem_range]
  have hU1 : 1 ≤ U := by linarith
  have hcover : FixedData.rawExceptionalSet D ρ U ⊆ ⋃ k ∈ I, Ek k := by
    intro u hu
    obtain ⟨hu1, hq1, hq2, s, hL, hσ, hs⟩ := hu
    have hre : s.re ≤ 1 := DedekindZetaZeroFree.Quantitative.DetectEuler.IsLZero.re_le_one hL
    obtain ⟨N, y, hN1, hN2, hNy, hy2, hlow⟩ :=
      hpre U hUU₁ u ⟨hu1, hq1, hq2, s, hL, hσ, hs⟩ s hL hσ hre hs
    have hpsE : pre (gfun U s.im (fun J => (FixedData.primMinus D u).character J)) N y =
        prefixSum F U (FixedData.primMinus D u).character s.im N y := rfl
    have hlow' : 3 * δ ≤ ‖pre (gfun U s.im (fun J => (FixedData.primMinus D u).character J)) N y‖ := by
      rw [hpsE, hδ]
      have : 3 * (c₁ / (3 * Real.log U)) = c₁ / Real.log U := by
        field_simp
      linarith
    have hUq0 : 0 < U ^ qExp / 2 := by positivity
    obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (N / (U ^ qExp / 2)) (by norm_num : (1:ℝ) < 2)
    have hPn : N < M n0 := by
      have := (div_lt_iff₀ hUq0).mp hn0
      rw [hMform]
      linarith [mul_comm ((2:ℝ) ^ n0) (U ^ qExp / 2)]
    have hk0 : ∃ k, N < M k := ⟨n0, hPn⟩
    have hspec := Nat.find_spec hk0
    have hk0pos : Nat.find hk0 ≠ 0 := by
      intro h0
      rw [h0, hMform, pow_zero, mul_one] at hspec
      linarith
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hk0 = k + 1 := ⟨Nat.find hk0 - 1, by omega⟩
    have hMk : M k ≤ N := by
      have := Nat.find_min hk0 (show k < Nat.find hk0 by omega)
      exact not_lt.mp this
    have hNk1 : N < M (k + 1) := by
      have := hspec
      rw [hk] at this
      exact this
    have hM2k : M (k + 1) = 2 * M k := by
      rw [hMform, hMform, pow_succ]; ring
    have hMk1 : M (k + 1) ≤ 2 * U ^ r' := by
      rw [hM2k]; linarith
    have hUr : U ^ r' ≤ U ^ qExp * U := by
      have h1 : U ^ r' ≤ U ^ (qExp + 1) :=
        Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num [DetectorDef.r', DetectorDef.qExp])
      rw [Real.rpow_add hUpos, Real.rpow_one] at h1
      exact h1
    have hX : (2:ℝ) ^ (k + 1) ≤ 4 * U := by
      have hPpos : 0 < U ^ qExp := by positivity
      have h1 : U ^ qExp / 2 * 2 ^ (k + 1) ≤ 2 * (U ^ qExp * U) := by
        have := hMk1
        rw [hMform] at this
        linarith [hUr]
      have h2 : U ^ qExp * 2 ^ (k + 1) ≤ U ^ qExp * (4 * U) := by linarith
      exact le_of_mul_le_mul_left h2 hPpos
    have hL2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlogX : ((k:ℝ) + 1) * Real.log 2 ≤ 2 * Real.log 2 + Real.log U := by
      have h1 := Real.log_le_log (by positivity) hX
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [Real.log_pow, Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hUpos.ne'] at h1
      push_cast at h1
      linarith
    have hKlt : ((k:ℝ) + 1) < 2 * Real.log U + 3 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_le_mul_of_nonneg_right hcon (Real.log_nonneg (by norm_num) : (0:ℝ) ≤ Real.log 2),
        mul_nonneg hlogpos.le (sub_nonneg.mpr hL2.le)]
    have hKk : k + 1 < K := by
      have hc := Nat.le_ceil (2 * Real.log U)
      have : ((k + 1 : ℕ) : ℝ) < ((⌈2 * Real.log U⌉₊ + 3 : ℕ) : ℝ) := by
        push_cast; linarith
      rw [hK]
      exact_mod_cast this
    have hMk' : M k ≤ 2 * U ^ r' := by linarith
    have hkI : k ∈ I := (hI_mem k).mpr ⟨by omega, hMk'⟩
    have hk1I : k + 1 ∈ I := (hI_mem (k + 1)).mpr ⟨hKk, hMk1⟩
    have hT1' : 1 ≤ T := by rw [hT]; exact hT1
    have hγ : |s.im| ≤ T := by rw [hT]; exact hs
    have hsplit := split_lower U (M k) N y s.im T δ (fun J => (FixedData.primMinus D u).character J)
      (hM2 k) hT1' hγ hδpos.le hMk (by linarith [hM2k, hNk1]) hNy hy2
      hlow'
    have hmemk : u ∈ Ek k ∨ u ∈ Ek (k + 1) := by
      rcases hsplit with h | h
      · left
        simp only [hEk, Set.mem_setOf_eq]
        exact ⟨hu1, hq1, hq2, h⟩
      · right
        simp only [hEk, Set.mem_setOf_eq, hM2k]
        exact ⟨hu1, hq1, hq2, h⟩
    rcases hmemk with h | h
    · exact Set.mem_iUnion₂.mpr ⟨k, hkI, h⟩
    · exact Set.mem_iUnion₂.mpr ⟨k + 1, hk1I, h⟩
  have hfinI : (⋃ k ∈ I, Ek k).Finite := (Set.Finite.biUnion I.finite_toSet (fun k _ => hEkfin k))
  refine ⟨hfinI.subset hcover, ?_⟩
  have hsub : ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ ((⋃ k ∈ I, Ek k).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hcover hfinI

  have hunion : (⋃ k ∈ I, Ek k) = ↑(I.biUnion fun k => (hEkfin k).toFinset) := by
    ext u; simp
  have hcard : (⋃ k ∈ I, Ek k).ncard ≤ ∑ k ∈ I, (Ek k).ncard := by
    rw [hunion, Set.ncard_coe_finset]
    refine le_trans Finset.card_biUnion_le (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro k _
    rw [Set.ncard_eq_toFinset_card _ (hEkfin k)]
  have hcardR : ((⋃ k ∈ I, Ek k).ncard : ℝ) ≤ ∑ k ∈ I, ((Ek k).ncard : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hcard
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C₂ * U ^ DetectorDef.α / (6 * Real.log U) := ⟨_, rfl⟩
  have hL6pos : 0 < 6 * Real.log U := by linarith
  have hL6 : 6 * Real.log U ≠ 0 := hL6pos.ne'
  have hterm : ∀ k ∈ I, ((Ek k).ncard : ℝ) ≤ B := by
    intro k hk
    have hk' := (hI_mem k).mp hk
    have h1 := hasym U hUU₂ (M k) (hM0 k) hk'.2
    have h2 := hEkcard k
    have h3 := mul_le_mul_of_nonneg_right h2 hL6pos.le
    rw [hB, le_div_iff₀ hL6pos]
    linarith
  have hsum' : ∑ k ∈ I, ((Ek k).ncard : ℝ) ≤ (I.card : ℝ) * B := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul I (fun k => ((Ek k).ncard : ℝ)) B hterm
  have hIK' : I.card ≤ K := by
    rw [hI]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hKL : (K : ℝ) ≤ 6 * Real.log U := by
    have h1 := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ 2 * Real.log U)
    rw [hK]
    push_cast
    linarith
  have hIL : (I.card : ℝ) ≤ 6 * Real.log U := le_trans (by exact_mod_cast hIK') hKL
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg hC₂.le (Real.rpow_nonneg hUpos.le _)) hL6pos.le
  have h6 : (6 * Real.log U) * B = C₂ * U ^ DetectorDef.α := by
    rw [hB]; field_simp
  have hfinal : (I.card : ℝ) * B ≤ C₂ * U ^ DetectorDef.α := by
    have := mul_le_mul_of_nonneg_right hIL hBnn
    linarith
  linarith

end

end DedekindZetaZeroFree.Quantitative.RawDetectorCount31
