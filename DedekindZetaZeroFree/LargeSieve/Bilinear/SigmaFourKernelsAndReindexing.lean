module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.NormalizedReciprocity
public import DedekindZetaZeroFree.Arithmetic.Ideals.FinitePrimeSupportDecomposition
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeKernelNorm
public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterFiniteOrder

@[expose] public section

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

def primeToSquarefreeKernel (c I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors
    (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I)).toFinset.filter (fun p => ¬ p ∣ c), p

def sc (c I : Ideal (𝓞 F)) : ℝ :=
  (Ideal.absNorm (primeToSquarefreeKernel c I) : ℝ)

def HasRapidDecayAtInfinity (h : ℝ → ℂ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧
    ∀ t : ℝ, R ≤ t → ‖h t‖ ≤ C * Real.rpow t (-A)

def S4Term (c m : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (I : Ideal (𝓞 F)) : ℂ :=
  if I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ sc c I ≤ K then
    h ((Ideal.absNorm I : ℝ) / X) * η I else 0

def S4 (c m : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f) : ℂ :=
  ∑' I, S4Term c m K h X η I

def S4allTerm (m : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (I : Ideal (𝓞 F)) : ℂ :=
  if I ≠ ⊥ ∧ I ⊔ m = ⊤ then h ((Ideal.absNorm I : ℝ) / X) * η I else 0

def S4all (m : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f) : ℂ :=
  ∑' I, S4allTerm m h X η I

def S4finite (c m : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X R : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f) : ℂ :=
  ∑ I ∈ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (R * X), S4Term c m K h X η I

def weightedSquareSeries (m : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (a : Ideal (𝓞 F)) : ℂ :=
  ∑' b : Ideal (𝓞 F), if b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤ then
    h ((Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) * (η b) ^ 2 else 0

def squareWeightSeries (m f : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    (a : Ideal (𝓞 F)) : ℂ :=
  ∑' b : Ideal (𝓞 F), if b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤ then
    h ((Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) else 0

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

private theorem upper_support_bound (h : ℝ → ℂ) (hh : HasCompactSupport h) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, h t ≠ 0 → t ≤ R := by
  obtain ⟨B, hB⟩ := hh.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  exact le_trans (hB (subset_closure ht)) (le_max_left _ _)

private theorem term_norm_bound {c m f : Ideal (𝓞 F)} (K : ℝ)
    (h : ℝ → ℂ) {X R : ℝ} (hX : 0 < X)
    (hR : ∀ t : ℝ, h t ≠ 0 → t ≤ R)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (I : Ideal (𝓞 F))
    (hI : S4Term c m K h X η I ≠ 0) : (Ideal.absNorm I : ℝ) ≤ R * X := by
  have hw : h ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    by_cases hc : I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ sc c I ≤ K
    · exact (mul_ne_zero_iff.mp (by simpa [S4Term, hc] using hI)).1
    · simp [S4Term, hc] at hI
  exact (div_le_iff₀ hX).mp (hR _ hw)

private theorem allterm_norm_bound {m f : Ideal (𝓞 F)}
    (h : ℝ → ℂ) {X R : ℝ} (hX : 0 < X)
    (hR : ∀ t : ℝ, h t ≠ 0 → t ≤ R)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (I : Ideal (𝓞 F))
    (hI : S4allTerm m h X η I ≠ 0) : (Ideal.absNorm I : ℝ) ≤ R * X := by
  have hw : h ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    by_cases hc : I ≠ ⊥ ∧ I ⊔ m = ⊤
    · exact (mul_ne_zero_iff.mp (by simpa [S4allTerm, hc] using hI)).1
    · simp [S4allTerm, hc] at hI
  exact (div_le_iff₀ hX).mp (hR _ hw)

theorem compact_support_api :
    (∀ {c m f : Ideal (𝓞 F)} (K : ℝ)
    (h : ℝ → ℂ) (hh : HasCompactSupport h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f),
    (Function.support (S4Term c m K h X η)).Finite) ∧
    (∀ {m f : Ideal (𝓞 F)}
    (h : ℝ → ℂ) (hh : HasCompactSupport h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f),
    (Function.support (S4allTerm m h X η)).Finite) ∧
    (∀ {c m f : Ideal (𝓞 F)} (K : ℝ)
    (h : ℝ → ℂ) (hh : HasCompactSupport h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f),
    ∃ R : ℝ, 0 < R ∧ (∀ t : ℝ, h t ≠ 0 → t ≤ R) ∧
      S4 c m K h X η = S4finite c m K h X R η) ∧
    (∀ (h : ℝ → ℂ) (hh : HasCompactSupport h),
    HasRapidDecayAtInfinity h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c m f K h hh X hX η
    obtain ⟨R, _, hR⟩ := upper_support_bound h hh
    exact (DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le F (R * X)).subset
      (fun I hI => term_norm_bound K h hX hR η I hI)
  · intro m f h hh X hX η
    obtain ⟨R, _, hR⟩ := upper_support_bound h hh
    exact (DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le F (R * X)).subset
      (fun I hI => allterm_norm_bound h hX hR η I hI)
  · intro c m f K h hh X hX η
    obtain ⟨R, hR0, hR⟩ := upper_support_bound h hh
    refine ⟨R, hR0, hR, ?_⟩
    apply tsum_eq_sum'
    intro I hI
    exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr (term_norm_bound K h hX hR η I hI)
  · intro h hh A hA
    obtain ⟨R, hR0, hR⟩ := upper_support_bound h hh
    refine ⟨0, max 1 (R + 1), le_refl 0, le_max_left _ _, ?_⟩
    intro t ht
    have hz : h t = 0 := by
      by_contra hn
      have := hR t hn
      have := le_trans (le_max_right 1 (R + 1)) ht
      linarith
    simp [hz]

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

theorem kernel_algebra :
    (∀ (c a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥),
    sc c (a * b ^ 2) = sc c a) ∧
    (∀ {c m a : Ideal (𝓞 F)} (hc : c ≠ ⊥)
    (hm : m ≠ ⊥) (hcm : c.radical ∣ m) (ha : Squarefree a) (ham : a ⊔ m = ⊤),
    sc c a = (Ideal.absNorm a : ℝ)) := by
  classical
  constructor
  · intro c a b ha hb
    have hab : a * b ^ 2 ≠ ⊥ := mul_ne_zero ha (pow_ne_zero _ hb)
    have hkernel : DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel (a * b ^ 2) =
        DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel a := by
      unfold DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel
      rw [if_neg hab, if_neg ha,
        UniqueFactorizationMonoid.normalizedFactors_mul ha (pow_ne_zero _ hb),
        UniqueFactorizationMonoid.normalizedFactors_pow]
      congr 1
      ext p
      simp only [Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_add,
        Multiset.count_add, two_nsmul, Multiset.count_add]
      constructor
      · intro hp
        have hcount : (UniqueFactorizationMonoid.normalizedFactors a).count p % 2 = 1 := by
          omega
        exact ⟨Multiset.count_pos.mp (by omega), hcount⟩
      · intro hp
        exact ⟨Or.inl hp.1, by omega⟩
    simp only [sc, primeToSquarefreeKernel, hkernel]
  · intro c m a hc hm hcm ha ham
    have hcopc : a ⊔ c = ⊤ := by
      by_contra hne
      obtain ⟨p, hp_max, hp_le⟩ := Ideal.exists_le_maximal (a ⊔ c) hne
      have hp_prime : p.IsPrime := hp_max.isPrime
      have ha_le : a ≤ p := le_trans le_sup_left hp_le
      have hc_le : c ≤ p := le_trans le_sup_right hp_le
      have hm_le : m ≤ p :=
        le_trans (Ideal.dvd_iff_le.mp hcm)
          ((Ideal.IsPrime.radical_le_iff hp_prime).mpr hc_le)
      have htop : (⊤ : Ideal (𝓞 F)) ≤ p := by
        rw [← ham]
        exact sup_le ha_le hm_le
      exact hp_prime.ne_top (top_le_iff.mp htop)
    have hfilter : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors a).toFinset,
        ¬ p ∣ c := by
      intro p hp hpc
      have hpmem := Multiset.mem_toFinset.mp hp
      have hpprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hpmem
      have hpdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpmem
      have htop : (⊤ : Ideal (𝓞 F)) ≤ p := by
        rw [← hcopc]
        exact sup_le (Ideal.dvd_iff_le.mp hpdvd) (Ideal.dvd_iff_le.mp hpc)
      exact hpprime.not_isUnit (Ideal.isUnit_iff.mpr (top_le_iff.mp htop))
    have hnodup :=
      (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha.ne_zero).mp ha
    rw [sc, primeToSquarefreeKernel, DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel_eq_self ha,
      Finset.filter_true_of_mem hfilter, Finset.prod_eq_multiset_prod,
      Multiset.map_id', Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup,
      Ideal.prod_normalizedFactors_eq_self ha.ne_zero]

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

private lemma norm_one_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

private lemma rapid_summable (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (t : Ideal (𝓞 F) → ℝ) (u : ℝ) (hu : 0 < u)
    (ht : ∀ I, I ≠ ⊥ → u * (Ideal.absNorm I : ℝ) ≤ t I) :
    Summable (fun I => if I = ⊥ then (0 : ℝ) else ‖h (t I)‖) := by
  obtain ⟨C, R, hC, hR, hdec⟩ := hh 2 (by norm_num)
  let s := DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (R / u)
  let g : Ideal (𝓞 F) → ℝ := fun I => if I = ⊥ then 0 else ‖h (t I)‖
  have hsmall : Summable (fun I => if I ∈ s then g I else 0) := by
    apply summable_of_ne_finset_zero (s := s)
    intro I hI
    simp [hI]
  have hmajor : Summable (fun I : Ideal (𝓞 F) =>
      C * u ^ (-(2 : ℝ)) * (if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)))) :=
    (DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F 2 (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (g := g) (fun I => by dsimp [g]; split <;> positivity)
      ?_ (hsmall.add hmajor)
  intro I
  by_cases hI : I = ⊥
  · simp [g, hI]
  by_cases hmem : I ∈ s
  · simp only [if_pos hmem, if_neg hI]
    exact le_add_of_nonneg_right (by positivity)
  · simp only [if_neg hmem, if_neg hI, zero_add]
    have hN : 0 < (Ideal.absNorm I : ℝ) := lt_of_lt_of_le zero_lt_one (norm_one_le hI)
    have hlt : R / u < (Ideal.absNorm I : ℝ) :=
      lt_of_not_ge (fun hn => hmem (DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr hn))
    have hRt : R ≤ t I := le_trans (le_of_lt ((div_lt_iff₀ hu).mp hlt))
      (by simpa [mul_comm] using ht I hI)
    dsimp only [g]
    rw [if_neg hI]
    calc
      ‖h (t I)‖ ≤ C * (t I) ^ (-(2 : ℝ)) := hdec _ hRt
      _ ≤ C * (u * (Ideal.absNorm I : ℝ)) ^ (-(2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Real.rpow_le_rpow_of_nonpos (mul_pos hu hN) (ht I hI) (by norm_num)
      _ = C * u ^ (-(2 : ℝ)) * (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.mul_rpow hu.le hN.le]
        ring

theorem rapid_convergence_api :
    (∀ {m f : Ideal (𝓞 F)} (hf : f ≠ ⊥)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f),
    Summable (fun I => ‖S4allTerm m h X η I‖)) ∧
    (∀ {c m f : Ideal (𝓞 F)} (hf : f ≠ ⊥) (K : ℝ)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f),
    Summable (fun I => ‖S4Term c m K h X η I‖)) ∧
    (∀ {m f a : Ideal (𝓞 F)}
    (hf : f ≠ ⊥) (ha : a ≠ ⊥) (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    {X : ℝ} (hX : 0 < X) (η : DedekindZetaZeroFree.RayClassCharacter F f),
    Summable (fun b : Ideal (𝓞 F) => ‖if b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤ then
      h ((Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) * (η b) ^ 2 else 0‖) ∧
    Summable (fun b : Ideal (𝓞 F) => ‖if b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤ then
      h ((Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) else 0‖)) := by
  have hlinear (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h) (X : ℝ) (hX : 0 < X) :
      Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else
        ‖h ((Ideal.absNorm I : ℝ) / X)‖) := by
    apply rapid_summable h hh _ X⁻¹ (inv_pos.mpr hX)
    intro I _
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro m f hf h hh X hX η
    apply Summable.of_nonneg_of_le (fun I => norm_nonneg _) _ (hlinear h hh X hX)
    intro I
    simp only [S4allTerm]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ m = ⊤
    · rw [if_pos hI, if_neg hI.1, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η I)
    · simp only [if_neg hI, norm_zero]
      split <;> positivity
  · intro c m f hf K h hh X hX η
    apply Summable.of_nonneg_of_le (fun I => norm_nonneg _) _ (hlinear h hh X hX)
    intro I
    simp only [S4Term]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ sc c I ≤ K
    · rw [if_pos hI, if_neg hI.1, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η I)
    · simp only [if_neg hI, norm_zero]
      split <;> positivity
  · intro m f a hf ha h hh X hX η
    have hA : 0 < (Ideal.absNorm a : ℝ) := lt_of_lt_of_le zero_lt_one (norm_one_le ha)
    have hs := rapid_summable h hh
      (fun b : Ideal (𝓞 F) => (Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X)
      ((Ideal.absNorm a : ℝ) / X) (div_pos hA hX) (by
        intro b hb
        have hb1 := norm_one_le hb
        have hb2 : (Ideal.absNorm b : ℝ) ≤ (Ideal.absNorm b : ℝ) ^ 2 := by nlinarith
        simpa [div_mul_eq_mul_div] using
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 hA.le) hX.le)
    constructor
    · apply Summable.of_nonneg_of_le (fun b => norm_nonneg _) _ hs
      intro b
      by_cases hb : b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤
      · rw [if_pos hb, if_neg hb.1, norm_mul, norm_pow]
        have hη := DedekindZetaZeroFree.LargeSieve.RayOperations.norm_le_one η b
        exact mul_le_of_le_one_right (norm_nonneg _) (by nlinarith [norm_nonneg (η b)])
      · simp only [if_neg hb, norm_zero]
        split <;> positivity
    · apply Summable.of_nonneg_of_le (fun b => norm_nonneg _) _ hs
      intro b
      split_ifs with hb <;> simp_all

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

 abbrev SfIdeals (F : Type) [Field F] [NumberField F] :=
  {a : Ideal (𝓞 F) // a ≠ ⊥ ∧ Squarefree a}

 abbrev NzIdeals (F : Type) [Field F] [NumberField F] :=
  {b : Ideal (𝓞 F) // b ≠ ⊥}

 def squareMap (p : SfIdeals F × NzIdeals F) : Ideal (𝓞 F) :=
  p.1.val * p.2.val ^ 2

private theorem squareMap_injective : Function.Injective (squareMap (F := F)) := by
  classical
  intro p q heq
  have hc := congrArg UniqueFactorizationMonoid.normalizedFactors heq
  change UniqueFactorizationMonoid.normalizedFactors (p.1.val * p.2.val ^ 2) =
    UniqueFactorizationMonoid.normalizedFactors (q.1.val * q.2.val ^ 2) at hc
  simp only [UniqueFactorizationMonoid.normalizedFactors_mul p.1.property.1
    (pow_ne_zero 2 p.2.property),
    UniqueFactorizationMonoid.normalizedFactors_mul q.1.property.1
    (pow_ne_zero 2 q.2.property), UniqueFactorizationMonoid.normalizedFactors_pow] at hc
  have hp := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      p.1.property.1).mp p.1.property.2)
  have hq := Multiset.nodup_iff_count_le_one.mp
    ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      q.1.property.1).mp q.1.property.2)
  have hcount (a : Ideal (𝓞 F)) :
      (UniqueFactorizationMonoid.normalizedFactors p.1.val).count a =
        (UniqueFactorizationMonoid.normalizedFactors q.1.val).count a ∧
      (UniqueFactorizationMonoid.normalizedFactors p.2.val).count a =
        (UniqueFactorizationMonoid.normalizedFactors q.2.val).count a := by
    have h := congrArg (Multiset.count a) hc
    simp only [Multiset.count_add, Multiset.count_nsmul] at h
    have := hp a
    have := hq a
    omega
  have ha : p.1.val = q.1.val := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
      p.1.property.1 q.1.property.1).mpr (Multiset.ext.mpr fun a => (hcount a).1))
  have hb : p.2.val = q.2.val := associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
      p.2.property q.2.property).mpr (Multiset.ext.mpr fun a => (hcount a).2))
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

private theorem squareMap_range {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ∈ Set.range (squareMap (F := F)) := by
  obtain ⟨b, a, heq, hsf⟩ := exists_sq_mul_squarefree I
  have ha : a ≠ ⊥ := by
    intro hz
    simp [hz] at heq
    exact hI heq.symm
  have hb : b ≠ ⊥ := by
    intro hz
    simp [hz] at heq
    exact hI heq.symm
  exact ⟨(⟨a, ha, hsf⟩, ⟨b, hb⟩), by simpa [squareMap, mul_comm] using heq⟩

private theorem sup_square (a b m : Ideal (𝓞 F)) :
    (a * b ^ 2) ⊔ m = ⊤ ↔ a ⊔ m = ⊤ ∧ b ⊔ m = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff,
    IsCoprime.pow_left_iff (by norm_num : 0 < (2 : ℕ))]

private theorem sup_product (b m f : Ideal (𝓞 F)) :
    b ⊔ (m * f) = ⊤ ↔ b ⊔ m = ⊤ ∧ b ⊔ f = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]

private theorem reindex (m : Ideal (𝓞 F)) {f : Ideal (𝓞 F)}
    (h : ℝ → ℂ) (X : ℝ) (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (P : Ideal (𝓞 F) → Prop)
    (hP : ∀ a b : Ideal (𝓞 F), a ≠ ⊥ → b ≠ ⊥ → (P (a * b ^ 2) ↔ P a))
    (hsum : Summable (fun I : Ideal (𝓞 F) =>
      if I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ P I then
        h ((Ideal.absNorm I : ℝ) / X) * η I else 0)) :
    (∑' I : Ideal (𝓞 F), if I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ P I then
      h ((Ideal.absNorm I : ℝ) / X) * η I else 0) =
    ∑' a : Ideal (𝓞 F), if a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ P a then
      η a * weightedSquareSeries m h X η a else 0 := by
  classical
  let T : Ideal (𝓞 F) → ℂ := fun I =>
    if I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ P I then h ((Ideal.absNorm I : ℝ) / X) * η I else 0
  have ht (a : SfIdeals F) (b : NzIdeals F) :
      T (squareMap (a, b)) =
      if a.val ⊔ m = ⊤ ∧ P a.val then
        η a.val * (if b.val ⊔ (m * f) = ⊤ then
          h ((Ideal.absNorm a.val : ℝ) * (Ideal.absNorm b.val : ℝ) ^ 2 / X) *
            (η b.val) ^ 2 else 0) else 0 := by
    have h0 : a.val * b.val ^ 2 ≠ ⊥ := mul_ne_zero a.property.1
      (pow_ne_zero _ b.property)
    have hb2 : b.val ^ 2 ≠ ⊥ := pow_ne_zero _ b.property
    have hn : (Ideal.absNorm (a.val * b.val ^ 2) : ℝ) =
        (Ideal.absNorm a.val : ℝ) * (Ideal.absNorm b.val : ℝ) ^ 2 := by
      simp
    have he : η (a.val * b.val ^ 2) = η a.val * (η b.val) ^ 2 := by
      simp only [pow_two, η.map_mul']
    simp only [T, squareMap, h0, true_and, sup_square, hP _ _ a.property.1 b.property,
      hn, he, sup_product]
    by_cases ha : a.val ⊔ m = ⊤ ∧ P a.val
    · by_cases hbm : b.val ⊔ m = ⊤
      · by_cases hbf : b.val ⊔ f = ⊤
        · simp [a.property.1, b.property, hb2, ha.1, ha.2, hbm, hbf, mul_assoc, mul_comm, mul_left_comm]
        · have hz : η b.val = 0 := (η.eq_zero_iff' b.val).mpr (Or.inr hbf)
          simp [ha.1, ha.2, hbm, hbf, hz]
      · simp [ha.1, ha.2, hbm]
    · have hx : ¬ ((a.val ⊔ m = ⊤ ∧ b.val ⊔ m = ⊤) ∧ P a.val) := by
        tauto
      simp [ha, hx]
  have heq : (∑' I, T I) = ∑' p : SfIdeals F × NzIdeals F, T (squareMap p) := by
    symm
    apply squareMap_injective.tsum_eq
    intro I hI
    apply squareMap_range
    intro hz
    apply hI
    simp [T, hz]
  rw [heq]
  have hs : Summable (fun p : SfIdeals F × NzIdeals F => T (squareMap p)) :=
    hsum.comp_injective squareMap_injective
  rw [hs.tsum_prod]
  have hi (a : SfIdeals F) :
      (∑' b : NzIdeals F, T (squareMap (a, b))) =
      if a.val ⊔ m = ⊤ ∧ P a.val then
        η a.val * weightedSquareSeries m h X η a.val else 0 := by
    simp_rw [ht]
    by_cases ha : a.val ⊔ m = ⊤ ∧ P a.val
    · simp only [if_pos ha, tsum_mul_left]
      congr 1
      refine (tsum_subtype {b : Ideal (𝓞 F) | b ≠ ⊥}
        (fun b => if b ⊔ (m * f) = ⊤ then
          h ((Ideal.absNorm a.val : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) *
            (η b) ^ 2 else 0)).trans ?_
      unfold weightedSquareSeries
      apply tsum_congr
      intro b
      by_cases hb : b ≠ ⊥ <;>
        simp [Set.indicator, hb, weightedSquareSeries]
    · simp [ha]
  simp_rw [hi]
  refine (tsum_subtype {a : Ideal (𝓞 F) | a ≠ ⊥ ∧ Squarefree a}
    (fun a => if a ⊔ m = ⊤ ∧ P a then
      η a * weightedSquareSeries m h X η a else 0)).trans ?_
  apply tsum_congr
  intro a
  by_cases ha : a ≠ ⊥ ∧ Squarefree a
  · simp [Set.indicator, ha.1, ha.2, and_assoc]
  · have hx : ¬ (a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ P a) := by tauto
    simp [Set.indicator, ha, hx]

theorem squarefree_reindex_api :
    (∀ {c m f : Ideal (𝓞 F)} (hc : c ≠ ⊥)
    (hm : m ≠ ⊥) (hf : f ≠ ⊥) {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive),
    S4 c m K h X η = ∑' a : Ideal (𝓞 F),
      if a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ sc c a ≤ K then
        η a * weightedSquareSeries m h X η a else 0) ∧
    (∀ {m f : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hf : f ≠ ⊥) {X : ℝ} (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive),
    S4all m h X η = ∑' a : Ideal (𝓞 F),
      if a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ then
        η a * weightedSquareSeries m h X η a else 0) := by
  constructor
  · intro c m f hc hm hf K X hK hX h hh η hprim
    unfold S4 S4Term
    apply reindex m h X η (fun I => sc c I ≤ K)
    · intro a b ha hb
      rw [kernel_algebra.1 c a b ha hb]
    · exact (rapid_convergence_api.2.1 hf K h hh hX η).of_norm
  · intro m f hm hf X hX h hh η hprim
    have hr := reindex m h X η (fun _ => True)
      (fun _ _ _ _ => Iff.rfl)
      (by
        have hs : Summable (S4allTerm m h X η) :=
          (rapid_convergence_api.1 (m := m) hf h hh hX η).of_norm
        change Summable (fun I : Ideal (𝓞 F) =>
          if I ≠ ⊥ ∧ I ⊔ m = ⊤ then h ((Ideal.absNorm I : ℝ) / X) * η I else 0) at hs
        simpa only [and_true] using hs)
    simpa only [and_true, S4all, S4allTerm] using hr

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

private theorem sc_squarefree (c a : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (ha : Squarefree a) : sc c a = (Ideal.absNorm (DedekindZetaZeroFree.LargeSieve.Bilinear.goodPart c a) : ℝ) := by
  have hne : a ≠ ⊥ := by
    intro hz
    rw [hz] at ha
    exact not_squarefree_zero ha
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mp ha
  have hprime : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors a).toFinset,
      (¬p ∣ c) ↔ p ∉ DedekindZetaZeroFree.LargeSieve.Bilinear.badPrimes c := by
    intro p hp
    have hp' := UniqueFactorizationMonoid.prime_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
    rw [DedekindZetaZeroFree.LargeSieve.Bilinear.mem_badPrimes hc]
    simp [hp']
  simp only [sc, primeToSquarefreeKernel, DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel_eq_self ha,
    DedekindZetaZeroFree.LargeSieve.Bilinear.goodPart]
  rw [Finset.filter_congr (fun p hp => hprime p hp)]
  rw [← Multiset.toFinset_filter, Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_id', Multiset.toFinset_val, Multiset.dedup_eq_self.mpr
    (Multiset.Nodup.filter _ hnodup)]

private theorem sup_mul_iff (a b d : Ideal (𝓞 F)) :
    a ⊔ (b * d) = ⊤ ↔ a ⊔ b = ⊤ ∧ a ⊔ d = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]

private theorem mul_sup_iff (a b d : Ideal (𝓞 F)) :
    (a * b) ⊔ d = ⊤ ↔ a ⊔ d = ⊤ ∧ b ⊔ d = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff]

private theorem pair_facts {c m e z : Ideal (𝓞 F)} {K : ℝ} (hc : c ≠ ⊥)
    (he : e ∈ DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c) (hem : e ⊔ m = ⊤)
    (hz : z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K) :
    e * z ≠ ⊥ ∧ Squarefree (e * z) ∧ (e * z) ⊔ m = ⊤ ∧ sc c (e * z) ≤ K ∧
    e = DedekindZetaZeroFree.LargeSieve.Bilinear.badPart c (e * z) ∧ z = DedekindZetaZeroFree.LargeSieve.Bilinear.goodPart c (e * z) := by
  obtain ⟨he0, hesf, hesup⟩ := (DedekindZetaZeroFree.LargeSieve.Bilinear.mem_squarefreeBadPool hc).mp he
  obtain ⟨hzsf, hzc, hzn⟩ := (DedekindZetaZeroFree.LargeSieve.Sieve.mem_idealAdmissibleFinset F (m * c) K z).mp hz
  obtain ⟨hzm, hzc⟩ := (sup_mul_iff z m c).mp hzc
  have hz0 : z ≠ ⊥ := hzsf.ne_zero
  have hez0 : e * z ≠ ⊥ := mul_ne_zero he0 hz0
  have hcop : IsRelPrime e z := by
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors he0).mpr
    intro p hpe hpz hp
    exact hp.not_isUnit ((Ideal.isCoprime_iff_sup_eq.mpr hzc).isRelPrime hpz
      (hesup p hp hpe))
  have hezsf : Squarefree (e * z) := squarefree_mul_iff.mpr ⟨hcop, hesf, hzsf⟩
  obtain ⟨heb, hzg⟩ := DedekindZetaZeroFree.LargeSieve.Bilinear.bad_good_unique hc hez0 he0 hz0 rfl hzc hesup
  refine ⟨hez0, hezsf, (mul_sup_iff e z m).mpr ⟨hem, hzm⟩, ?_, heb, hzg⟩
  rw [sc_squarefree c (e * z) hc hezsf, ← hzg]
  exact hzn

private theorem finite_reindex {c m : Ideal (𝓞 F)} {K : ℝ} (hc : c ≠ ⊥)
    (G : Ideal (𝓞 F) → ℂ) :
    (∑' a : Ideal (𝓞 F), if a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ sc c a ≤ K
      then G a else 0) =
    ∑ e ∈ DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c, if e ⊔ m = ⊤ then
      ∑ z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K, G (e * z) else 0 := by
  let E := (DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c).filter (fun e => e ⊔ m = ⊤)
  let Z := DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K
  let P := E ×ˢ Z
  let S := P.image (fun p => p.1 * p.2)
  have hmem : ∀ a, a ∈ S ↔ a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ sc c a ≤ K := by
    intro a
    constructor
    · intro ha
      obtain ⟨⟨e,z⟩, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨he,hz⟩ := Finset.mem_product.mp hp
      obtain ⟨he,hem⟩ := Finset.mem_filter.mp he
      obtain ⟨h0,hs,hm,hK,_⟩ := pair_facts hc he hem hz
      exact ⟨h0,hs,hm,hK⟩
    · rintro ⟨ha,hs,ham,hK⟩
      obtain ⟨he0,hz0,hprod,hzc,hsup⟩ := DedekindZetaZeroFree.LargeSieve.Bilinear.bad_good_factorization hc ha
      obtain ⟨hem,hzm⟩ := (mul_sup_iff _ _ m).mp (hprod ▸ ham)
      have he := DedekindZetaZeroFree.LargeSieve.Bilinear.badPart_mem_squarefreeBadPool hc ha hs
      have hz : DedekindZetaZeroFree.LargeSieve.Bilinear.goodPart c a ∈ Z := by
        apply (DedekindZetaZeroFree.LargeSieve.Sieve.mem_idealAdmissibleFinset F (m * c) K _).mpr
        refine ⟨(DedekindZetaZeroFree.LargeSieve.Bilinear.squarefree_bad_good hc ha hs).2,
          (sup_mul_iff _ m c).mpr ⟨hzm,hzc⟩, ?_⟩
        rwa [sc_squarefree c a hc hs] at hK
      exact Finset.mem_image.mpr ⟨(_, _),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨he,hem⟩,hz⟩, hprod.symm⟩
  have hinj : Set.InjOn (fun p : Ideal (𝓞 F) × Ideal (𝓞 F) => p.1 * p.2) ↑P := by
    intro p hp q hq heq
    obtain ⟨hep,hzp⟩ := Finset.mem_product.mp hp
    obtain ⟨heq',hzq⟩ := Finset.mem_product.mp hq
    obtain ⟨hep,hepm⟩ := Finset.mem_filter.mp hep
    obtain ⟨heq',heqm⟩ := Finset.mem_filter.mp heq'
    obtain ⟨_,_,_,_,hpb,hpg⟩ := pair_facts hc hep hepm hzp
    obtain ⟨_,_,_,_,hqb,hqg⟩ := pair_facts hc heq' heqm hzq
    change p.1 * p.2 = q.1 * q.2 at heq
    apply Prod.ext
    · rw [hpb, hqb, heq]
    · rw [hpg, hqg, heq]
  rw [tsum_eq_sum (s := S) (fun a ha => by simp [← hmem a, ha])]
  calc
    _ = ∑ a ∈ S, G a := Finset.sum_congr rfl (fun a ha => if_pos ((hmem a).mp ha))
    _ = ∑ p ∈ P, G (p.1 * p.2) := Finset.sum_image hinj
    _ = ∑ e ∈ E, ∑ z ∈ Z, G (e * z) := Finset.sum_product E Z _
    _ = _ := Finset.sum_filter _ _

theorem fixed_primes_reindex_api :
    (∀ {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive),
    S4 c m K h X η = ∑ e ∈ DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c, if e ⊔ m = ⊤ then
      η e * (∑ z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K,
        η z * weightedSquareSeries m h X η (e * z)) else 0) ∧
    (∀ {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive)
    (hquad : ∀ I : Ideal (𝓞 F), (η I) ^ 3 = η I),
    S4 c m K h X η = ∑ e ∈ DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c, if e ⊔ m = ⊤ then
      η e * (∑ z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K,
        η z * squareWeightSeries m f h X (e * z)) else 0) := by
  have hw : ∀ {c m f : Ideal (𝓞 F)} (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥)
      {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X) (h : ℝ → ℂ)
      (hh : HasRapidDecayAtInfinity h) (η : DedekindZetaZeroFree.RayClassCharacter F f)
      (hprim : η.IsPrimitive),
      S4 c m K h X η = ∑ e ∈ DedekindZetaZeroFree.LargeSieve.Bilinear.squarefreeBadPool c, if e ⊔ m = ⊤ then
        η e * (∑ z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K,
          η z * weightedSquareSeries m h X η (e * z)) else 0 := by
    intro c m f hc hm hf K X hK hX h hh η hprim
    rw [squarefree_reindex_api.1 hc hm hf hK hX h hh η hprim, finite_reindex hc]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [η.map_mul']
      ring
    · rfl
  refine ⟨hw, ?_⟩
  intro c m f hc hm hf K X hK hX h hh η hprim hquad
  rw [hw hc hm hf hK hX h hh η hprim]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    unfold weightedSquareSeries squareWeightSeries
    apply tsum_congr
    intro b
    split_ifs with hb
    · obtain ⟨hb0,hbc⟩ := hb
      have hbf := ((sup_mul_iff b m f).mp hbc).2
      have hbη : η b ≠ 0 := by
        intro hzero
        rcases (η.eq_zero_iff' b).mp hzero with hzero | hbad
        · exact hb0 hzero
        · exact hbad hbf
      have hs : (η b) ^ 2 = 1 := by
        apply mul_left_cancel₀ hbη
        simpa only [← pow_succ', mul_one] using hquad b
      rw [hs, mul_one]
    · rfl
  · rfl

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4
variable {F : Type} [Field F] [NumberField F]

private theorem weighted_radical_reindex
    {c m f : Ideal (𝓞 F)} (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥)
    (hcm : c.radical ∣ m) {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive) :
    S4 c m K h X η = ∑ a ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K,
      η a * weightedSquareSeries m h X η a := by
  rw [squarefree_reindex_api.1 hc hm hf hK hX h hh η hprim]
  have hmask (a : Ideal (𝓞 F)) :
      (a ≠ ⊥ ∧ Squarefree a ∧ a ⊔ m = ⊤ ∧ sc c a ≤ K) ↔
        a ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K := by
    rw [DedekindZetaZeroFree.LargeSieve.Sieve.mem_idealAdmissibleFinset]
    constructor
    · rintro ⟨ha, hs, ham, hn⟩
      rw [kernel_algebra.2 hc hm hcm hs ham] at hn
      exact ⟨hs, ham, hn⟩
    · rintro ⟨hs, ham, hn⟩
      exact ⟨hs.ne_zero, hs, ham, by rwa [kernel_algebra.2 hc hm hcm hs ham]⟩
  rw [tsum_eq_sum (s := DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K)
    (fun a ha => if_neg (fun hp => ha ((hmask a).mp hp)))]
  apply Finset.sum_congr rfl
  intro a ha
  exact if_pos ((hmask a).mpr ha)

theorem radical_reindex_api :
    (∀ {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hcm : c.radical ∣ m)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive),
    S4 c m K h X η = ∑ a ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K,
      η a * weightedSquareSeries m h X η a) ∧
    (∀ {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hcm : c.radical ∣ m)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive)
    (hquad : ∀ I : Ideal (𝓞 F), (η I) ^ 3 = η I),
    S4 c m K h X η = ∑ a ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K,
      η a * squareWeightSeries m f h X a) := by
  refine ⟨weighted_radical_reindex, ?_⟩
  intro c m f hc hm hf hcm K X hK hX h hh η hprim hquad
  rw [weighted_radical_reindex hc hm hf hcm hK hX h hh η hprim]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  unfold weightedSquareSeries squareWeightSeries
  apply tsum_congr
  intro b
  by_cases hb : b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤
  · have hbf : b ⊔ f = ⊤ := by
      apply top_unique
      rw [← hb.2]
      exact sup_le_sup_left Ideal.mul_le_right b
    have hne : η b ≠ 0 := by
      intro hz
      rcases (η.eq_zero_iff' b).mp hz with hz | hbad
      · exact hb.1 hz
      · exact hbad hbf
    have hsquare : (η b) ^ 2 = 1 := by
      apply mul_left_cancel₀ hne
      simpa [pow_succ, mul_comm] using hquad b
    simp [hb, hsquare]
  · simp [hb]

end DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

variable {F : Type} [Field F] [NumberField F]

def primeToSquarefreeKernel (c I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors
    (DedekindZetaZeroFree.LargeSieve.Sieve.squarefreeKernel I)).toFinset.filter (fun p => ¬ p ∣ c), p

def sc (c I : Ideal (𝓞 F)) : ℝ :=
  (Ideal.absNorm (primeToSquarefreeKernel c I) : ℝ)

def HasRapidDecayAtInfinity (h : ℝ → ℂ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧
    ∀ t : ℝ, R ≤ t → ‖h t‖ ≤ C * Real.rpow t (-A)

def S4Term (c m : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (I : Ideal (𝓞 F)) : ℂ :=
  if I ≠ ⊥ ∧ I ⊔ m = ⊤ ∧ sc c I ≤ K then
    h ((Ideal.absNorm I : ℝ) / X) * η I else 0

def S4 (c m : Ideal (𝓞 F)) (K : ℝ) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f) : ℂ :=
  ∑' I, S4Term c m K h X η I

def S4allTerm (m : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (I : Ideal (𝓞 F)) : ℂ :=
  if I ≠ ⊥ ∧ I ⊔ m = ⊤ then h ((Ideal.absNorm I : ℝ) / X) * η I else 0

def S4all (m : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f) : ℂ :=
  ∑' I, S4allTerm m h X η I

def squareWeightSeries (m f : Ideal (𝓞 F)) (h : ℝ → ℂ) (X : ℝ)
    (a : Ideal (𝓞 F)) : ℂ :=
  ∑' b : Ideal (𝓞 F), if b ≠ ⊥ ∧ b ⊔ (m * f) = ⊤ then
    h ((Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) ^ 2 / X) else 0

theorem finite_support_S4allTerm {m f : Ideal (𝓞 F)}
    (h : ℝ → ℂ) (hh : HasCompactSupport h) {X : ℝ} (hX : 0 < X)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) :
    (Function.support (S4allTerm m h X η)).Finite := by
  exact (DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4.compact_support_api (F := F)).2.1 h hh hX η

theorem rapidDecay_of_compactSupport (h : ℝ → ℂ) (hh : HasCompactSupport h) :
    HasRapidDecayAtInfinity h := by
  exact (DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4.compact_support_api (F := ℚ)).2.2.2 h hh

theorem S4_reindex_quadratic_of_radical_dvd {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hcm : c.radical ∣ m)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive)
    (hquad : ∀ I : Ideal (𝓞 F), (η I) ^ 3 = η I) :
    S4 c m K h X η = ∑ a ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F m K,
      η a * squareWeightSeries m f h X a := by
  exact (DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4.radical_reindex_api (F := F)).2 hc hm hf hcm hK hX h hh η hprim hquad

theorem S4_reindex_fixed_primes_quadratic {c m f : Ideal (𝓞 F)}
    (hc : c ≠ ⊥) (hm : m ≠ ⊥) (hf : f ≠ ⊥)
    {K X : ℝ} (hK : 1 ≤ K) (hX : 0 < X)
    (h : ℝ → ℂ) (hh : HasRapidDecayAtInfinity h)
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (hprim : η.IsPrimitive)
    (hquad : ∀ I : Ideal (𝓞 F), (η I) ^ 3 = η I) :
    S4 c m K h X η = ∑ e ∈ squarefreeBadPool c, if e ⊔ m = ⊤ then
      η e * (∑ z ∈ DedekindZetaZeroFree.LargeSieve.Sieve.idealAdmissibleFinset F (m * c) K,
        η z * squareWeightSeries m f h X (e * z)) else 0 := by
  exact (DedekindZetaZeroFree.LargeSieve.WeightedSeries.Sigma4.fixed_primes_reindex_api (F := F)).2 hc hm hf hK hX h hh η hprim hquad

end DedekindZetaZeroFree.LargeSieve.Bilinear

end

end
