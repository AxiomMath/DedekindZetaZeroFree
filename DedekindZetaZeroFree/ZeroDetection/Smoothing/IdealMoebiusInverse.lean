module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorBoundsAndDampedTails
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.Detector

noncomputable def idealMoebius (F : Type) [Field F] [NumberField F]
    (d : Ideal (𝓞 F)) : ℤ :=
  UniqueFactorizationMonoid.moebius d

noncomputable def truncatedIdealMoebius (F : Type) [Field F] [NumberField F]
    (U : ℝ) (n : Ideal (𝓞 F)) : ℝ := by
  classical
  exact ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
      (idealMoebius F d : ℝ) else 0

noncomputable def truncatedIdealInverse (F : Type) [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (U : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ d : Ideal (𝓞 F),
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
      (idealMoebius F d : ℂ) * ω d * (Ideal.absNorm d : ℂ) ^ (-s) else 0

noncomputable def idealLSeries (F : Type) [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} (ω : RayClassCharacter F m) (s : ℂ) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ then ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0

theorem truncatedIdealMoebius_top (F : Type) [Field F] [NumberField F]
    (U : ℝ) (hU : 2 ≤ U) : truncatedIdealMoebius F U ⊤ = 1 := by
  classical
  unfold truncatedIdealMoebius
  rw [finsum_eq_single _ ⊤]
  · have h : (1 : ℝ) ≤ U ^ 2 := by nlinarith
    have htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
    simp only [ne_eq, htop, not_false_eq_true, dvd_refl, Ideal.absNorm_top,
      Nat.cast_one, h, and_self, if_true]
    norm_cast
    simpa only [idealMoebius, Ideal.one_eq_top] using
      UniqueFactorizationMonoid.moebius_one (α := Ideal (𝓞 F))
  · intro d hd
    have hnot : ¬d ∣ (⊤ : Ideal (𝓞 F)) := by
      simpa [Ideal.dvd_iff_le] using hd
    simp [hnot]

open UniqueFactorizationMonoid

private theorem squarefree_prod_subset (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (t : Finset (Ideal (𝓞 F)))
    (ht : t ⊆ (normalizedFactors n).toFinset) :
    (∏ p ∈ t, p) ≠ ⊥ ∧ (∏ p ∈ t, p) ∣ n ∧ Squarefree (∏ p ∈ t, p) ∧
      idealMoebius F (∏ p ∈ t, p) = (-1) ^ t.card := by
  have hp : ∀ p ∈ t, Prime p := by
    intro p hp
    exact prime_of_normalized_factor p (Multiset.mem_toFinset.mp (ht hp))
  have hprod : (∏ p ∈ t, p) ≠ (0 : Ideal (𝓞 F)) :=
    Finset.prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  have hfactor : normalizedFactors (∏ p ∈ t, p) = t.val := by
    simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using normalizedFactors_prod_of_prime hp
  have hsq : Squarefree (∏ p ∈ t, p) := by
    rw [squarefree_iff_nodup_normalizedFactors hprod, hfactor]
    exact t.nodup
  refine ⟨hprod, ?_, hsq, ?_⟩
  · rw [dvd_iff_normalizedFactors_le_normalizedFactors hprod hn, hfactor]
    apply (Multiset.le_iff_subset t.nodup).mpr
    intro p hp
    exact Multiset.mem_toFinset.mp (ht hp)
  · rw [idealMoebius, hsq.moebius_eq, factors_eq_normalizedFactors, hfactor]
    rfl
private theorem mobius_sum_zero (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) (hnt : n ≠ ⊤) :
    (∑ d ∈ (ideal_divisors_finite F n hn).toFinset, (idealMoebius F d : ℝ)) = 0 := by
  classical
  let D := (ideal_divisors_finite F n hn).toFinset
  let P := (normalizedFactors n).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n := Set.Finite.mem_toFinset _
  have hsum : (∑ d ∈ D, (idealMoebius F d : ℝ)) =
      ∑ d ∈ D.filter Squarefree, (idealMoebius F d : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hd'
    have : ¬ Squarefree d := by simpa [hd] using hd'
    simp [idealMoebius, UniqueFactorizationMonoid.moebius_of_not_squarefree this]
  rw [hsum]
  have hbij : (∑ d ∈ D.filter Squarefree, (idealMoebius F d : ℝ)) =
      ∑ t ∈ P.powerset, (-1 : ℝ) ^ t.card := by
    symm
    apply Finset.sum_bij (fun t _ => ∏ p ∈ t, p)
    · intro t ht
      have h := squarefree_prod_subset F n hn t (Finset.mem_powerset.mp ht)
      exact Finset.mem_filter.mpr ⟨(hD _).mpr ⟨h.1, h.2.1⟩, h.2.2.1⟩
    · intro t ht u hu heq
      have htf : normalizedFactors (∏ p ∈ t, p) = t.val := by
        simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
          normalizedFactors_prod_of_prime (fun p hp => prime_of_normalized_factor p
            (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp ht hp)))
      have huf : normalizedFactors (∏ p ∈ u, p) = u.val := by
        simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id'] using
          normalizedFactors_prod_of_prime (fun p hp => prime_of_normalized_factor p
            (Multiset.mem_toFinset.mp (Finset.mem_powerset.mp hu hp)))
      exact Finset.val_injective (htf.symm.trans ((congrArg normalizedFactors heq).trans huf))
    · intro d hd
      obtain ⟨hdD, hsq⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd0, hdn⟩ := (hD d).mp hdD
      refine ⟨(normalizedFactors d).toFinset, ?_, ?_⟩
      · apply Finset.mem_powerset.mpr
        intro p hp
        apply Multiset.mem_toFinset.mpr
        exact Multiset.mem_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn).mp hdn)
          (Multiset.mem_toFinset.mp hp)
      · simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hd0).mp hsq)] using
          associated_iff_eq.mp (prod_normalizedFactors hd0)
    · intro t ht
      rw [(squarefree_prod_subset F n hn t (Finset.mem_powerset.mp ht)).2.2.2]
      simp
  rw [hbij]
  have hP : P.Nonempty := by
    by_contra h
    have hnf : normalizedFactors n = 0 := by
      simpa only [P, Finset.not_nonempty_iff_eq_empty, Multiset.toFinset_eq_empty] using h
    have hunit := (normalizedFactors_eq_zero_iff hn).mp hnf
    exact hnt (Ideal.isUnit_iff.mp hunit)
  have := Finset.prod_add_one (R := ℝ) (f := fun _ : Ideal (𝓞 F) => -1) P
  simpa [Finset.prod_const, zero_pow hP.card_ne_zero] using this.symm

theorem truncatedIdealMoebius_eq_zero (F : Type) [Field F] [NumberField F]
    (U : ℝ) (hU : 2 ≤ U) (n : Ideal (𝓞 F))
    (hn : n ≠ ⊥) (hNorm : 1 < (Ideal.absNorm n : ℝ))
    (hCutoff : (Ideal.absNorm n : ℝ) ≤ U ^ (2 : ℕ)) :
    truncatedIdealMoebius F U n = 0 := by
  classical
  have hnt : n ≠ ⊤ := by
    intro h
    simp [h] at hNorm
  let D := (ideal_divisors_finite F n hn).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n := Set.Finite.mem_toFinset _
  have hcut (d : Ideal (𝓞 F)) (hd : d ∈ D) : (Ideal.absNorm d : ℝ) ≤ U ^ 2 := by
    have hdiv := (hD d).mp hd
    have hle : Ideal.absNorm d ≤ Ideal.absNorm n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hn))
        (map_dvd Ideal.absNorm hdiv.2)
    exact (Nat.cast_le.mpr hle).trans hCutoff
  unfold truncatedIdealMoebius
  rw [finsum_eq_sum_of_support_subset _ (s := D)]
  · have heq : (∑ d ∈ D, if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ 2 then
      (idealMoebius F d : ℝ) else 0) = ∑ d ∈ D, (idealMoebius F d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact if_pos ⟨((hD d).mp hd).1, ((hD d).mp hd).2, hcut d hd⟩
    rw [heq]
    exact mobius_sum_zero F n hn hnt
  · intro d hd
    apply (hD d).mpr
    by_contra hd'
    simp only [Function.mem_support] at hd
    exact hd (if_neg (fun h => hd' ⟨h.1, h.2.1⟩))

theorem truncatedIdealMoebius_abs_le (F : Type) [Field F] [NumberField F]
    (U : ℝ) (hU : 2 ≤ U) (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    |truncatedIdealMoebius F U n| ≤ (idealDivisorCount F n : ℝ) := by
  classical
  let D := (ideal_divisors_finite F n hn).toFinset
  have hD (d : Ideal (𝓞 F)) : d ∈ D ↔ d ≠ ⊥ ∧ d ∣ n :=
    Set.Finite.mem_toFinset _
  have hsupport : Function.support (fun d : Ideal (𝓞 F) =>
      if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ 2 then
        (idealMoebius F d : ℝ) else 0) ⊆ D := by
    intro d hd
    apply (hD d).mpr
    by_contra hd'
    simp only [Function.mem_support] at hd
    exact hd (if_neg (fun h => hd' ⟨h.1, h.2.1⟩))
  unfold truncatedIdealMoebius
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  calc
    _ ≤ ∑ d ∈ D, |if d ≠ ⊥ ∧ d ∣ n ∧ (Ideal.absNorm d : ℝ) ≤ U ^ 2 then
      (idealMoebius F d : ℝ) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · unfold idealMoebius UniqueFactorizationMonoid.moebius
        split_ifs <;> simp [Int.cast_pow, abs_pow]
      · simp
    _ = (idealDivisorCount F n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      exact (Set.ncard_eq_toFinset_card _ (ideal_divisors_finite F n hn)).symm

theorem idealLSeries_summable (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ω : RayClassCharacter F m)
    (hω : ω.IsPrimitive) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0) := by
  classical
  have h := (heckeDirichlet_right_edge F s.re hs m hm ω s le_rfl).1
  exact h.congr fun n => by
    by_cases hn : n ≠ ⊥
    · simp [hn]
    · have hz : ω n = 0 := (ω.eq_zero_iff' n).mpr (Or.inl (not_ne_iff.mp hn))
      simp [hn, hz]

theorem idealLSeries_mul_truncatedInverse (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ω : RayClassCharacter F m)
    (hω : ω.IsPrimitive) (U : ℝ) (hU : 2 ≤ U) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (truncatedIdealMoebius F U n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0) ∧
    HasSum (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ then (truncatedIdealMoebius F U n : ℂ) *
        ω n * (Ideal.absNorm n : ℂ) ^ (-s) else 0)
      (idealLSeries F ω s * truncatedIdealInverse F ω U s) := by
  classical
  let K := (ideals_bounded_norm_finite F (U ^ 2)).toFinset
  have hK (d : Ideal (𝓞 F)) : d ∈ K ↔ d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ 2 :=
    Set.Finite.mem_toFinset _
  let W : Ideal (𝓞 F) → ℂ := fun n => ω n * (Ideal.absNorm n : ℂ) ^ (-s)
  have hzero : W ⊥ = 0 := by
    have hz : ω ⊥ = 0 := (ω.eq_zero_iff' ⊥).mpr (Or.inl rfl)
    simp [W, hz]
  have hmul (a b : Ideal (𝓞 F)) : W (a * b) = W a * W b := by
    dsimp [W]
    rw [ω.map_mul', map_mul Ideal.absNorm, Nat.cast_mul]
    have hp : ((Ideal.absNorm a : ℂ) * (Ideal.absNorm b : ℂ)) ^ (-s) =
        (Ideal.absNorm a : ℂ) ^ (-s) * (Ideal.absNorm b : ℂ) ^ (-s) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm a) : (0 : ℝ) ≤ Ideal.absNorm a)
        (Nat.cast_nonneg (Ideal.absNorm b) : (0 : ℝ) ≤ Ideal.absNorm b) (-s)
    rw [hp]
    ring
  have hW : HasSum W (idealLSeries F ω s) := by
    have heq : (fun n : Ideal (𝓞 F) => if n ≠ ⊥ then W n else 0) = W := by
      funext n
      by_cases hn : n = ⊥ <;> simp [hn, hzero]
    change HasSum W (∑' n, if n ≠ ⊥ then W n else 0)
    rw [heq]
    exact ((idealLSeries_summable F m hm ω hω s hs).congr
      (fun n => congrFun heq n)).hasSum
  let T : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun d n =>
    if n ≠ ⊥ ∧ d ∣ n then (idealMoebius F d : ℂ) * W n else 0
  have hT (d : Ideal (𝓞 F)) (hd : d ∈ K) :
      HasSum (T d) (idealLSeries F ω s * ((idealMoebius F d : ℂ) * W d)) := by
    have hd0 := ((hK d).mp hd).1
    have hinj : Function.Injective (fun n : Ideal (𝓞 F) => n * d) :=
      mul_left_injective₀ hd0
    apply (hinj.hasSum_iff ?_).mp
    · have heq : T d ∘ (fun n : Ideal (𝓞 F) => n * d) =
          fun n => W n * ((idealMoebius F d : ℂ) * W d) := by
        funext n
        dsimp [T, Function.comp_def]
        by_cases hn : n = ⊥
        · simp [hn, hzero]
        · rw [if_pos ⟨mul_ne_zero hn hd0, dvd_mul_left d n⟩, hmul]
          ring
      rw [heq]
      exact hW.mul_right _
    · intro n hn
      have hnd : ¬d ∣ n := by
        rintro ⟨a, ha⟩
        apply hn
        exact ⟨a, by simpa [mul_comm] using ha.symm⟩
      simp [T, hnd]
  have hsum := hasSum_sum hT
  have hcoef (n : Ideal (𝓞 F)) : (∑ d ∈ K, T d n) =
      if n ≠ ⊥ then (truncatedIdealMoebius F U n : ℂ) * W n else 0 := by
    by_cases hn : n ≠ ⊥
    · rw [if_pos hn]
      have ha : truncatedIdealMoebius F U n = ∑ d ∈ K,
          if d ∣ n then (idealMoebius F d : ℝ) else 0 := by
        unfold truncatedIdealMoebius
        rw [finsum_eq_sum_of_support_subset _ (s := K)]
        · apply Finset.sum_congr rfl
          intro d hd
          simp [((hK d).mp hd).1, ((hK d).mp hd).2]
        · intro d hd
          apply (hK d).mpr
          by_contra h
          exact hd (if_neg (fun hh => h ⟨hh.1, hh.2.2⟩))
      rw [ha, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdn : d ∣ n <;> simp [T, hn, hdn]
    · simp [T, hn]
  have hvalue : (∑ d ∈ K, idealLSeries F ω s * ((idealMoebius F d : ℂ) * W d)) =
      idealLSeries F ω s * truncatedIdealInverse F ω U s := by
    have hi : truncatedIdealInverse F ω U s =
        ∑ d ∈ K, (idealMoebius F d : ℂ) * W d := by
      unfold truncatedIdealInverse
      rw [finsum_eq_sum_of_support_subset _ (s := K)]
      · apply Finset.sum_congr rfl
        intro d hd
        rw [if_pos ((hK d).mp hd)]
        dsimp [W]
        ring
      · intro d hd
        apply (hK d).mpr
        by_contra h
        exact hd (if_neg h)
    rw [hi, Finset.mul_sum]
  rw [hvalue] at hsum
  have heq : (fun n => ∑ d ∈ K, T d n) =
      (fun n => if n ≠ ⊥ then (truncatedIdealMoebius F U n : ℂ) * W n else 0) :=
    funext hcoef
  rw [heq] at hsum
  simpa only [W, mul_assoc] using And.intro hsum.summable hsum

theorem truncatedIdealMoebius_tail_uniform (F : Type) [Field F] [NumberField F] :
    ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ β : ℝ, (0.996 : ℝ) ≤ β →
        |idealDampedTail F (truncatedIdealMoebius F) X β| < δ := by
  exact ideal_damped_tail_uniform F (truncatedIdealMoebius F)
    (fun X hX n hn => truncatedIdealMoebius_abs_le F X hX n hn)

end DedekindZetaZeroFree.Detector
