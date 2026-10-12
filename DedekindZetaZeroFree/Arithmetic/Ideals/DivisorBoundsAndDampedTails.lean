module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

open scoped NumberField Topology
open Filter
open scoped Topology

namespace DedekindZetaZeroFree.Detector

open UniqueFactorizationMonoid

noncomputable def idealDivisorCount (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) : ℕ :=
  Set.ncard {d : Ideal (𝓞 F) | d ≠ ⊥ ∧ d ∣ n}

noncomputable def idealNormCount (F : Type) [Field F] [NumberField F] (X : ℝ) : ℕ :=
  Set.ncard {n : Ideal (𝓞 F) | n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ X}

theorem ideal_divisors_finite (F : Type) [Field F] [NumberField F]
    (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    {d : Ideal (𝓞 F) | d ≠ ⊥ ∧ d ∣ n}.Finite := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine (Ring.HasFiniteQuotients.finite_setOfPred_mem x hx0).subset ?_
  intro d hd
  exact Ideal.le_of_dvd hd.2 hx

theorem ideals_bounded_norm_finite (F : Type) [Field F] [NumberField F] (X : ℝ) :
    {n : Ideal (𝓞 F) | n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ X}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset ?_
  intro n hn
  exact Nat.le_floor hn.2

private theorem divisor_card (F : Type) [Field F] [NumberField F] (n : Ideal (𝓞 F)) (hn : n ≠ ⊥) :
    idealDivisorCount F n ≤ ∏ p ∈ (normalizedFactors n).toFinset, ((normalizedFactors n).count p + 1) := by
  classical
  let s := (normalizedFactors n).toFinset
  let D := {d : Ideal (𝓞 F) | d ≠ ⊥ ∧ d ∣ n}
  haveI := (ideal_divisors_finite F n hn).fintype
  let f : D → ((p : s) → Fin ((normalizedFactors n).count p.val + 1)) := fun d p =>
    ⟨(normalizedFactors d.val).count p.val, Nat.lt_succ_of_le
      (Multiset.count_le_of_le p.val ((dvd_iff_normalizedFactors_le_normalizedFactors d.property.1 hn).mp d.property.2))⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : normalizedFactors a.val = normalizedFactors b.val := by
      apply Multiset.ext.mpr
      intro p
      by_cases hp : p ∈ s
      · exact congrArg Fin.val (congrFun hab ⟨p, hp⟩)
      · have hpa : p ∉ normalizedFactors a.val := by
          intro H
          exact hp (Multiset.mem_toFinset.mpr (Multiset.mem_of_le
            ((dvd_iff_normalizedFactors_le_normalizedFactors a.property.1 hn).mp a.property.2) H))
        have hpb : p ∉ normalizedFactors b.val := by
          intro H
          exact hp (Multiset.mem_toFinset.mpr (Multiset.mem_of_le
            ((dvd_iff_normalizedFactors_le_normalizedFactors b.property.1 hn).mp b.property.2) H))
        rw [Multiset.count_eq_zero.mpr hpa, Multiset.count_eq_zero.mpr hpb]
    apply Subtype.ext
    rw [← Ideal.prod_normalizedFactors_eq_self a.property.1,
      ← Ideal.prod_normalizedFactors_eq_self b.property.1, he]
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_pi] at hc
  simp only [Fintype.card_fin, Finset.prod_coe_sort] at hc
  change Fintype.card D ≤ ∏ p : s, ((normalizedFactors n).count p.val + 1) at hc
  rw [Finset.prod_coe_sort s (fun p => (normalizedFactors n).count p + 1)] at hc
  simpa only [idealDivisorCount, D, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, s] using hc
private theorem local_bound (a : ℝ) (ha : 1 < a) (k : ℕ) :
    (k + 1 : ℝ) ≤ (1 + (a-1)⁻¹) * a^k := by
  have h := k.cast_le_pow_div_sub ha
  have hp : 1 ≤ a^k := one_le_pow₀ ha.le
  rw [div_eq_mul_inv] at h
  nlinarith
private theorem local_large (a : ℝ) (ha : 2 ≤ a) (k : ℕ) :
    (k+1:ℝ) ≤ a^k := by
  have h : (k+1:ℝ) ≤ (2:ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
  exact h.trans (pow_le_pow_left₀ (by norm_num) ha k)

theorem ideal_divisor_bound (F : Type) [Field F] [NumberField F]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      (idealDivisorCount F n : ℝ) ≤ C * (Ideal.absNorm n : ℝ) ^ ε := by
  classical
  let a : ℝ := (2:ℝ)^ε
  have ha : 1 < a := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + (a-1)⁻¹
  have hB : 1 ≤ B := by dsimp [B]; have := inv_nonneg.mpr (sub_nonneg.mpr ha.le); linarith
  let T : ℝ := (2:ℝ)^ε⁻¹
  let e : Finset (Ideal (𝓞 F)) := (ideals_bounded_norm_finite F T).toFinset
  refine ⟨B^e.card, pow_pos (lt_of_lt_of_le zero_lt_one hB) _, ?_⟩
  intro n hn
  let s := (normalizedFactors n).toFinset
  have hp (p : Ideal (𝓞 F)) (hps : p ∈ s) : Prime p :=
    prime_of_normalized_factor p (Multiset.mem_toFinset.mp hps)
  have hlocal (p : Ideal (𝓞 F)) (hps : p ∈ s) :
      (((normalizedFactors n).count p + 1 : ℕ) : ℝ) ≤
      (if p ∈ e then B else 1) * ((Ideal.absNorm p : ℝ)^ε)^((normalizedFactors n).count p) := by
    have hNp : 2 ≤ (Ideal.absNorm p : ℝ) := idealNorm_prime_ge_two p (hp p hps)
    have hap : a ≤ (Ideal.absNorm p : ℝ)^ε := Real.rpow_le_rpow (by norm_num) hNp hε.le
    by_cases hpe : p ∈ e
    · rw [if_pos hpe]
      have hb := local_bound a ha ((normalizedFactors n).count p)
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hap _) (by linarith : 0 ≤ B))
    · rw [if_neg hpe, one_mul]
      have hT : T ≤ (Ideal.absNorm p : ℝ) := by
        by_contra H
        apply hpe
        apply (ideals_bounded_norm_finite F T).mem_toFinset.mpr
        exact ⟨(hp p hps).ne_zero, le_of_lt (lt_of_not_ge H)⟩
      have htwo : (2:ℝ) ≤ (Ideal.absNorm p : ℝ)^ε := by
        have H := Real.rpow_le_rpow (show 0 ≤ T by positivity) hT hε.le
        have he : T^ε = (2:ℝ) := Real.rpow_inv_rpow (by norm_num) hε.ne'
        rwa [he] at H
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact local_large _ htwo _
  have hconst : (∏ p ∈ s, if p ∈ e then B else 1) ≤ B^e.card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hB
    apply Finset.card_le_card
    intro p hps
    exact (Finset.mem_filter.mp hps).2
  have hnorm : (∏ p ∈ s, (Ideal.absNorm p : ℝ)^((normalizedFactors n).count p)) = (Ideal.absNorm n : ℝ) := by
    have hid := Ideal.prod_normalizedFactors_eq_self hn
    rw [Finset.prod_multiset_count] at hid
    have H := congrArg (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ)) hid
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow, s] using H
  have heq : (∏ p ∈ s, ((Ideal.absNorm p : ℝ)^ε)^((normalizedFactors n).count p)) =
      (Ideal.absNorm n : ℝ)^ε := by
    calc
      _ = ∏ p ∈ s, ((Ideal.absNorm p : ℝ)^((normalizedFactors n).count p))^ε := by
        apply Finset.prod_congr rfl
        intro p hps
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
      _ = (∏ p ∈ s, (Ideal.absNorm p : ℝ)^((normalizedFactors n).count p))^ε :=
        Real.finsetProd_rpow s _ (fun p _ => by positivity) ε
      _ = _ := by rw [hnorm]
  calc
    _ ≤ ∏ p ∈ s, (((normalizedFactors n).count p + 1 : ℕ) : ℝ) := by
      exact_mod_cast divisor_card F n hn
    _ ≤ ∏ p ∈ s, (if p ∈ e then B else 1) * ((Ideal.absNorm p : ℝ)^ε)^((normalizedFactors n).count p) :=
      Finset.prod_le_prod₀ (fun p _ => by positivity) hlocal
    _ = (∏ p ∈ s, if p ∈ e then B else 1) * (Ideal.absNorm n : ℝ)^ε := by
      rw [Finset.prod_mul_distrib, heq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (by positivity)

private theorem sqrt_sum (N : ℕ) : (∑ i ∈ Finset.range N, ((i+1:ℕ):ℝ)^(-(1/2:ℝ))) ≤ 2 * Real.sqrt N := by
  have step (i : ℕ) : ((i+1:ℕ):ℝ)^(-(1/2:ℝ)) ≤ 2 * (Real.sqrt (i+1) - Real.sqrt i) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hp : 0 < Real.sqrt (i+1) := Real.sqrt_pos.2 (by positivity)
    rw [inv_eq_one_div, div_le_iff₀ hp]
    have h1 := Real.sq_sqrt (show 0 ≤ (i:ℝ)+1 by positivity)
    have h0 := Real.sq_sqrt (show 0 ≤ (i:ℝ) by positivity)
    have hd := sq_nonneg (Real.sqrt (i+1) - Real.sqrt i)
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := step N
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    linarith

private theorem weighted {F : Type} [Field F] [NumberField F] (K : ℝ)
    (hK : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X)
    (u : Finset (NonzeroIdeal F)) (N : ℕ)
    (hN : ∀ I ∈ u, Ideal.absNorm I.val ≤ N)
    (g : ℕ → ℝ) (hg0 : 0 ≤ g) (hg : Antitone g) :
    ∑ I ∈ u, g (Ideal.absNorm I.val - 1) ≤ K * ∑ i ∈ Finset.range N, g i := by
  let f : ℕ → ℝ := fun i => ((u.filter (fun I => Ideal.absNorm I.val - 1 = i)).card : ℝ)
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, f i =
      ((u.filter (fun I => Ideal.absNorm I.val - 1 < k)).card : ℝ) := by
    simp only [f, ← Finset.sum_boole]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    simp
  have hfc (k : ℕ) (hk : k ≤ N) : ∑ i ∈ Finset.range k, f i ≤
      ∑ i ∈ Finset.range k, K := by
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    by_cases hk0 : k = 0
    · simp [hk0]
    have hsub : (↑(u.filter (fun I => Ideal.absNorm I.val - 1 < k)) : Set (NonzeroIdeal F)) ⊆
        normBoundedIdeals F k := by
      intro I hI
      have hi := (Finset.mem_filter.mp hI).2
      have hp := (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
      change (Ideal.absNorm I.val : ℝ) ≤ (k : ℝ)
      exact_mod_cast (show Ideal.absNorm I.val ≤ k by omega)
    have hc := Set.ncard_le_ncard hsub (normBoundedIdeals_finite F k)
    have hb := hK k (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0))
    exact (by exact_mod_cast hc : ((u.filter (fun I => Ideal.absNorm I.val - 1 < k)).card : ℝ) ≤
      ((normBoundedIdeals F k).ncard : ℝ)).trans hb
  have he : ∑ I ∈ u, g (Ideal.absNorm I.val - 1) = ∑ i ∈ Finset.range N, f i * g i := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun I : NonzeroIdeal F => Ideal.absNorm I.val - 1)
      (t := Finset.range N) (fun I hI => Finset.mem_range.mpr (by have := hN I hI; have := (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)); omega))]
    apply Finset.sum_congr rfl
    intro i hi
    calc ∑ I ∈ u with Ideal.absNorm I.val - 1 = i, g (Ideal.absNorm I.val - 1)
        = ∑ I ∈ u with Ideal.absNorm I.val - 1 = i, g i := by
            apply Finset.sum_congr rfl
            intro I hI
            rw [(Finset.mem_filter.mp hI).2]
         _ = f i * g i := by simp [f, nsmul_eq_mul]
  rw [he, Finset.mul_sum]
  exact Finset.sum_mul_le_sum_mul_of_sum_range_le hfc hg0 (hg.antitoneOn _)

theorem ideal_norm_summation_bounds (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (idealNormCount F X : ℝ) ≤ C * X ∧
      (∑ᶠ d : Ideal (𝓞 F),
        if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
          (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) else 0) ≤ C * X ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨K, K', hK0, hK'0, hKall⟩ := ideal_counting_harmonic_bounds F
  have hK : ∀ X : ℝ, 1 ≤ X → ((normBoundedIdeals F X).ncard : ℝ) ≤ K * X := by
    simpa using (hKall Set.univ).1
  have himage (X : ℝ) : (fun I : NonzeroIdeal F => I.val) '' normBoundedIdeals F X =
      {n : Ideal (𝓞 F) | n ≠ ⊥ ∧ (Ideal.absNorm n : ℝ) ≤ X} := by
    ext n
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I.property, hI⟩
    · intro hn
      exact ⟨⟨n, hn.1⟩, hn.2, rfl⟩
  refine ⟨2*K, by positivity, ?_⟩
  intro X hX
  constructor
  · have he : idealNormCount F X = (normBoundedIdeals F X).ncard := by
      rw [idealNormCount, ← himage]
      exact Set.InjOn.ncard_image (fun a _ b _ h => Subtype.ext h)
    rw [he]
    have := hK X hX
    nlinarith
  · let u := (normBoundedIdeals_finite F X).toFinset
    let v := (ideals_bounded_norm_finite F X).toFinset
    have he : (∑ᶠ d : Ideal (𝓞 F), if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Ideal.absNorm d : ℝ)^(-(1/2:ℝ)) else 0) =
        ∑ I ∈ u, (Ideal.absNorm I.val : ℝ)^(-(1/2:ℝ)) := by
      rw [finsum_eq_sum_of_support_subset (s := v)]
      · have hv : v = u.image (fun I : NonzeroIdeal F => I.val) := by
          apply Finset.coe_injective
          simpa only [v, u, Finset.coe_image, Set.Finite.coe_toFinset] using (himage X).symm
        rw [hv]
        rw [Finset.sum_image (g := fun I : NonzeroIdeal F => I.val) (fun a _ b _ h => Subtype.ext h)]
        apply Finset.sum_congr rfl
        intro I hI
        have hmem : I ∈ normBoundedIdeals F X := (normBoundedIdeals_finite F X).mem_toFinset.mp hI
        rw [if_pos ⟨I.property, hmem⟩]
      · intro n hn
        apply (Set.Finite.mem_toFinset _).mpr
        by_contra H
        simp only [Function.mem_support] at hn
        exact hn (if_neg H)
    rw [he]
    let g : ℕ → ℝ := fun i => ((i+1:ℕ):ℝ)^(-(1/2:ℝ))
    have hg : Antitone g := by
      intro i j hij
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.succ_le_succ hij) (by norm_num)
    have hw := weighted K hK u ⌊X⌋₊ (fun I hI => by
      have hmem : I ∈ normBoundedIdeals F X := (normBoundedIdeals_finite F X).mem_toFinset.mp hI
      exact Nat.le_floor (show (Ideal.absNorm I.val : ℝ) ≤ X from hmem))
      g (fun i => by dsimp [g]; positivity) hg
    have he2 : (fun I : NonzeroIdeal F => g (Ideal.absNorm I.val - 1)) =
        (fun I => (Ideal.absNorm I.val : ℝ)^(-(1/2:ℝ))) := by
      funext I
      simp only [g, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))]
    rw [he2] at hw
    calc
      _ ≤ K * ∑ i ∈ Finset.range ⌊X⌋₊, g i := hw
      _ ≤ K * (2 * Real.sqrt ⌊X⌋₊) := mul_le_mul_of_nonneg_left (sqrt_sum _) hK0.le
      _ ≤ K * (2 * Real.sqrt X) := by gcongr; exact Nat.floor_le (by linarith)
      _ = _ := by rw [← Real.sqrt_eq_rpow]; ring

noncomputable def idealDampedTail (F : Type) [Field F] [NumberField F]
    (α : ℝ → Ideal (𝓞 F) → ℝ) (X β : ℝ) : ℝ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ ∧ X ^ (11 : ℕ) < (Ideal.absNorm n : ℝ) then
      |α X n| * (Ideal.absNorm n : ℝ) ^ (-β) *
        Real.exp (-(Ideal.absNorm n : ℝ) / X ^ (10 : ℕ)) else 0

private theorem exp_poly_bound (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ 6 / t ^ 3 := by
  have h := Real.pow_div_factorial_le_exp t ht.le 3
  norm_num at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos ht _)).mpr
  nlinarith
private theorem term_bound (C X β N A : ℝ) (hC : 0 < C) (hX : 2 ≤ X)
    (hβ : (0.996 : ℝ) ≤ β) (hN : 1 ≤ N) (hA : 0 ≤ A) (hAC : A ≤ C * N) :
    A * N ^ (-β) * Real.exp (-N / X ^ (10 : ℕ)) ≤
      C * 6 * X ^ (30 : ℕ) * N ^ (-(2 : ℝ)) := by
  have hXp : 0 < X := by linarith
  have hNp : 0 < N := by linarith
  have hr : N ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have he : Real.exp (-N / X ^ (10 : ℕ)) ≤ 6 / (N / X ^ (10 : ℕ)) ^ 3 := by
    simpa only [neg_div] using exp_poly_bound (N / X ^ (10 : ℕ)) (by positivity)
  have hm : A * N ^ (-β) ≤ C * N :=
    le_trans (mul_le_of_le_one_right hA hr) hAC
  calc
    _ ≤ (C * N) * (6 / (N / X ^ (10 : ℕ)) ^ 3) :=
      mul_le_mul hm he (Real.exp_nonneg _) (by positivity)
    _ = C * 6 * X ^ (30 : ℕ) * N ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hNp.le, Real.rpow_two]
      field_simp

theorem ideal_damped_tail_summable (F : Type) [Field F] [NumberField F]
    (α : ℝ → Ideal (𝓞 F) → ℝ)
    (hα : ∀ X : ℝ, 2 ≤ X → ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      |α X n| ≤ (idealDivisorCount F n : ℝ))
    (X β : ℝ) (hX : 2 ≤ X) (hβ : (0.996 : ℝ) ≤ β) :
    Summable (fun n : Ideal (𝓞 F) =>
      if n ≠ ⊥ ∧ X ^ (11 : ℕ) < (Ideal.absNorm n : ℝ) then
        |α X n| * (Ideal.absNorm n : ℝ) ^ (-β) *
          Real.exp (-(Ideal.absNorm n : ℝ) / X ^ (10 : ℕ)) else 0) := by
  classical
  obtain ⟨C, hC, hCn⟩ := ideal_divisor_bound F 1 (by norm_num)
  have hs := (ideal_norm_rpow_summable F 2 (by norm_num)).mul_left (C * 6 * X ^ (30 : ℕ))
  have hsub : Summable (fun n : NonzeroIdeal F =>
      if X ^ (11 : ℕ) < (Ideal.absNorm n.1 : ℝ) then
        |α X n.1| * (Ideal.absNorm n.1 : ℝ) ^ (-β) *
          Real.exp (-(Ideal.absNorm n.1 : ℝ) / X ^ (10 : ℕ)) else 0) := by
    apply hs.of_nonneg_of_le
    · intro n
      split_ifs <;> positivity
    · intro n
      change _ ≤ C * 6 * X ^ (30 : ℕ) * (Ideal.absNorm n.1 : ℝ) ^ (-(2 : ℝ))
      split_ifs
      · apply term_bound C X β _ _ hC hX hβ
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr n.2)
        · exact abs_nonneg _
        · simpa only [Real.rpow_one] using (hα X hX n.1 n.2).trans (hCn n.1 n.2)
      · positivity
  have hh := (summable_subtype_iff_indicator (s := {n : Ideal (𝓞 F) | n ≠ ⊥})
    (f := fun n => if X ^ (11 : ℕ) < (Ideal.absNorm n : ℝ) then
      |α X n| * (Ideal.absNorm n : ℝ) ^ (-β) * Real.exp (-(Ideal.absNorm n : ℝ) / X ^ (10 : ℕ)) else 0)).mp hsub
  apply hh.congr
  intro n
  simp only [Set.indicator_apply, Set.mem_setOf_eq, ← ite_and]

private theorem split_term_bound (C X β N A : ℝ) (hC : 0 < C) (hX : 2 ≤ X)
    (hβ : (0.996 : ℝ) ≤ β) (hN : 1 ≤ N) (hNX : X ^ (11 : ℕ) < N)
    (hA : 0 ≤ A) (hAC : A ≤ C * N) :
    A * N ^ (-β) * Real.exp (-N / X ^ (10 : ℕ)) ≤
      C * 48 * X ^ (30 : ℕ) * Real.exp (-X / 2) * N ^ (-(2 : ℝ)) := by
  have hXp : 0 < X := by linarith
  have hNp : 0 < N := by linarith
  have hr : N ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have he : Real.exp (-N / (2 * X ^ (10 : ℕ))) ≤ 6 / (N / (2 * X ^ (10 : ℕ))) ^ 3 := by
    simpa only [neg_div] using exp_poly_bound (N / (2 * X ^ (10 : ℕ))) (by positivity)
  have hf : Real.exp (-N / (2 * X ^ (10 : ℕ))) ≤ Real.exp (-X / 2) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * X ^ (10 : ℕ)) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [show X ^ (11 : ℕ) = X * X ^ (10 : ℕ) by ring]
  have hm : A * N ^ (-β) ≤ C * N :=
    le_trans (mul_le_of_le_one_right hA hr) hAC
  have heq : -N / X ^ (10 : ℕ) = -N / (2 * X ^ (10 : ℕ)) + -N / (2 * X ^ (10 : ℕ)) := by ring
  rw [heq, Real.exp_add, ← mul_assoc]
  calc
    _ ≤ ((C * N) * Real.exp (-X / 2)) * (6 / (N / (2 * X ^ (10 : ℕ))) ^ 3) :=
      mul_le_mul (mul_le_mul hm hf (Real.exp_nonneg _) (by positivity)) he
        (Real.exp_nonneg _) (by positivity)
    _ = C * 48 * X ^ (30 : ℕ) * Real.exp (-X / 2) * N ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hNp.le, Real.rpow_two]
      field_simp
      norm_num
private theorem base_summable (F : Type) [Field F] [NumberField F] :
    Summable (fun n : Ideal (𝓞 F) => if n ≠ ⊥ then
      (Ideal.absNorm n : ℝ) ^ (-(2 : ℝ)) else 0) := by
  have hs := ideal_norm_rpow_summable F 2 (by norm_num)
  have hh := (summable_subtype_iff_indicator (s := {n : Ideal (𝓞 F) | n ≠ ⊥})
    (f := fun n : Ideal (𝓞 F) => (Ideal.absNorm n : ℝ) ^ (-(2 : ℝ)))).mp
    (show Summable (fun n : NonzeroIdeal F =>
        (Ideal.absNorm n.1 : ℝ) ^ (-(2 : ℝ))) by exact hs)
  apply hh.congr
  intro n
  simp [Set.indicator_apply]

theorem ideal_damped_tail_uniform (F : Type) [Field F] [NumberField F]
    (α : ℝ → Ideal (𝓞 F) → ℝ)
    (hα : ∀ X : ℝ, 2 ≤ X → ∀ n : Ideal (𝓞 F), n ≠ ⊥ →
      |α X n| ≤ (idealDivisorCount F n : ℝ)) :
    ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ β : ℝ, (0.996 : ℝ) ≤ β →
        |idealDampedTail F α X β| < δ := by
  classical
  obtain ⟨C, hC, hCn⟩ := ideal_divisor_bound F 1 (by norm_num)
  let T := ∑' n : Ideal (𝓞 F), if n ≠ ⊥ then
    (Ideal.absNorm n : ℝ) ^ (-(2 : ℝ)) else 0
  have hT : 0 ≤ T := tsum_nonneg (by intro n; split_ifs <;> positivity)
  have tend : Tendsto (fun X : ℝ => (C * 48 * T) *
      (X ^ (30 : ℕ) * Real.exp (-X / 2))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (30 : ℝ) (1 / 2 : ℝ)
      (by norm_num)
    convert (tendsto_const_nhds (x := C * 48 * T)).mul h using 1
    · ext x; rw [show (30 : ℝ) = (30 : ℕ) by norm_num, Real.rpow_natCast]; congr 2; ring
    · simp
  intro δ hδ
  have ev : ∀ᶠ X : ℝ in atTop,
      (C * 48 * T) * (X ^ (30 : ℕ) * Real.exp (-X / 2)) < δ :=
    tend.eventually (gt_mem_nhds hδ)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp ev
  refine ⟨max 2 X₁, le_max_left _ _, ?_⟩
  intro X hX β hβ
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hhX : X₁ ≤ X := (le_max_right _ _).trans hX
  have hs := ideal_damped_tail_summable F α hα X β hX2 hβ
  let b : Ideal (𝓞 F) → ℝ := fun n => if n ≠ ⊥ then
    (Ideal.absNorm n : ℝ) ^ (-(2 : ℝ)) else 0
  let D : ℝ := C * 48 * X ^ (30 : ℕ) * Real.exp (-X / 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb := (base_summable F).mul_left D
  have hle : idealDampedTail F α X β ≤ D * T := by
    change _ ≤ D * ∑' n, b n
    rw [idealDampedTail, ← (base_summable F).tsum_mul_left]
    apply hs.tsum_le_tsum _ hb
    intro n
    by_cases hn : n ≠ ⊥ ∧ X ^ (11 : ℕ) < (Ideal.absNorm n : ℝ)
    · simp only [if_pos hn, b, if_pos hn.1]
      apply split_term_bound C X β _ _ hC hX2 hβ _ hn.2 (abs_nonneg _)
      · simpa only [Real.rpow_one] using (hα X hX2 n hn.1).trans (hCn n hn.1)
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn.1)
    · simp only [if_neg hn, b]
      split_ifs <;> positivity
  have hn : 0 ≤ idealDampedTail F α X β := by
    apply tsum_nonneg
    intro n
    split_ifs <;> positivity
  rw [abs_of_nonneg hn]
  apply lt_of_le_of_lt hle
  convert hX₁ X hhX using 1
  dsimp [D]
  ring

end DedekindZetaZeroFree.Detector
