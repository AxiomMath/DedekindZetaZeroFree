module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarity

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.Detector.SSupportedPartition

noncomputable section

variable {F : Type} [Field F] [NumberField F]

abbrev badIdeal (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Ideal (𝓞 F) :=
  ∏ v ∈ Sf, v.asIdeal

abbrev SupportedIdeal (Sf : Finset (HeightOneSpectrum (𝓞 F))) :=
  {h : NonzeroIdeal F // IdealSupportedOn h.val (badIdeal Sf)}

abbrev Exterior (Sf : Finset (HeightOneSpectrum (𝓞 F))) :=
  ExteriorIdeal (badIdeal Sf)

def DyadicBand (k : ℕ) (x : ℝ) : Prop :=
  if k = 0 then x = 1 else (2 : ℝ) ^ (k - 1) < x ∧ x ≤ (2 : ℝ) ^ k

private theorem prod_factors (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (normalizedFactors I).prod = I := by
  simpa using prod_normalizedFactors_eq hI
private theorem coprime_of_disjoint (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hd : Disjoint (normalizedFactors I) (normalizedFactors J)) : I ⊔ J = ⊤ := by
  apply Ideal.isUnit_iff.mp
  change IsUnit (gcd I J)
  apply gcd_isUnit_iff_isRelPrime.mpr
  apply (isRelPrime_iff_no_prime_factors hI).mpr
  intro p hpI hpJ hp
  exact Multiset.disjoint_left.mp hd
    ((mem_normalizedFactors_iff hI).mpr ⟨hp, hpI⟩)
    ((mem_normalizedFactors_iff hJ).mpr ⟨hp, hpJ⟩)
private theorem disjoint_of_coprime (I J : Ideal (𝓞 F)) (hc : I ⊔ J = ⊤) :
    Disjoint (normalizedFactors I) (normalizedFactors J) := by
  apply disjoint_normalizedFactors
  apply gcd_isUnit_iff_isRelPrime.mp
  exact Ideal.isUnit_iff.mpr hc
private theorem split_exists (J n : Ideal (𝓞 F)) (hJ : J ≠ ⊥) (hn : n ≠ ⊥) :
    ∃ h a : Ideal (𝓞 F), h ≠ ⊥ ∧ a ≠ ⊥ ∧ IdealSupportedOn h J ∧
      a ⊔ J = ⊤ ∧ n = h * a := by
  let P := fun p : Ideal (𝓞 F) => p ∈ idealPrimeSupport J
  let t := (normalizedFactors n).filter P
  let u := (normalizedFactors n).filter (fun p => ¬ P p)
  have ht : t ⊆ normalizedFactors n := Multiset.filter_subset _ _
  have hu : u ⊆ normalizedFactors n := Multiset.filter_subset _ _
  have ht0 := prod_ne_zero_of_subset_normalizedFactors ht
  have hu0 := prod_ne_zero_of_subset_normalizedFactors hu
  have htf := normalizedFactors_prod_eq_self_of_subset ht
  have huf := normalizedFactors_prod_eq_self_of_subset hu
  refine ⟨t.prod, u.prod, ht0, hu0, ?_, ?_, ?_⟩
  · intro p hp
    change p ∈ (normalizedFactors t.prod).toFinset at hp
    rw [htf, Multiset.mem_toFinset] at hp
    exact (Multiset.mem_filter.mp hp).2
  · apply coprime_of_disjoint _ _ hu0 hJ
    rw [huf, Multiset.disjoint_left]
    intro p hp hpJ
    exact (Multiset.mem_filter.mp hp).2 (Multiset.mem_toFinset.mpr hpJ)
  · rw [← Multiset.prod_add, show t + u = normalizedFactors n from Multiset.filter_add_not P _,
      prod_factors n hn]

private theorem supported_filter (J h : Ideal (𝓞 F)) (hs : IdealSupportedOn h J) :
    (normalizedFactors h).filter (fun p => p ∈ idealPrimeSupport J) = normalizedFactors h := by
  apply Multiset.filter_eq_self.mpr
  intro p hp
  exact hs (Multiset.mem_toFinset.mpr hp)
private theorem exterior_filter (J a : Ideal (𝓞 F)) (hc : a ⊔ J = ⊤) :
    (normalizedFactors a).filter (fun p => p ∈ idealPrimeSupport J) = 0 := by
  apply Multiset.filter_eq_nil.mpr
  intro p hp hpJ
  exact Multiset.disjoint_left.mp (disjoint_of_coprime a J hc) hp
    (Multiset.mem_toFinset.mp hpJ)
private theorem split_h_eq (J n h a : Ideal (𝓞 F)) (hh : h ≠ ⊥) (ha : a ≠ ⊥)
    (hs : IdealSupportedOn h J) (hc : a ⊔ J = ⊤) (he : n = h * a) :
    h = ((normalizedFactors n).filter (fun p => p ∈ idealPrimeSupport J)).prod := by
  rw [he, normalizedFactors_mul hh ha, Multiset.filter_add,
    supported_filter J h hs, exterior_filter J a hc, add_zero, prod_factors h hh]

private theorem dyadic_exists (x : ℝ) (hx : 1 ≤ x) : ∃ k : ℕ, DyadicBand k x := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  have he : ∃ m : ℕ, x ≤ (2 : ℝ)^m := ⟨m, hm.le⟩
  refine ⟨Nat.find he, ?_⟩
  have hk := Nat.find_spec he
  unfold DyadicBand
  split_ifs with h
  · have : Nat.find he = 0 := h
    simpa [this] using le_antisymm (by simpa [this] using hk) hx
  · refine ⟨?_, hk⟩
    exact lt_of_not_ge (Nat.find_min he (by omega : Nat.find he - 1 < Nat.find he))
private theorem dyadic_unique (x : ℝ) (k l : ℕ)
    (hk : DyadicBand k x) (hl : DyadicBand l x) : k = l := by
  have upper (m : ℕ) (hm : DyadicBand m x) : x ≤ (2 : ℝ) ^ m := by
    unfold DyadicBand at hm
    split_ifs at hm with h
    · simp [h, hm]
    · exact hm.2
  have minimal (m j : ℕ) (hm : DyadicBand m x) (hj : j < m) : (2 : ℝ)^j < x := by
    unfold DyadicBand at hm
    split_ifs at hm with h
    · omega
    · exact lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : j ≤ m - 1)) hm.1
  apply le_antisymm
  · by_contra h
    exact (minimal k l hk (by omega)).not_ge (upper l hl)
  · by_contra h
    exact (minimal l k hl (by omega)).not_ge (upper k hk)
private theorem dyadic_upper (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (hk : DyadicBand k x) :
    (2 : ℝ)^k ≤ 2*x := by
  unfold DyadicBand at hk
  split_ifs at hk with h
  · simp [h]
    linarith
  · have he : k = k-1+1 := by omega
    rw [he, pow_succ]
    linarith [hk.1]

private theorem bad_factors (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    normalizedFactors (badIdeal Sf) = Sf.val.map HeightOneSpectrum.asIdeal := by
  change normalizedFactors (∏ v ∈ Sf, v.asIdeal) = _
  rw [Finset.prod_eq_multiset_prod]
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hp
  exact v.prime
private theorem supported_exponent_injective (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (fun h : SupportedIdeal Sf =>
      fun v : Sf => idealPrimeExponent v.val.asIdeal h.val.val) := by
  intro h g he
  have factors_eq : normalizedFactors h.val.val = normalizedFactors g.val.val := by
    apply Multiset.ext.mpr
    intro p
    by_cases hp : p ∈ idealPrimeSupport (badIdeal Sf)
    · rw [idealPrimeSupport, bad_factors, Multiset.mem_toFinset, Multiset.mem_map] at hp
      obtain ⟨v, hv, rfl⟩ := hp
      exact congrFun he ⟨v, hv⟩
    · have hh : p ∉ normalizedFactors h.val.val := fun hh => hp (h.property (Multiset.mem_toFinset.mpr hh))
      have hg : p ∉ normalizedFactors g.val.val := fun hg => hp (g.property (Multiset.mem_toFinset.mpr hg))
      simp [Multiset.count_eq_zero_of_notMem hh, Multiset.count_eq_zero_of_notMem hg]
  apply Subtype.ext
  apply Subtype.ext
  simpa only [prod_normalizedFactors_eq h.val.property, prod_normalizedFactors_eq g.val.property,
    normalize_eq] using congrArg Multiset.prod factors_eq
private theorem exponent_norm_bound (n p : Ideal (𝓞 F)) (hn : n ≠ ⊥) (hp : Prime p) :
    (2 : ℝ) ^ idealPrimeExponent p n ≤ idealNorm n := by
  have hd : p ^ idealPrimeExponent p n ∣ n := by
    have hle : Multiset.replicate ((normalizedFactors n).count p) p ≤ normalizedFactors n :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hprod := Multiset.prod_dvd_prod_of_le hle
    rw [Multiset.prod_replicate, prod_normalizedFactors_eq hn, normalize_eq] at hprod
    exact hprod
  have hn0 : Ideal.absNorm n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hn
  have hnorm : idealNorm (p ^ idealPrimeExponent p n) ≤ idealNorm n := by
    unfold idealNorm
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (map_dvd Ideal.absNorm hd)
  have hp2 := idealNorm_prime_ge_two p hp
  have hh : (2 : ℝ)^idealPrimeExponent p n ≤ idealNorm p ^ idealPrimeExponent p n :=
    pow_le_pow_left₀ (by norm_num) hp2 _
  apply hh.trans
  simpa only [idealNorm, map_pow, Nat.cast_pow] using hnorm

private theorem exponent_cutoff (n p : Ideal (𝓞 F)) (hn : n ≠ ⊥) (hp : Prime p)
    (X : ℝ) (hX : idealNorm n ≤ X) :
    (idealPrimeExponent p n : ℝ) ≤ Real.log X / Real.log 2 := by
  have hb := exponent_norm_bound n p hn hp
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [Real.log_pow] using
    Real.log_le_log (by positivity : (0 : ℝ) < 2^idealPrimeExponent p n) (hb.trans hX)
private theorem label_card_nat (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (L : Finset (SupportedIdeal Sf × ℕ)) (m : ℕ)
    (hs : ∀ l ∈ L, ∀ v : Sf, idealPrimeExponent v.val.asIdeal l.1.val.val ≤ m)
    (hk : ∀ l ∈ L, l.2 ≤ m) : L.card ≤ (m+1)^(Sf.card+1) := by
  let f : {l // l ∈ L} → (Sf → Fin (m+1)) × Fin (m+1) := fun l =>
    (fun v => ⟨idealPrimeExponent v.val.asIdeal l.val.1.val.val,
      Nat.lt_succ_iff.mpr (hs l.val l.property v)⟩,
      ⟨l.val.2, Nat.lt_succ_iff.mpr (hk l.val l.property)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · apply supported_exponent_injective Sf
      funext v
      exact congrArg Fin.val (congrFun (congrArg Prod.fst hab) v)
    · exact congrArg Fin.val (congrArg Prod.snd hab)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    pow_succ] using hc

private theorem finite_norm_set (N : ℝ) :
    {n : NonzeroIdeal F | idealNorm n.val ≤ N}.Finite := by
  have h := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).preimage
    (show Set.InjOn (fun n : NonzeroIdeal F => n.val) _ from
      Subtype.val_injective.injOn)
  apply h.subset
  intro n hn
  exact Nat.le_floor hn

private theorem label_card_real (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (L : Finset (SupportedIdeal Sf × ℕ)) (N : ℝ) (hN : 2 ≤ N)
    (hs : ∀ l ∈ L, idealNorm l.1.val.val ≤ N)
    (hk : ∀ l ∈ L, (2 : ℝ)^l.2 ≤ 2*N) :
    (L.card : ℝ) ≤ (2 + 1 / Real.log 2) ^ (Sf.card+1) *
      (1 + Real.log N) ^ (Sf.card+1) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  let m := ⌊Real.log (2*N) / Real.log 2⌋₊
  have hr : Real.log (2*N) / Real.log 2 = 1 + Real.log N / Real.log 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hN0)]
    field_simp
  have hc : L.card ≤ (m+1)^(Sf.card+1) := by
    apply label_card_nat Sf L m
    · intro l hl v
      apply Nat.le_floor
      apply (exponent_cutoff _ _ l.1.val.property v.val.prime N (hs l hl)).trans
      rw [hr]
      linarith
    · intro l hl
      apply Nat.le_floor
      apply (le_div_iff₀ h2).mpr
      simpa only [Real.log_pow] using
        Real.log_le_log (by positivity : (0 : ℝ) < 2^l.2) (hk l hl)
  have hm : (m+1 : ℕ) ≤ (2 + 1 / Real.log 2) * (1 + Real.log N) := by
    have hh : (m : ℝ) ≤ Real.log (2*N) / Real.log 2 :=
      Nat.floor_le (by rw [hr]; positivity)
    rw [hr, div_eq_mul_inv] at hh
    have hp : 0 ≤ 1 / Real.log 2 := le_of_lt (one_div_pos.mpr h2)
    have hmul : 0 ≤ (1 / Real.log 2) * Real.log N := mul_nonneg hp hlog
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [m] at *
    simp only [one_div] at *
    nlinarith
  calc
    (L.card : ℝ) ≤ ((m+1 : ℕ) : ℝ)^(Sf.card+1) := by exact_mod_cast hc
    _ ≤ ((2 + 1 / Real.log 2) * (1 + Real.log N))^(Sf.card+1) :=
      pow_le_pow_left₀ (by positivity) hm _
    _ = _ := by rw [mul_pow]

theorem factor_unique (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (n : NonzeroIdeal F) :
    ∃! ha : SupportedIdeal Sf × Exterior Sf,
      n.val = ha.1.val.val * ha.2.val ∧
        idealNorm n.val = idealNorm ha.1.val.val * idealNorm ha.2.val := by
  have hJ : badIdeal Sf ≠ (⊥ : Ideal (𝓞 F)) := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact v.ne_bot
  obtain ⟨h, a, hh, ha, hs, hc, he⟩ := split_exists (badIdeal Sf) n.val hJ n.property
  let h' : SupportedIdeal Sf := ⟨⟨h, hh⟩, hs⟩
  let a' : Exterior Sf := ⟨a, ha, hc⟩
  refine ⟨(h', a'), ⟨he, ?_⟩, ?_⟩
  · simp only [he, idealNorm, map_mul, Nat.cast_mul]
    rfl
  · intro b hb
    have eh : b.1.val.val = h := by
      rw [split_h_eq (badIdeal Sf) n.val b.1.val.val b.2.val b.1.val.property
        b.2.property.1 b.1.property b.2.property.2 hb.1,
        ← split_h_eq (badIdeal Sf) n.val h a hh ha hs hc he]
    have ea : b.2.val = a := by
      apply mul_left_cancel₀ hh
      exact (by simpa only [eh] using hb.1.symm.trans he)
    apply Prod.ext
    · exact Subtype.ext (Subtype.ext eh)
    · exact Subtype.ext ea

theorem mul_exterior_injective (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (h : SupportedIdeal Sf) :
    Function.Injective (fun a : Exterior Sf => h.val.val * a.val) := by
  intro a b hab
  apply Subtype.ext
  exact mul_left_cancel₀ h.val.property hab

theorem finite_dyadic_partition
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 2 ≤ N →
      ∃ (T : Finset (NonzeroIdeal F))
        (L : Finset (SupportedIdeal Sf × ℕ))
        (B : (SupportedIdeal Sf × ℕ) → Finset (NonzeroIdeal F)),
        (∀ n : NonzeroIdeal F, n ∈ T ↔ idealNorm n.val ≤ N) ∧
        (∀ l ∈ L, (B l).Nonempty ∧
          idealNorm l.1.val.val ≤ N ∧ (2 : ℝ) ^ l.2 ≤ 2 * N) ∧
        (∀ l ∈ L, ∀ n : NonzeroIdeal F, n ∈ B l ↔
          n ∈ T ∧ ∃ a : Exterior Sf,
            n.val = l.1.val.val * a.val ∧ DyadicBand l.2 (idealNorm a.val)) ∧
        (∀ n ∈ T, ∃! l : {l // l ∈ L}, n ∈ B l.val) ∧
        (L.card : ℝ) ≤ D * (1 + Real.log N) ^ (Sf.card + 1) ∧
        (∀ b : NonzeroIdeal F → ℂ,
          (∑ l ∈ L, ∑ n ∈ B l, ‖b n‖ ^ 2) =
            ∑ n ∈ T, ‖b n‖ ^ 2) := by
  classical
  refine ⟨(2 + 1 / Real.log 2) ^ (Sf.card+1), by positivity, ?_⟩
  intro N hN
  have hf : ∀ n : NonzeroIdeal F, ∃ ha : SupportedIdeal Sf × Exterior Sf,
      n.val = ha.1.val.val * ha.2.val ∧
      idealNorm n.val = idealNorm ha.1.val.val * idealNorm ha.2.val :=
    fun n => (factor_unique Sf n).exists
  choose ha hha using hf
  have hb : ∀ n : NonzeroIdeal F, ∃ k : ℕ, DyadicBand k (idealNorm (ha n).2.val) :=
    fun n => dyadic_exists _ (idealNorm_ge_one _ (ha n).2.property.1)
  choose k hk using hb
  let label : NonzeroIdeal F → SupportedIdeal Sf × ℕ := fun n => ((ha n).1, k n)
  have hlabel (n : NonzeroIdeal F) (l : SupportedIdeal Sf × ℕ) :
      label n = l ↔ ∃ a : Exterior Sf,
        n.val = l.1.val.val * a.val ∧ DyadicBand l.2 (idealNorm a.val) := by
    constructor
    · intro he
      obtain rfl := he.symm
      exact ⟨(ha n).2, (hha n).1, hk n⟩
    · rintro ⟨a, he, hband⟩
      have heNorm : idealNorm n.val = idealNorm l.1.val.val * idealNorm a.val := by
        simp only [he, idealNorm, map_mul, Nat.cast_mul]
      have hh : ha n = (l.1, a) := (factor_unique Sf n).unique (hha n) ⟨he, heNorm⟩
      apply Prod.ext
      · exact congrArg (fun p : SupportedIdeal Sf × Exterior Sf => p.1) hh
      · apply dyadic_unique (idealNorm a.val)
        · simpa only [hh] using hk n
        · exact hband
  let T := (finite_norm_set (F := F) N).toFinset
  let L := T.image label
  let B : (SupportedIdeal Sf × ℕ) → Finset (NonzeroIdeal F) :=
    fun l => T.filter (fun n => label n = l)
  have hT (n : NonzeroIdeal F) : n ∈ T ↔ idealNorm n.val ≤ N :=
    Set.Finite.mem_toFinset _
  have hL (n : NonzeroIdeal F) (hn : n ∈ T) : label n ∈ L :=
    Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hB (n : NonzeroIdeal F) (l : SupportedIdeal Sf × ℕ) :
      n ∈ B l ↔ n ∈ T ∧ label n = l := Finset.mem_filter
  have hbounds (l : SupportedIdeal Sf × ℕ) (hl : l ∈ L) :
      (B l).Nonempty ∧ idealNorm l.1.val.val ≤ N ∧ (2 : ℝ)^l.2 ≤ 2*N := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hl
    have hnN := (hT n).mp hn
    have hh1 := idealNorm_ge_one _ (ha n).1.val.property
    have ha1 := idealNorm_ge_one _ (ha n).2.property.1
    have hhN : idealNorm (ha n).1.val.val ≤ N := by
      nlinarith [(hha n).2]
    have haN : idealNorm (ha n).2.val ≤ N := by
      nlinarith [(hha n).2]
    exact ⟨⟨n, (hB n _).mpr ⟨hn, rfl⟩⟩, hhN,
      (dyadic_upper _ ha1 _ (hk n)).trans (by linarith)⟩
  refine ⟨T, L, B, hT, hbounds, ?_, ?_, ?_, ?_⟩
  · intro l hl n
    rw [hB, hlabel]
  · intro n hn
    refine ⟨⟨label n, hL n hn⟩, (hB n _).mpr ⟨hn, rfl⟩, ?_⟩
    intro l hl
    apply Subtype.ext
    exact ((hB n l.val).mp hl).2.symm
  · exact label_card_real Sf L N hN (fun l hl => (hbounds l hl).2.1)
      (fun l hl => (hbounds l hl).2.2)
  · intro b
    exact Finset.sum_fiberwise_of_maps_to hL (fun n => ‖b n‖^2)

end
end DedekindZetaZeroFree.Detector.SSupportedPartition
