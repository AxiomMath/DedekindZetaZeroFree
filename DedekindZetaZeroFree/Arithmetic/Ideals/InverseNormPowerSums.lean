module

public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
public import DedekindZetaZeroFree.Analysis.DyadicInitialPowerSums
public import DedekindZetaZeroFree.Analysis.DyadicTailPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

private lemma one_le_absNorm_coe {F : Type*} [Field F] [NumberField F] {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h0)

noncomputable def idealW (F : Type*) [Field F] [NumberField F] (I : Ideal (𝓞 F)) : ℝ :=
  max 1 (Ideal.absNorm I : ℝ)

private lemma one_le_idealW {F : Type*} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    1 ≤ idealW F I := le_max_left _ _

private lemma absNorm_le_idealW {F : Type*} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    (Ideal.absNorm I : ℝ) ≤ idealW F I := le_max_right _ _

private lemma idealW_eq {F : Type*} [Field F] [NumberField F] {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    idealW F I = (Ideal.absNorm I : ℝ) := max_eq_right (one_le_absNorm_coe hI)

private lemma idealW_lt_imp {F : Type*} [Field F] [NumberField F] {X : ℝ} (hX : 1 ≤ X)
    {I : Ideal (𝓞 F)} (h : X < idealW F I) :
    I ≠ ⊥ ∧ X < (Ideal.absNorm I : ℝ) ∧ idealW F I = (Ideal.absNorm I : ℝ) := by
  have hgt : 1 < idealW F I := lt_of_le_of_lt hX h
  have ha : (1 : ℝ) < (Ideal.absNorm I : ℝ) := by
    by_contra hle
    push Not at hle
    rw [show idealW F I = 1 from max_eq_left hle] at hgt
    exact absurd hgt (lt_irrefl 1)
  have hw : idealW F I = (Ideal.absNorm I : ℝ) := max_eq_right (le_of_lt ha)
  have hne : I ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot] at ha
    norm_num at ha
  exact ⟨hne, by rw [hw] at h; exact h, hw⟩

private lemma ite_absNorm_eq_ite_idealW {F : Type*} [Field F] [NumberField F] (p X : ℝ)
    (hX : 1 ≤ X) (I : Ideal (𝓞 F)) :
    (if I ≠ ⊥ ∧ X < (Ideal.absNorm I : ℝ) then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
      = (if X < idealW F I then idealW F I ^ (-p) else 0) := by
  by_cases h : X < idealW F I
  · obtain ⟨hne, hlt, hw⟩ := idealW_lt_imp hX h
    rw [if_pos h, if_pos ⟨hne, hlt⟩, hw]
  · rw [if_neg h]
    exact if_neg (fun hc => h (by rw [idealW_eq hc.1]; exact hc.2))

private lemma ite_absNorm_le_ite_idealW {F : Type*} [Field F] [NumberField F] (p X : ℝ)
    (hX : 1 ≤ X) (P : Ideal (𝓞 F) → Prop) (I : Ideal (𝓞 F)) :
    (if I ≠ ⊥ ∧ P I ∧ X < (Ideal.absNorm I : ℝ) then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
      ≤ (if X < idealW F I then idealW F I ^ (-p) else 0) := by
  by_cases h : X < idealW F I
  · obtain ⟨hne, hlt, hw⟩ := idealW_lt_imp hX h
    rw [if_pos h, hw]
    split_ifs with hc
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · rw [if_neg h]
    rw [if_neg (fun hc => h (by rw [idealW_eq hc.1]; exact hc.2.2))]

private lemma exists_count_bound_idealW {F : Type*} [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset (Ideal (𝓞 F)),
      (∀ I ∈ s, idealW F I ≤ Y) → (s.card : ℝ) ≤ C * Y := by
  obtain ⟨C, hC, -, hfin⟩ := exists_ideal_count_bound_finset F
  exact ⟨C, hC, fun Y hY s hs => hfin Y hY s fun I hI => le_trans (absNorm_le_idealW I) (hs I hI)⟩

private lemma tail_finset_sum_le {F : Type*} [Field F] [NumberField F] (p : ℝ) (hp : 1 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 1 ≤ X → ∀ u : Finset (Ideal (𝓞 F)),
      ∑ I ∈ u, (if X < idealW F I then idealW F I ^ (-p) else 0) ≤ B * X ^ (1 - p) := by
  obtain ⟨C, hC1, hcount⟩ := exists_count_bound_idealW (F := F)
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  have hden : 0 < 1 - (2 : ℝ) ^ (1 - p) := by
    have h2 : (2 : ℝ) ^ (1 - p) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  refine ⟨2 * C / (1 - (2 : ℝ) ^ (1 - p)), div_nonneg (by linarith) (le_of_lt hden), ?_⟩
  intro X hX u
  have h := Vendor.inversePower_tail_sum_le (w := idealW F) (fun I => one_le_idealW I) C hC hcount
    p hp X hX (u.filter (fun I => X < idealW F I)) (fun I hI => (Finset.mem_filter.mp hI).2)
  rwa [Finset.sum_filter] at h

theorem summable_ideal_inverse_power (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-p)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨C, hC1, hcount⟩ := exists_count_bound_idealW (F := F)
  obtain ⟨B, hB0, hB⟩ := tail_finset_sum_le (F := F) p hp

  have hzero : (fun I : Ideal (𝓞 F) => if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-p))
      = fun I => (Ideal.absNorm I : ℝ) ^ (-p) := by
    funext I
    by_cases h : I = ⊥
    · rw [if_pos h, h, Ideal.absNorm_bot, Nat.cast_zero,
        Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hp0))]
    · rw [if_neg h]
  rw [hzero]

  have hsplit : (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-p))
      = (fun I => if idealW F I ≤ 1 then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
        + (fun I => if 1 < idealW F I then (Ideal.absNorm I : ℝ) ^ (-p) else 0) := by
    funext I
    by_cases hI : idealW F I ≤ 1
    · have h2 : ¬ 1 < idealW F I := not_lt.mpr hI
      simp only [Pi.add_apply, if_pos hI, if_neg h2, add_zero]
    · have h2 : 1 < idealW F I := lt_of_not_ge hI
      simp only [Pi.add_apply, if_neg hI, if_pos h2, zero_add]
  rw [hsplit]
  have hterm : ∀ I : Ideal (𝓞 F), (Ideal.absNorm I : ℝ) ^ (-p) ≤ 1 := by
    intro I
    rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hp0))]
      norm_num
    · have h1 : (1 : ℕ) ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hpos)
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h1) (by linarith)
  refine Summable.add ?hg1 ?hg2
  ·
    have hnonneg : 0 ≤ (fun I => if idealW F I ≤ 1 then (Ideal.absNorm I : ℝ) ^ (-p) else 0) := by
      intro I
      change (0 : ℝ) ≤ (if idealW F I ≤ 1 then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
      split_ifs with h
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    have hbound : ∀ u : Finset (Ideal (𝓞 F)),
        ∑ I ∈ u, (if idealW F I ≤ 1 then (Ideal.absNorm I : ℝ) ^ (-p) else 0) ≤ C := by
      intro u
      rw [← Finset.sum_filter (s := u) (p := fun I => idealW F I ≤ 1)
        (f := fun I => (Ideal.absNorm I : ℝ) ^ (-p))]
      have hcard : ((u.filter (fun I => idealW F I ≤ 1)).card : ℝ) ≤ C := by
        simpa using hcount 1 le_rfl (u.filter (fun I => idealW F I ≤ 1))
          (fun I hI => (Finset.mem_filter.mp hI).2)
      calc ∑ I ∈ u.filter (fun I => idealW F I ≤ 1), (Ideal.absNorm I : ℝ) ^ (-p)
          ≤ ∑ I ∈ u.filter (fun I => idealW F I ≤ 1), (1 : ℝ) :=
            Finset.sum_le_sum (fun I _ => hterm I)
        _ = ((u.filter (fun I => idealW F I ≤ 1)).card : ℝ) := by simp
        _ ≤ C := hcard
    exact summable_of_sum_le hnonneg hbound
  ·
    have hnonneg : 0 ≤ (fun I => if 1 < idealW F I then (Ideal.absNorm I : ℝ) ^ (-p) else 0) := by
      intro I
      change (0 : ℝ) ≤ (if 1 < idealW F I then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
      split_ifs with h
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    have hbound : ∀ u : Finset (Ideal (𝓞 F)),
        ∑ I ∈ u, (if 1 < idealW F I then (Ideal.absNorm I : ℝ) ^ (-p) else 0) ≤ B := by
      intro u
      have hcongr : ∑ I ∈ u, (if 1 < idealW F I then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
          = ∑ I ∈ u, (if 1 < idealW F I then idealW F I ^ (-p) else 0) := by
        refine Finset.sum_congr rfl (fun I _ => ?_)
        by_cases hI : 1 < idealW F I
        · rw [if_pos hI, if_pos hI, idealW_eq (idealW_lt_imp le_rfl hI).1]
        · rw [if_neg hI, if_neg hI]
      rw [hcongr]
      simpa using hB 1 le_rfl u
    exact summable_of_sum_le hnonneg hbound

theorem exists_ideal_inverse_power_tail_bound (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp : 1 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 1 ≤ X →
      (∑' I : Ideal (𝓞 F),
        if I ≠ ⊥ ∧ X < (Ideal.absNorm I : ℝ)
        then (Ideal.absNorm I : ℝ) ^ (-p) else 0) ≤ B * X ^ (1 - p) := by
  obtain ⟨B, hB0, hB⟩ := tail_finset_sum_le (F := F) p hp
  refine ⟨B, hB0, fun X hX => ?_⟩
  refine Real.tsum_le_of_sum_le ?_ (fun u => ?_)
  · intro I
    change (0 : ℝ) ≤ (if I ≠ ⊥ ∧ X < (Ideal.absNorm I : ℝ)
      then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
    split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl
  · refine le_trans (Finset.sum_le_sum (fun I _ => ?_)) (hB X hX u)
    exact le_of_eq (ite_absNorm_eq_ite_idealW p X hX I)

theorem exists_ideal_inverse_power_initial_bound (F : Type*) [Field F] [NumberField F]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ I ∈ (boundedNormIdeals F X).filter (fun I => I ≠ ⊥),
        (Ideal.absNorm I : ℝ) ^ (-p)) ≤ B * X ^ (1 - p) := by
  obtain ⟨C, hC1, hcount⟩ := exists_count_bound_idealW (F := F)
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  have hden : 0 < 1 - (2 : ℝ) ^ (p - 1) := by
    have h2 : (2 : ℝ) ^ (p - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  refine ⟨(2 : ℝ) ^ p * C / (1 - (2 : ℝ) ^ (p - 1)),
    div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) p) hC) (le_of_lt hden), fun X hX => ?_⟩
  have hs : ∀ I ∈ (boundedNormIdeals F X).filter (fun I => I ≠ ⊥), idealW F I ≤ X := by
    intro I hI
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hI
    rw [idealW_eq h2]
    exact mem_boundedNormIdeals.mp h1
  have h := Vendor.inversePower_initial_sum_le (w := idealW F) (fun I => one_le_idealW I) C hC hcount
    p hp0 hp1 X hX ((boundedNormIdeals F X).filter (fun I => I ≠ ⊥)) hs
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun I hI => ?_)
  rw [idealW_eq (Finset.mem_filter.mp hI).2]

theorem exists_filtered_ideal_inverse_power_tail_bound
    (F : Type*) [Field F] [NumberField F] (p : ℝ) (hp : 1 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X : ℝ) (P : Ideal (𝓞 F) → Prop), 1 ≤ X →
      (∑' I : Ideal (𝓞 F),
        if I ≠ ⊥ ∧ P I ∧ X < (Ideal.absNorm I : ℝ)
        then (Ideal.absNorm I : ℝ) ^ (-p) else 0) ≤ B * X ^ (1 - p) := by
  obtain ⟨B, hB0, hB⟩ := tail_finset_sum_le (F := F) p hp
  refine ⟨B, hB0, fun X P hX => ?_⟩
  refine Real.tsum_le_of_sum_le ?_ (fun u => ?_)
  · intro I
    change (0 : ℝ) ≤ (if I ≠ ⊥ ∧ P I ∧ X < (Ideal.absNorm I : ℝ)
      then (Ideal.absNorm I : ℝ) ^ (-p) else 0)
    split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl
  · refine le_trans (Finset.sum_le_sum (fun I _ => ite_absNorm_le_ite_idealW p X hX P I))
      (hB X hX u)

end DedekindZetaZeroFree.LargeSieve
