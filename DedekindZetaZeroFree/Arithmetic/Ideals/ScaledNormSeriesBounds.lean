module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.PoissonTruncation

open scoped NumberField Classical

private lemma one_le_absNorm_cast {F : Type*} [Field F] [NumberField F]
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  have h : Ideal.absNorm I ≠ 0 := fun h0 => hI (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

private lemma norm_le_majorant {F : Type*} [Field F] [NumberField F]
    {B K u : ℝ} (hu : 0 < u) {φ : ℝ → ℂ}
    (hφ : ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B)) (I : Ideal (𝓞 F)) :
    ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖ ≤
      K * u ^ (-B) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B)) := by
  by_cases hI : I = ⊥
  · simp [hI]
  · rw [if_neg hI, if_neg hI]
    have hn : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := one_le_absNorm_cast hI
    have hn0 : 0 ≤ (Ideal.absNorm I : ℝ) := le_trans zero_le_one hn
    have hpos : 0 < u * (Ideal.absNorm I : ℝ) := mul_pos hu (lt_of_lt_of_le zero_lt_one hn)
    calc ‖φ (u * (Ideal.absNorm I : ℝ))‖
        ≤ K * (u * (Ideal.absNorm I : ℝ)) ^ (-B) := hφ _ hpos
      _ = K * (u ^ (-B) * (Ideal.absNorm I : ℝ) ^ (-B)) := by rw [Real.mul_rpow hu.le hn0]
      _ = K * u ^ (-B) * (Ideal.absNorm I : ℝ) ^ (-B) := by ring

private lemma norm_le_tail_majorant {F : Type*} [Field F] [NumberField F]
    {B K u R : ℝ} (hu : 0 < u) {φ : ℝ → ℂ}
    (hφ : ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B)) (I : Ideal (𝓞 F)) :
    ‖if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) then φ (u * (Ideal.absNorm I : ℝ)) else 0‖ ≤
      K * u ^ (-B) *
        (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) then (Ideal.absNorm I : ℝ) ^ (-B) else 0) := by
  by_cases h : I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
  · rw [if_pos h, if_pos h]
    have hn : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := one_le_absNorm_cast h.1
    have hn0 : 0 ≤ (Ideal.absNorm I : ℝ) := le_trans zero_le_one hn
    have hpos : 0 < u * (Ideal.absNorm I : ℝ) := mul_pos hu (lt_of_lt_of_le zero_lt_one hn)
    calc ‖φ (u * (Ideal.absNorm I : ℝ))‖
        ≤ K * (u * (Ideal.absNorm I : ℝ)) ^ (-B) := hφ _ hpos
      _ = K * (u ^ (-B) * (Ideal.absNorm I : ℝ) ^ (-B)) := by rw [Real.mul_rpow hu.le hn0]
      _ = K * u ^ (-B) * (Ideal.absNorm I : ℝ) ^ (-B) := by ring
  · simp [h]

private lemma tail_norm_eq_norm_tail {F : Type*} [Field F] [NumberField F]
    {u R : ℝ} (φ : ℝ → ℂ) (I : Ideal (𝓞 F)) :
    (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0) =
    ‖if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) then φ (u * (Ideal.absNorm I : ℝ)) else 0‖ := by
  by_cases h : I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) <;> simp [h]

private lemma summable_inverse_power_tail {F : Type*} [Field F] [NumberField F]
    (B : ℝ) (hB : 1 < B) (R : ℝ) :
    Summable (fun I : Ideal (𝓞 F) =>
      if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) then (Ideal.absNorm I : ℝ) ^ (-B) else 0) := by
  refine Summable.of_nonneg_of_le (fun I => ?_) (fun I => ?_)
    (DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F B hB)
  · by_cases h : I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
    · rw [if_pos h]; positivity
    · simp [h]
  · by_cases h : I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
    · rw [if_pos h]
      simp [h.1]
    · rw [if_neg h]
      by_cases hbot : I = ⊥
      · simp [hbot]
      · rw [if_neg hbot]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem scaled_ideal_series_summable (F : Type*) [Field F] [NumberField F]
    (B : ℝ) (hB : 1 < B) (K : ℝ) (hK : 0 ≤ K) (φ : ℝ → ℂ)
    (hφ : ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B))
    (u : ℝ) (hu : 0 < u) :
    Summable (fun I : Ideal (𝓞 F) =>
      ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖) ∧
    Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))) := by
  have hmaj : Summable (fun I : Ideal (𝓞 F) =>
      K * u ^ (-B) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) :=
    (DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F B hB).mul_left (K * u ^ (-B))
  exact ⟨Summable.of_nonneg_of_le (fun I => norm_nonneg _)
      (fun I => norm_le_majorant hu hφ I) hmaj,
    Summable.of_norm_bounded hmaj (fun I => norm_le_majorant hu hφ I)⟩

theorem scaled_ideal_tail_summable (F : Type*) [Field F] [NumberField F]
    (B : ℝ) (hB : 1 < B) (K : ℝ) (hK : 0 ≤ K) (φ : ℝ → ℂ)
    (hφ : ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B))
    (u : ℝ) (hu : 0 < u) (R : ℝ) :
    Summable (fun I : Ideal (𝓞 F) =>
      if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
      then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0) ∧
    Summable (fun I : Ideal (𝓞 F) =>
      if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
      then φ (u * (Ideal.absNorm I : ℝ)) else 0) := by
  have hmaj : Summable (fun I : Ideal (𝓞 F) =>
      K * u ^ (-B) *
        (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
         then (Ideal.absNorm I : ℝ) ^ (-B) else 0)) :=
    (summable_inverse_power_tail B hB R).mul_left (K * u ^ (-B))
  exact ⟨Summable.of_nonneg_of_le
      (fun I => by by_cases h : I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ) <;> simp [h])
      (fun I => by rw [tail_norm_eq_norm_tail φ I]; exact norm_le_tail_majorant hu hφ I) hmaj,
    Summable.of_norm_bounded hmaj (fun I => norm_le_tail_majorant hu hφ I)⟩

theorem scaled_ideal_series_split (F : Type*) [Field F] [NumberField F]
    (B : ℝ) (hB : 1 < B) (K : ℝ) (hK : 0 ≤ K) (φ : ℝ → ℂ)
    (hφ : ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B))
    (u : ℝ) (hu : 0 < u) (R : ℝ) :
    (∑' I : Ideal (𝓞 F),
      if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))) =
      (∑ I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F R).filter (fun I => I ≠ ⊥),
        φ (u * (Ideal.absNorm I : ℝ))) +
      ∑' I : Ideal (𝓞 F),
        if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
        then φ (u * (Ideal.absNorm I : ℝ)) else 0 := by
  set A : Finset (Ideal (𝓞 F)) := (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F R).filter (fun I => I ≠ ⊥) with hA
  let f : Ideal (𝓞 F) → ℂ :=
    fun I => if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))
  let g : Ideal (𝓞 F) → ℂ := fun I => if I ∈ A then f I else 0
  let h : Ideal (𝓞 F) → ℂ := fun I => if I ∈ A then 0 else f I
  have hsumm : Summable f :=
    (scaled_ideal_series_summable F B hB K hK φ hφ u hu).2
  have hg : Summable g := by
    refine summable_of_ne_finset_zero (s := A) (fun I hI => ?_)
    simp [g, hI]
  have hh : Summable h := by
    have heq : h = fun I => f I - g I := by
      funext I; by_cases hI : I ∈ A <;> simp [h, g, hI]
    rw [heq]; exact hsumm.sub hg
  have hfgh : f = fun I => g I + h I := by
    funext I; by_cases hI : I ∈ A <;> simp [g, h, hI]
  have key : (∑' I : Ideal (𝓞 F), f I) =
      (∑' I : Ideal (𝓞 F), g I) + ∑' I : Ideal (𝓞 F), h I := by
    rw [tsum_congr (fun I => congrFun hfgh I), hg.tsum_add hh]
  rw [key]
  congr 1
  · rw [tsum_eq_sum (s := A) (fun I hI => by simp [g, hI])]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    have hne : I ≠ ⊥ := by
      have h2 := hI; rw [hA] at h2
      exact (Finset.mem_filter.mp h2).2
    simp [g, hI, f, hne]
  · refine tsum_congr (fun I => ?_)
    by_cases hI : I ∈ A
    · have hh0 : h I = 0 := by simp [h, hI]
      rw [hh0]
      have hle : (Ideal.absNorm I : ℝ) ≤ R := by
        have h2 := hI; rw [hA] at h2
        exact DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mp (Finset.mem_filter.mp h2).1
      have hnot : ¬ (I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)) := by
        rintro ⟨-, hlt⟩; exact absurd hlt (not_lt.mpr hle)
      simp [hnot]
    · have hh1 : h I = f I := by simp [h, hI]
      rw [hh1]
      by_cases hbot : I = ⊥
      · subst hbot; simp [f]
      · have hlt : R < (Ideal.absNorm I : ℝ) := by
          by_contra hcon
          exact hI (by
            rw [hA]
            exact Finset.mem_filter.mpr
              ⟨DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr (le_of_not_gt hcon), hbot⟩)
        simp [f, hbot, hlt]

theorem exists_scaled_ideal_series_tail_bound
    (F : Type*) [Field F] [NumberField F] (B : ℝ) (hB : 1 < B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K : ℝ), 0 ≤ K → ∀ (φ : ℝ → ℂ),
        (∀ t : ℝ, 0 < t → ‖φ t‖ ≤ K * t ^ (-B)) →
        ∀ (u : ℝ), 0 < u →
          Summable (fun I : Ideal (𝓞 F) =>
            ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖) ∧
          Summable (fun I : Ideal (𝓞 F) =>
            if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))) ∧
          (∑' I : Ideal (𝓞 F),
            ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖) ≤
              C * K * u ^ (-B) ∧
          ∀ (R : ℝ), 1 ≤ R →
            Summable (fun I : Ideal (𝓞 F) =>
              if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
              then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0) ∧
            Summable (fun I : Ideal (𝓞 F) =>
              if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
              then φ (u * (Ideal.absNorm I : ℝ)) else 0) ∧
            (∑' I : Ideal (𝓞 F),
              if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
              then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0) ≤
                C * K * u ^ (-B) * R ^ (1 - B) ∧
            (∑' I : Ideal (𝓞 F),
              if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))) =
              (∑ I ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F R).filter (fun I => I ≠ ⊥),
                φ (u * (Ideal.absNorm I : ℝ))) +
              ∑' I : Ideal (𝓞 F),
                if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
                then φ (u * (Ideal.absNorm I : ℝ)) else 0 := by
  obtain ⟨B0, hB0nn, hB0bd⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_inverse_power_tail_bound F B hB
  have hfull : Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B)) :=
    DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F B hB
  refine ⟨max (∑' I : Ideal (𝓞 F),
      (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0, ?_, ?_⟩
  · exact le_max_of_le_left
      (tsum_nonneg (fun I => by
        by_cases h : I = ⊥
        · simp [h]
        · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro K hK φ hφ u hu
    have hKup : 0 ≤ K * u ^ (-B) := mul_nonneg hK (Real.rpow_nonneg hu.le (-B))
    have hmaj : Summable (fun I : Ideal (𝓞 F) =>
        K * u ^ (-B) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) :=
      hfull.mul_left (K * u ^ (-B))
    have hmain := scaled_ideal_series_summable F B hB K hK φ hφ u hu
    refine ⟨hmain.1, hmain.2, ?_, ?_⟩
    · have h1 : (∑' I : Ideal (𝓞 F),
            ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖)
          ≤ ∑' I : Ideal (𝓞 F),
              K * u ^ (-B) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B)) :=
        Summable.tsum_le_tsum (fun I => norm_le_majorant hu hφ I) hmain.1 hmaj
      have h2 : (∑' I : Ideal (𝓞 F),
              K * u ^ (-B) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B)))
          = (K * u ^ (-B)) * (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) :=
        tsum_mul_left
      rw [h2] at h1
      have hCK : (∑' I : Ideal (𝓞 F),
            (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B)))
          ≤ max (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 :=
        le_max_left _ _
      calc (∑' I : Ideal (𝓞 F),
              ‖if I = ⊥ then (0 : ℂ) else φ (u * (Ideal.absNorm I : ℝ))‖)
          ≤ (K * u ^ (-B)) * (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) := h1
        _ ≤ (K * u ^ (-B)) * max (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 :=
              mul_le_mul_of_nonneg_left hCK hKup
        _ = max (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 *
              K * u ^ (-B) := by ring
    · intro R hR
      have hR0 : 0 ≤ R := by linarith
      have hRpow : 0 ≤ R ^ (1 - B) := Real.rpow_nonneg hR0 _
      have htail := scaled_ideal_tail_summable F B hB K hK φ hφ u hu R
      have hmajT : Summable (fun I : Ideal (𝓞 F) =>
          K * u ^ (-B) * (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
            then (Ideal.absNorm I : ℝ) ^ (-B) else 0)) :=
        (summable_inverse_power_tail B hB R).mul_left (K * u ^ (-B))
      refine ⟨htail.1, htail.2, ?_,
        scaled_ideal_series_split F B hB K hK φ hφ u hu R⟩
      have h1 : (∑' I : Ideal (𝓞 F),
            (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
             then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0))
          ≤ ∑' I : Ideal (𝓞 F),
              K * u ^ (-B) * (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
                then (Ideal.absNorm I : ℝ) ^ (-B) else 0) :=
        Summable.tsum_le_tsum
          (fun I => by rw [tail_norm_eq_norm_tail φ I]; exact norm_le_tail_majorant hu hφ I)
          htail.1 hmajT
      have h2 : (∑' I : Ideal (𝓞 F),
              K * u ^ (-B) * (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
                then (Ideal.absNorm I : ℝ) ^ (-B) else 0))
          = (K * u ^ (-B)) * (∑' I : Ideal (𝓞 F),
              (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
               then (Ideal.absNorm I : ℝ) ^ (-B) else 0)) :=
        tsum_mul_left
      rw [h2] at h1
      have hb := hB0bd R hR
      have hB0C : B0 ≤ max (∑' I : Ideal (𝓞 F),
          (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 := le_max_right _ _
      calc (∑' I : Ideal (𝓞 F),
              (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
               then ‖φ (u * (Ideal.absNorm I : ℝ))‖ else 0))
          ≤ (K * u ^ (-B)) * (∑' I : Ideal (𝓞 F),
              (if I ≠ ⊥ ∧ R < (Ideal.absNorm I : ℝ)
               then (Ideal.absNorm I : ℝ) ^ (-B) else 0)) := h1
        _ ≤ (K * u ^ (-B)) * (B0 * R ^ (1 - B)) := mul_le_mul_of_nonneg_left hb hKup
        _ = (K * u ^ (-B) * R ^ (1 - B)) * B0 := by ring
        _ ≤ (K * u ^ (-B) * R ^ (1 - B)) * max (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 :=
              mul_le_mul_of_nonneg_left hB0C (mul_nonneg hKup hRpow)
        _ = max (∑' I : Ideal (𝓞 F),
              (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-B))) B0 *
              K * u ^ (-B) * R ^ (1 - B) := by ring

end DedekindZetaZeroFree.LargeSieve.PoissonTruncation
