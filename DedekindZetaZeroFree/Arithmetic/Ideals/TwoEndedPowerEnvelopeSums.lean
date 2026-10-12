module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma absNorm_pos_of_ne_bot {F : Type*} [Field F] [NumberField F]
    {I : Ideal (𝓞 F)} (h : I ≠ ⊥) : (0 : ℝ) < (Ideal.absNorm I : ℝ) := by
  have h0 : Ideal.absNorm I ≠ 0 := fun hh => h (Ideal.absNorm_eq_zero_iff.mp hh)
  exact_mod_cast Nat.pos_of_ne_zero h0

private lemma one_le_absNorm_of_ne_bot {F : Type*} [Field F] [NumberField F]
    {I : Ideal (𝓞 F)} (h : I ≠ ⊥) : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have h0 : Ideal.absNorm I ≠ 0 := fun hh => h (Ideal.absNorm_eq_zero_iff.mp hh)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0

private lemma div_rpow_neg_half {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    (x / Y) ^ (-(1 / 2 : ℝ)) = Y ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow hx.le hY.le, Real.rpow_neg hY.le, div_inv_eq_mul, mul_comm]

private lemma div_rpow_neg_two {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    (x / Y) ^ (-(2 : ℝ)) = Y ^ 2 * x ^ (-(2 : ℝ)) := by
  rw [Real.div_rpow hx.le hY.le, Real.rpow_neg hY.le, div_inv_eq_mul, Real.rpow_two, mul_comm]

noncomputable def nearScaled (F : Type*) [Field F] [NumberField F] (Y : ℝ)
    (I : Ideal (𝓞 F)) : ℝ :=
  if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y then (Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) else 0

noncomputable def farScaled (F : Type*) [Field F] [NumberField F] (Y : ℝ)
    (I : Ideal (𝓞 F)) : ℝ :=
  if I ≠ ⊥ ∧ Y < (Ideal.absNorm I : ℝ) then (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)) else 0

noncomputable def nearPart (F : Type*) [Field F] [NumberField F] (Y : ℝ)
    (I : Ideal (𝓞 F)) : ℝ :=
  if I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y then ((Ideal.absNorm I : ℝ) / Y) ^ (-(1 / 2 : ℝ)) else 0

noncomputable def farPart (F : Type*) [Field F] [NumberField F] (Y : ℝ)
    (I : Ideal (𝓞 F)) : ℝ :=
  if I ≠ ⊥ ∧ Y < (Ideal.absNorm I : ℝ) then ((Ideal.absNorm I : ℝ) / Y) ^ (-(2 : ℝ)) else 0

private lemma nearPart_eq_mul (F : Type*) [Field F] [NumberField F] {Y : ℝ} (hY : 0 < Y)
    (I : Ideal (𝓞 F)) : nearPart F Y I = Y ^ (1 / 2 : ℝ) * nearScaled F Y I := by
  unfold nearPart nearScaled
  by_cases hc : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y
  · rw [if_pos hc, if_pos hc]
    exact div_rpow_neg_half (absNorm_pos_of_ne_bot hc.1) hY
  · rw [if_neg hc, if_neg hc, mul_zero]

private lemma farPart_eq_mul (F : Type*) [Field F] [NumberField F] {Y : ℝ} (hY : 0 < Y)
    (I : Ideal (𝓞 F)) : farPart F Y I = Y ^ 2 * farScaled F Y I := by
  unfold farPart farScaled
  by_cases hc : I ≠ ⊥ ∧ Y < (Ideal.absNorm I : ℝ)
  · rw [if_pos hc, if_pos hc]
    exact div_rpow_neg_two (absNorm_pos_of_ne_bot hc.1) hY
  · rw [if_neg hc, if_neg hc, mul_zero]

theorem initial_two_ended_ideal_sum (F : Type*) [Field F] [NumberField F] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Y : ℝ, 0 < Y →
      ∀ g : Ideal (𝓞 F) → ℂ, g ⊥ = 0 →
        (∀ I : Ideal (𝓞 F), I ≠ ⊥ →
          ‖g I‖ ≤ if (Ideal.absNorm I : ℝ) ≤ Y then
            ((Ideal.absNorm I : ℝ) / Y) ^ (-(1 / 2 : ℝ))
          else ((Ideal.absNorm I : ℝ) / Y) ^ (-(2 : ℝ))) →
        Summable (fun I => ‖g I‖) ∧ Summable g ∧ (∑' I, ‖g I‖) ≤ B * Y := by
  classical
  obtain ⟨Bhalf, hBhalf0, hBhalf⟩ :=
    exists_ideal_inverse_power_initial_bound F (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Btail, hBtail0, hBtail⟩ :=
    exists_filtered_ideal_inverse_power_tail_bound F 2 (by norm_num)
  have hsum2 : Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))) :=
    summable_ideal_inverse_power F 2 (by norm_num)
  set Z2 : ℝ := ∑' I : Ideal (𝓞 F),
      (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))) with hZ2def
  have hZ2nn : 0 ≤ Z2 := by
    rw [hZ2def]
    exact tsum_nonneg fun I => by
      by_cases h : I = ⊥
      · simp [h]
      · simp only [h, if_false]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨Bhalf + Btail + Z2, by linarith, ?_⟩
  intro Y hY g hg0 hg

  have hnearSummable : Summable (nearScaled F Y) := by
    refine summable_of_ne_finset_zero (s := (boundedNormIdeals F Y).filter (fun I => I ≠ ⊥)) ?_
    intro I hI
    by_cases h : I = ⊥
    · rw [nearScaled, if_neg (fun hc => hc.1 h)]
    · by_cases hle : (Ideal.absNorm I : ℝ) ≤ Y
      · exact absurd (by rw [Finset.mem_filter]; exact ⟨mem_boundedNormIdeals.mpr hle, h⟩) hI
      · rw [nearScaled, if_neg (fun hc => hle hc.2)]
  have hfarSummable : Summable (farScaled F Y) := by
    refine Summable.of_nonneg_of_le (g := farScaled F Y)
      (f := fun I : Ideal (𝓞 F) =>
        if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ)))
      (fun I => ?_) (fun I => ?_) hsum2
    · by_cases h : I = ⊥
      · rw [farScaled, if_neg (fun hc => hc.1 h)]
      · by_cases hlt : Y < (Ideal.absNorm I : ℝ)
        · rw [farScaled, if_pos ⟨h, hlt⟩]
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · rw [farScaled, if_neg (fun hc => hlt hc.2)]
    · by_cases h : I = ⊥
      · rw [farScaled, if_neg (fun hc => hc.1 h), if_pos h]
      · by_cases hlt : Y < (Ideal.absNorm I : ℝ)
        · rw [farScaled, if_pos ⟨h, hlt⟩, if_neg h]
        · rw [farScaled, if_neg (fun hc => hlt hc.2), if_neg h]
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnearSummable' : Summable (nearPart F Y) := by
    have h := hnearSummable.mul_left (Y ^ (1 / 2 : ℝ))
    exact h.congr (fun I => (nearPart_eq_mul F hY I).symm)
  have hfarSummable' : Summable (farPart F Y) := by
    have h := hfarSummable.mul_left (Y ^ 2)
    exact h.congr (fun I => (farPart_eq_mul F hY I).symm)

  have hnearTsum : (∑' I : Ideal (𝓞 F), nearScaled F Y I)
      = ∑ I ∈ (boundedNormIdeals F Y).filter (fun I => I ≠ ⊥),
          (Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hzero : ∀ I ∉ (boundedNormIdeals F Y).filter (fun I => I ≠ ⊥),
        nearScaled F Y I = 0 := by
      intro I hI
      by_cases h : I = ⊥
      · rw [nearScaled, if_neg (fun hc => hc.1 h)]
      · by_cases hle : (Ideal.absNorm I : ℝ) ≤ Y
        · exact absurd (by rw [Finset.mem_filter]; exact ⟨mem_boundedNormIdeals.mpr hle, h⟩) hI
        · rw [nearScaled, if_neg (fun hc => hle hc.2)]
    rw [tsum_eq_sum (f := nearScaled F Y)
      (s := (boundedNormIdeals F Y).filter (fun I => I ≠ ⊥)) hzero]
    exact Finset.sum_congr rfl fun I hI => by
      rw [nearScaled, if_pos ⟨(Finset.mem_filter.mp hI).2, mem_boundedNormIdeals.mp (Finset.mem_filter.mp hI).1⟩]

  have hhalf : Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) = Y := by
    rw [← Real.rpow_add hY, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hYinv : Y ^ 2 * Y ^ (-1 : ℝ) = Y := by
    rw [Real.rpow_neg_one]
    field_simp
  have hbound : (∑' I : Ideal (𝓞 F), (nearPart F Y I + farPart F Y I))
      ≤ (Bhalf + Btail + Z2) * Y := by
    rw [Summable.tsum_add hnearSummable' hfarSummable',
      tsum_congr (fun I => nearPart_eq_mul F hY I), tsum_congr (fun I => farPart_eq_mul F hY I),
      tsum_mul_left, tsum_mul_left]
    by_cases hY1 : 1 ≤ Y
    · have hN : (∑' I : Ideal (𝓞 F), nearScaled F Y I) ≤ Bhalf * Y ^ (1 / 2 : ℝ) := by
        have h := hBhalf Y hY1
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
        rw [hnearTsum]
        exact h
      have hF : (∑' I : Ideal (𝓞 F), farScaled F Y I) ≤ Btail * Y ^ (-1 : ℝ) := by
        have h := hBtail Y (fun _ => True) hY1
        rw [show (1 : ℝ) - 2 = -1 by norm_num] at h
        exact (le_of_eq (tsum_congr fun I => by simp [farScaled])).trans h
      have hN' : Y ^ (1 / 2 : ℝ) * (∑' I : Ideal (𝓞 F), nearScaled F Y I) ≤ Bhalf * Y := by
        calc Y ^ (1 / 2 : ℝ) * (∑' I : Ideal (𝓞 F), nearScaled F Y I)
            ≤ Y ^ (1 / 2 : ℝ) * (Bhalf * Y ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hY.le _)
          _ = Bhalf * (Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) := by ring
          _ = Bhalf * Y := by rw [hhalf]
      have hF' : Y ^ 2 * (∑' I : Ideal (𝓞 F), farScaled F Y I) ≤ Btail * Y := by
        calc Y ^ 2 * (∑' I : Ideal (𝓞 F), farScaled F Y I)
            ≤ Y ^ 2 * (Btail * Y ^ (-1 : ℝ)) :=
              mul_le_mul_of_nonneg_left hF (by positivity)
          _ = Btail * (Y ^ 2 * Y ^ (-1 : ℝ)) := by ring
          _ = Btail * Y := by rw [hYinv]
      linarith [hN', hF', mul_nonneg hZ2nn hY.le]
    · have hYlt : Y < 1 := lt_of_not_ge hY1
      have hN : (∑' I : Ideal (𝓞 F), nearScaled F Y I) = 0 := by
        have hzero : ∀ I : Ideal (𝓞 F), nearScaled F Y I = 0 := by
          intro I
          by_cases h : I = ⊥
          · rw [nearScaled, if_neg (fun hc => hc.1 h)]
          · have hlt : ¬ ((Ideal.absNorm I : ℝ) ≤ Y) := by
              have := one_le_absNorm_of_ne_bot h
              linarith
            rw [nearScaled, if_neg (fun hc => hlt hc.2)]
        rw [tsum_eq_sum (f := nearScaled F Y) (s := ∅) (fun I _ => hzero I)]
        simp
      have hF : (∑' I : Ideal (𝓞 F), farScaled F Y I) = Z2 := by
        rw [hZ2def]
        refine tsum_congr fun I => ?_
        by_cases h : I = ⊥
        · rw [farScaled, if_neg (fun hc => hc.1 h)]; simp [h]
        · have hlt : Y < (Ideal.absNorm I : ℝ) :=
            lt_of_lt_of_le hYlt (one_le_absNorm_of_ne_bot h)
          rw [farScaled, if_pos ⟨h, hlt⟩, if_neg h]
      have hF' : Y ^ 2 * (∑' I : Ideal (𝓞 F), farScaled F Y I) ≤ Z2 * Y := by
        rw [hF]
        have hY2 : Y ^ 2 ≤ Y := by nlinarith [hY, hYlt]
        calc Y ^ 2 * Z2 ≤ Y * Z2 := mul_le_mul_of_nonneg_right hY2 hZ2nn
          _ = Z2 * Y := by ring
      have hN' : Y ^ (1 / 2 : ℝ) * (∑' I : Ideal (𝓞 F), nearScaled F Y I) = 0 := by
        rw [hN, mul_zero]
      have hrest : 0 ≤ (Bhalf + Btail) * Y := mul_nonneg (by linarith) hY.le
      linarith [hN', hF', hrest]

  have hnearnn : ∀ I : Ideal (𝓞 F), 0 ≤ nearPart F Y I := by
    intro I
    by_cases hc : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y
    · rw [nearPart, if_pos hc]
      exact Real.rpow_nonneg (div_nonneg (le_of_lt (absNorm_pos_of_ne_bot hc.1)) hY.le) _
    · rw [nearPart, if_neg hc]
  have hfarnn : ∀ I : Ideal (𝓞 F), 0 ≤ farPart F Y I := by
    intro I
    by_cases hc : I ≠ ⊥ ∧ Y < (Ideal.absNorm I : ℝ)
    · rw [farPart, if_pos hc]
      exact Real.rpow_nonneg (div_nonneg (le_of_lt (absNorm_pos_of_ne_bot hc.1)) hY.le) _
    · rw [farPart, if_neg hc]
  have henv : ∀ I : Ideal (𝓞 F), ‖g I‖ ≤ nearPart F Y I + farPart F Y I := by
    intro I
    by_cases h : I = ⊥
    · rw [h, hg0, norm_zero, nearPart, if_neg (fun hc => hc.1 rfl), farPart,
        if_neg (fun hc => hc.1 rfl)]
      simp
    · by_cases hle : (Ideal.absNorm I : ℝ) ≤ Y
      · have hthis := hg I h
        rw [if_pos hle] at hthis
        have hfar : farPart F Y I = 0 := if_neg (fun hc => not_lt_of_ge hle hc.2)
        rw [nearPart, if_pos ⟨h, hle⟩, hfar, add_zero]
        exact hthis
      · have hthis := hg I h
        rw [if_neg hle] at hthis
        have hnear : nearPart F Y I = 0 := if_neg (fun hc => hle hc.2)
        rw [farPart, if_pos ⟨h, lt_of_not_ge hle⟩, hnear, zero_add]
        exact hthis
  have key : ∀ u : Finset (Ideal (𝓞 F)), ∑ I ∈ u, ‖g I‖ ≤ (Bhalf + Btail + Z2) * Y := by
    intro u
    calc ∑ I ∈ u, ‖g I‖ ≤ ∑ I ∈ u, (nearPart F Y I + farPart F Y I) :=
          Finset.sum_le_sum fun I _ => henv I
      _ ≤ ∑' I : Ideal (𝓞 F), (nearPart F Y I + farPart F Y I) :=
          Summable.sum_le_tsum u (fun I _ => add_nonneg (hnearnn I) (hfarnn I))
            (hnearSummable'.add hfarSummable')
      _ ≤ (Bhalf + Btail + Z2) * Y := hbound
  have hnorm : Summable (fun I : Ideal (𝓞 F) => ‖g I‖) :=
    summable_of_sum_le (fun I => norm_nonneg _) key
  exact ⟨hnorm, Summable.of_norm hnorm, Real.tsum_le_of_sum_le (fun I => norm_nonneg _) key⟩

end DedekindZetaZeroFree.LargeSieve.Sieve
