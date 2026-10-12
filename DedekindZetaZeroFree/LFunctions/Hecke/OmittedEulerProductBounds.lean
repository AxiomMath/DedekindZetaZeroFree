module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField BigOperators
open UniqueFactorizationMonoid

private lemma rpow_two_inv_mul_self (ε : ℝ) (hε : ε ≠ 0) : ((2 : ℝ) ^ (1 / ε)) ^ ε = 2 := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), div_mul_cancel₀ 1 hε, Real.rpow_one]

private lemma threshold_bound (σ₀ ε : ℝ) (hσ₀ : 0 < σ₀) (hε : 0 < ε) (x : ℝ)
    (hx : (2 : ℝ) ^ (1 / ε) + (2 : ℝ) ^ (1 / σ₀) ≤ x) :
    1 + x ^ (-σ₀) ≤ x ^ ε ∧ (1 - x ^ (-σ₀))⁻¹ ≤ x ^ ε := by
  have hεnn : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / ε) := Real.rpow_nonneg (by norm_num) _
  have hσnn : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / σ₀) := Real.rpow_nonneg (by norm_num) _
  have hxε : (2 : ℝ) ^ (1 / ε) ≤ x := (le_add_of_nonneg_right hσnn).trans hx
  have hxσ : (2 : ℝ) ^ (1 / σ₀) ≤ x := (le_add_of_nonneg_left hεnn).trans hx
  have h2ε : (2 : ℝ) ≤ x ^ ε := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hxε hε.le
    rwa [rpow_two_inv_mul_self ε hε.ne'] at h
  have h2σ : (2 : ℝ) ≤ x ^ σ₀ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hxσ hσ₀.le
    rwa [rpow_two_inv_mul_self σ₀ hσ₀.ne'] at h
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (one_div_pos.mpr hσ₀)) hxσ
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hhalf : x ^ (-σ₀) ≤ 1 / 2 := by
    rw [Real.rpow_neg hxpos.le σ₀]
    calc (x ^ σ₀)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2σ
      _ = 1 / 2 := by norm_num
  constructor
  · linarith
  · have hpos : 0 < 1 - x ^ (-σ₀) := by linarith
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (by linarith :
      (1 : ℝ) / 2 ≤ 1 - x ^ (-σ₀))
    have h2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    linarith

private lemma small_case (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (x : ℝ) (hx : 2 ≤ x) :
    1 + x ^ (-σ₀) ≤ 1 + (2 : ℝ) ^ (-σ₀) ∧
      (1 - x ^ (-σ₀))⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := by
  have hle : x ^ (-σ₀) ≤ (2 : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
  have h2lt : (2 : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hb : 0 < 1 - (2 : ℝ) ^ (-σ₀) := by linarith
  exact ⟨by linarith, inv_anti₀ hb (by linarith)⟩

private lemma support_norm_prod_le {F : Type} [Field F] [NumberField F]
    (𝔲 : Ideal (𝓞 F)) (h𝔲 : 𝔲 ≠ ⊥) :
    (∏ p ∈ idealPrimeSupport 𝔲, idealNorm p) ≤ idealNorm 𝔲 := by
  have hd : idealRadical 𝔲 ∣ 𝔲 := by
    have H := Multiset.prod_dvd_prod_of_le (Multiset.dedup_le (normalizedFactors 𝔲))
    have Heq : (normalizedFactors 𝔲).prod = 𝔲 := by
      simpa only [associated_eq_eq] using prod_normalizedFactors h𝔲
    simpa only [idealRadical, idealPrimeSupport, Finset.prod_eq_multiset_prod,
      Multiset.map_id', Multiset.toFinset_val, Heq] using H
  have hnorm := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd)
  have hpos : 0 < Ideal.absNorm 𝔲 :=
    Nat.pos_of_ne_zero (fun hz => h𝔲 (Ideal.absNorm_eq_zero_iff.mp hz))
  have H : idealNorm (idealRadical 𝔲) ≤ idealNorm 𝔲 := by
    unfold idealNorm
    exact_mod_cast Nat.le_of_dvd hpos hnorm
  simpa only [idealNorm, idealRadical, map_prod, Nat.cast_prod] using H

private lemma prod_norm_le_of_dvd {F : Type} [Field F] [NumberField F]
    (𝔲 : Ideal (𝓞 F)) (h𝔲 : 𝔲 ≠ ⊥) (T : Finset (Ideal (𝓞 F)))
    (hT : ∀ 𝔭 ∈ T, Prime 𝔭 ∧ 𝔭 ∣ 𝔲) :
    (∏ 𝔭 ∈ T, idealNorm 𝔭) ≤ idealNorm 𝔲 := by
  have h𝔲0 : 𝔲 ≠ 0 := fun h => h𝔲 (by simpa using h)
  have hsub : T ⊆ idealPrimeSupport 𝔲 := fun p hp =>
    Multiset.mem_toFinset.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (α := Ideal (𝓞 F)) h𝔲0).mpr
        ⟨(hT p hp).1, (hT p hp).2⟩)
  refine (Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_).trans (support_norm_prod_le 𝔲 h𝔲)
  · intro p hp
    exact le_trans (by norm_num) (idealNorm_prime_ge_two p (hT p hp).1)
  · intro p hp _
    exact le_trans (by norm_num)
      (idealNorm_prime_ge_two p (prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)))

theorem omitted_prime_euler_subpolynomial
    (F : Type) [Field F] [NumberField F]
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hσ₀_one : σ₀ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (𝔲 : Ideal (𝓞 F)), 𝔲 ≠ ⊥ →
      ∀ (T : Finset (Ideal (𝓞 F))),
        (∀ (𝔭 : Ideal (𝓞 F)), 𝔭 ∈ T → Prime 𝔭 ∧ 𝔭 ∣ 𝔲) →
        (∏ 𝔭 ∈ T, (1 + (idealNorm 𝔭) ^ (-σ₀))) ≤ C * (idealNorm 𝔲) ^ ε ∧
        (∏ 𝔭 ∈ T, (1 - (idealNorm 𝔭) ^ (-σ₀))⁻¹) ≤ C * (idealNorm 𝔲) ^ ε := by
  classical
  set Q : ℝ := (2 : ℝ) ^ (1 / ε) + (2 : ℝ) ^ (1 / σ₀) with hQdef
  have hQeq : (2 : ℝ) ^ (1 / ε) + (2 : ℝ) ^ (1 / σ₀) = Q := hQdef.symm
  let B : ℝ := max (1 + (2 : ℝ) ^ (-σ₀)) ((1 - (2 : ℝ) ^ (-σ₀))⁻¹)
  have hB1 : 1 ≤ B := by
    refine le_trans ?_ (le_max_left _ _)
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-σ₀)
    linarith
  have hefin : (Subtype.val '' normBoundedIdeals F Q).Finite :=
    (normBoundedIdeals_finite F Q).image Subtype.val
  let e : Finset (Ideal (𝓞 F)) := hefin.toFinset
  refine ⟨B ^ e.card, pow_pos (lt_of_lt_of_le zero_lt_one hB1) _, ?_⟩
  intro 𝔲 h𝔲 T hT
  have hnorm : (∏ 𝔭 ∈ T, idealNorm 𝔭) ≤ idealNorm 𝔲 := prod_norm_le_of_dvd 𝔲 h𝔲 T hT
  have hmem_e : ∀ 𝔭 : Ideal (𝓞 F), Prime 𝔭 → idealNorm 𝔭 ≤ Q → 𝔭 ∈ e := fun 𝔭 hp hle =>
    hefin.mem_toFinset.mpr ⟨⟨𝔭, by simpa using hp.ne_zero⟩, hle, rfl⟩
  have hloc1 : ∀ 𝔭 ∈ T, 1 + (idealNorm 𝔭) ^ (-σ₀) ≤
      (if 𝔭 ∈ e then B else 1) * (idealNorm 𝔭) ^ ε := by
    intro 𝔭 h𝔭
    have hp := (hT 𝔭 h𝔭).1
    have hp2 : (2 : ℝ) ≤ idealNorm 𝔭 := idealNorm_prime_ge_two 𝔭 hp
    have hpow : 1 ≤ (idealNorm 𝔭) ^ ε := Real.one_le_rpow (by linarith) hε.le
    split_ifs with hpe
    · have hb : 1 + (idealNorm 𝔭) ^ (-σ₀) ≤ B :=
        (small_case σ₀ hσ₀ (idealNorm 𝔭) hp2).1.trans (le_max_left _ _)
      exact hb.trans (le_mul_of_one_le_right (le_trans zero_le_one hB1) hpow)
    · have hlarge : Q ≤ idealNorm 𝔭 := by
        by_contra H
        exact hpe (hmem_e 𝔭 hp (le_of_lt (lt_of_not_ge H)))
      have := (threshold_bound σ₀ ε hσ₀ hε (idealNorm 𝔭) (hQeq.le.trans hlarge)).1
      simpa using this
  have hloc2 : ∀ 𝔭 ∈ T, (1 - (idealNorm 𝔭) ^ (-σ₀))⁻¹ ≤
      (if 𝔭 ∈ e then B else 1) * (idealNorm 𝔭) ^ ε := by
    intro 𝔭 h𝔭
    have hp := (hT 𝔭 h𝔭).1
    have hp2 : (2 : ℝ) ≤ idealNorm 𝔭 := idealNorm_prime_ge_two 𝔭 hp
    have hpow : 1 ≤ (idealNorm 𝔭) ^ ε := Real.one_le_rpow (by linarith) hε.le
    split_ifs with hpe
    · have hb : (1 - (idealNorm 𝔭) ^ (-σ₀))⁻¹ ≤ B :=
        (small_case σ₀ hσ₀ (idealNorm 𝔭) hp2).2.trans (le_max_right _ _)
      exact hb.trans (le_mul_of_one_le_right (le_trans zero_le_one hB1) hpow)
    · have hlarge : Q ≤ idealNorm 𝔭 := by
        by_contra H
        exact hpe (hmem_e 𝔭 hp (le_of_lt (lt_of_not_ge H)))
      have := (threshold_bound σ₀ ε hσ₀ hε (idealNorm 𝔭) (hQeq.le.trans hlarge)).2
      simpa using this
  have hconst : (∏ 𝔭 ∈ T, (if 𝔭 ∈ e then B else 1)) ≤ B ^ e.card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    exact pow_le_pow_right₀ hB1 (Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2)
  have hnn : ∀ 𝔭 ∈ T, 0 ≤ idealNorm 𝔭 := fun 𝔭 h𝔭 =>
    le_trans (by norm_num) (idealNorm_prime_ge_two 𝔭 (hT 𝔭 h𝔭).1)
  have hstep : ∀ (f : Ideal (𝓞 F) → ℝ), (∀ 𝔭 ∈ T, 0 ≤ f 𝔭) →
      (∀ 𝔭 ∈ T, f 𝔭 ≤ (if 𝔭 ∈ e then B else 1) * (idealNorm 𝔭) ^ ε) →
      (∏ 𝔭 ∈ T, f 𝔭) ≤ B ^ e.card * (idealNorm 𝔲) ^ ε := by
    intro f hf0 hf
    calc ∏ 𝔭 ∈ T, f 𝔭
        ≤ ∏ 𝔭 ∈ T, (if 𝔭 ∈ e then B else 1) * (idealNorm 𝔭) ^ ε :=
          Finset.prod_le_prod₀ hf0 hf
      _ = (∏ 𝔭 ∈ T, (if 𝔭 ∈ e then B else 1)) * (∏ 𝔭 ∈ T, (idealNorm 𝔭) ^ ε) :=
          Finset.prod_mul_distrib
      _ = (∏ 𝔭 ∈ T, (if 𝔭 ∈ e then B else 1)) * (∏ 𝔭 ∈ T, idealNorm 𝔭) ^ ε := by
          rw [Real.finsetProd_rpow T idealNorm hnn ε]
      _ ≤ B ^ e.card * (idealNorm 𝔲) ^ ε := by
          refine mul_le_mul hconst (Real.rpow_le_rpow (Finset.prod_nonneg hnn) hnorm hε.le)
            (Real.rpow_nonneg (Finset.prod_nonneg hnn) _) ?_
          exact pow_nonneg (le_trans zero_le_one hB1) _
  constructor
  · refine hstep _ ?_ hloc1
    intro 𝔭 h𝔭
    have := Real.rpow_nonneg (hnn 𝔭 h𝔭) (-σ₀)
    linarith
  · refine hstep _ ?_ hloc2
    intro 𝔭 h𝔭
    have hp2 := idealNorm_prime_ge_two 𝔭 (hT 𝔭 h𝔭).1
    have hlt : (idealNorm 𝔭) ^ (-σ₀) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    exact inv_nonneg.mpr (by linarith)

end
end DedekindZetaZeroFree
