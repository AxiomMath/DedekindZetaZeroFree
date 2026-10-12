module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical
open UniqueFactorizationMonoid Filter

private theorem pcSmall_support_norm_le {F : Type} [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (∏ p ∈ idealPrimeSupport I, idealNorm p) ≤ idealNorm I := by
  have hd : (∏ p ∈ idealPrimeSupport I, p) ∣ I := by
    have hd' : (normalizedFactors I).dedup.prod ∣ (normalizedFactors I).prod :=
      Multiset.prod_dvd_prod_of_le (Multiset.dedup_le _)
    simpa only [idealPrimeSupport, Finset.prod_eq_multiset_prod, Multiset.map_id',
      Multiset.toFinset_val, Ideal.prod_normalizedFactors_eq_self hI] using hd'
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (map_dvd Ideal.absNorm hd)
  simpa [idealNorm, map_prod, Nat.cast_prod] using (show
    ((Ideal.absNorm (∏ p ∈ idealPrimeSupport I, p) : ℕ) : ℝ) ≤ (Ideal.absNorm I : ℝ) by exact_mod_cast hn)

private theorem pcSmall_local_bound (C δ ε : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ Q : ℝ, B ≤ Q → 1 ≤ Q → 1 + C * Q ^ (-δ) ≤ Q ^ ε := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hε).eventually
    (eventually_ge_atTop (1 + C)))
  refine ⟨B, fun Q hBQ hQ => ?_⟩
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith : -δ ≤ 0)
  nlinarith [hB Q hBQ]

theorem fixed_small_prime_subpower
    (F : Type) [Field F] [NumberField F]
    (cS : Ideal (𝓞 F)) (C δ ε : ℝ)
    (hC : 0 ≤ C) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ I : ExteriorIdeal cS,
      (∏ p ∈ idealPrimeSupport I.val,
        (1 + C * (idealNorm p) ^ (-δ))) ≤ K * (idealNorm I.val) ^ ε := by
  obtain ⟨B, hB⟩ := pcSmall_local_bound C δ ε hC hδ hε
  let s : Finset (Ideal (𝓞 F)) := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈B⌉₊).toFinset
  let f : Ideal (𝓞 F) → ℝ := fun p => 1 + C * idealNorm p ^ (-δ)
  have hf : ∀ p, 1 ≤ f p := by
    intro p
    dsimp [f]
    have hn : 0 ≤ idealNorm p := by unfold idealNorm; positivity
    have := Real.rpow_nonneg hn (-δ)
    nlinarith
  let K := ∏ p ∈ s, f p
  refine ⟨K, ?_, ?_⟩
  · exact Finset.prod_pos (fun p _ => lt_of_lt_of_le zero_lt_one (hf p))
  · intro I
    have hp : ∀ p ∈ idealPrimeSupport I.val, Prime p := by
      intro p hp
      exact prime_of_normalized_factor p (by
        simpa only [idealPrimeSupport, Multiset.mem_toFinset] using hp)
    have hq : ∀ p ∈ idealPrimeSupport I.val, 1 ≤ idealNorm p := by
      intro p h
      exact le_trans (by norm_num) (idealNorm_prime_ge_two p (hp p h))
    have hs : ∀ p, p ∉ s → B ≤ idealNorm p := by
      intro p h
      have hn : ¬ Ideal.absNorm p ≤ ⌈B⌉₊ := by simpa [s] using h
      have hn' : (⌈B⌉₊ : ℝ) < idealNorm p := by
        unfold idealNorm
        exact_mod_cast (lt_of_not_ge hn)
      exact (Nat.le_ceil B).trans hn'.le
    have hloc : ∀ p ∈ idealPrimeSupport I.val,
        f p ≤ (if p ∈ s then f p else 1) * idealNorm p ^ ε := by
      intro p h
      split_ifs with hh
      · exact le_mul_of_one_le_right (le_trans zero_le_one (hf p))
          (Real.one_le_rpow (hq p h) hε.le)
      · simpa [f] using hB (idealNorm p) (hs p hh) (hq p h)
    have hsmall : (∏ p ∈ idealPrimeSupport I.val, if p ∈ s then f p else 1) ≤ K := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, mul_one]
      apply Finset.prod_le_prod_of_subset_of_one_le₀
      · intro p h
        exact (Finset.mem_filter.mp h).2
      · intro p _
        exact le_trans zero_le_one (hf p)
      · intro p _ _
        exact hf p
    calc
      (∏ p ∈ idealPrimeSupport I.val, f p) ≤
          ∏ p ∈ idealPrimeSupport I.val, (if p ∈ s then f p else 1) * idealNorm p ^ ε :=
        Finset.prod_le_prod₀ (fun p _ => (le_trans zero_le_one (hf p))) hloc
      _ = (∏ p ∈ idealPrimeSupport I.val, if p ∈ s then f p else 1) *
          (∏ p ∈ idealPrimeSupport I.val, idealNorm p ^ ε) := Finset.prod_mul_distrib
      _ ≤ K * (∏ p ∈ idealPrimeSupport I.val, idealNorm p ^ ε) :=
        mul_le_mul_of_nonneg_right hsmall (Finset.prod_nonneg (fun p h =>
          Real.rpow_nonneg (le_trans zero_le_one (hq p h)) ε))
      _ ≤ K * idealNorm I.val ^ ε := by
        apply mul_le_mul_of_nonneg_left _
          (Finset.prod_nonneg (fun p _ => (le_trans zero_le_one (hf p))))
        rw [Real.finset_prod_rpow _ _ (fun p h => le_trans zero_le_one (hq p h))]
        exact Real.rpow_le_rpow
          (Finset.prod_nonneg (fun p h => le_trans zero_le_one (hq p h)))
          (pcSmall_support_norm_le I.val I.property.1) hε.le

end

end DedekindZetaZeroFree
