module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries
public import DedekindZetaZeroFree.Moments.Reflected.BetaEulerSeries

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
open UniqueFactorizationMonoid

private theorem support_prod (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ p ∈ s, Prime p) : idealPrimeSupport (∏ p ∈ s, p) = s := by
  unfold idealPrimeSupport
  have H : normalizedFactors s.val.prod = s.val :=
    normalizedFactors_prod_of_prime (by simpa using hs)
  simpa using congrArg Multiset.toFinset H

private theorem prod_ne_bot (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ p ∈ s, Prime p) : (∏ p ∈ s, p) ≠ ⊥ := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)

private theorem prime_of_support (h : Ideal (𝓞 F)) {p : Ideal (𝓞 F)}
    (hp : p ∈ idealPrimeSupport h) : Prime p :=
  prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)

def activeSquarefreeDivisors (h : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  (idealPrimeSupport h).powerset.image (fun s => ∏ p ∈ s, p)

theorem mem_activeSquarefreeDivisors_iff (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (f : Ideal (𝓞 F)) :
    f ∈ activeSquarefreeDivisors h ↔
      f ≠ ⊥ ∧ Squarefree f ∧ f ∣ idealRadical h := by
  have hp : ∀ p ∈ idealPrimeSupport h, Prime p := fun p hp => prime_of_support h hp
  have hr := (idealRadical_squarefree_nonzero h hh).2
  have hrad : normalizedFactors (idealRadical h) = (idealPrimeSupport h).val :=
    by simpa only [idealRadical, Finset.prod_eq_multiset_prod, Multiset.map_id'] using
      (normalizedFactors_prod_of_prime (m := (idealPrimeSupport h).val)
        (fun p hp' => hp p hp'))
  constructor
  · intro hf
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf
    have hs' := Finset.mem_powerset.mp hs
    have hp' : ∀ p ∈ s, Prime p := fun p hps => hp p (hs' hps)
    have hn := prod_ne_bot s hp'
    refine ⟨hn, ?_, ?_⟩
    · apply (squarefree_iff_nodup_normalizedFactors hn).mpr
      have H : normalizedFactors s.val.prod = s.val :=
        normalizedFactors_prod_of_prime (by simpa using hp')
      simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id', H] using s.nodup
    · apply (dvd_iff_normalizedFactors_le_normalizedFactors hn hr).mpr
      rw [hrad]
      have H : normalizedFactors s.val.prod = s.val :=
        normalizedFactors_prod_of_prime (by simpa using hp')
      simpa only [Finset.prod_eq_multiset_prod, Multiset.map_id', H] using
        (Finset.val_le_iff.mpr hs')
  · rintro ⟨hf, hsf, hdiv⟩
    have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hf hr).mp hdiv
    have hsub : idealPrimeSupport f ⊆ idealPrimeSupport h := by
      intro p hp
      have := Multiset.mem_of_le hle (Multiset.mem_toFinset.mp hp)
      simpa [hrad] using this
    apply Finset.mem_image.mpr
    refine ⟨idealPrimeSupport f, Finset.mem_powerset.mpr hsub, ?_⟩
    have hn := (squarefree_iff_nodup_normalizedFactors hf).mp hsf
    have H : (normalizedFactors f).prod = f :=
      by simpa only [associated_eq_eq] using (prod_normalizedFactors hf)
    simpa only [idealPrimeSupport, Finset.prod_eq_multiset_prod, Multiset.map_id',
      Multiset.toFinset_val, hn.dedup] using H

def activeEulerFactor (f : Ideal (𝓞 F)) (σ : ℝ) : ℝ :=
  ∏ p ∈ idealPrimeSupport f, eulerLocal (idealNorm p) σ

def activeEulerSum (h : Ideal (𝓞 F)) (σ : ℝ) : ℝ :=
  ∑ f ∈ activeSquarefreeDivisors h, activeEulerFactor f σ

theorem activeEulerFactor_eq_eulerIdeal {cS : Ideal (𝓞 F)}
    (f : ExteriorSquarefreeIdeal cS) (σ : ℝ) :
    activeEulerFactor f.val.val σ = eulerIdeal f σ := by
  rfl

theorem activeEulerSum_eq_prod (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) (σ : ℝ) :
    activeEulerSum h σ =
      ∏ p ∈ idealPrimeSupport h, (1 + eulerLocal (idealNorm p) σ) := by
  unfold activeEulerSum activeSquarefreeDivisors
  rw [Finset.sum_image]
  · rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro s hs
    unfold activeEulerFactor
    rw [support_prod s (fun p hp => prime_of_support h (Finset.mem_powerset.mp hs hp))]
  · intro s hs t ht hst
    have Hs := support_prod s (fun p hp => prime_of_support h (Finset.mem_powerset.mp hs hp))
    have Ht := support_prod t (fun p hp => prime_of_support h (Finset.mem_powerset.mp ht hp))
    exact Hs.symm.trans ((congrArg idealPrimeSupport hst).trans Ht)

theorem activeEulerFactor_nonneg (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    0 ≤ activeEulerFactor f σ := by
  apply Finset.prod_nonneg
  intro p hp
  exact le_trans zero_le_one
    (eulerLocal_bounds _ σ (idealNorm_prime_ge_two p (prime_of_support f hp)) hσ).1

theorem activeEulerSum_subset_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (σ : ℝ) (hσ : 0 ≤ σ) (t : Finset (Ideal (𝓞 F)))
    (ht : t ⊆ activeSquarefreeDivisors h) :
    (∑ f ∈ t, activeEulerFactor f σ) ≤ activeEulerSum h σ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg ht
  intro f hf _
  exact activeEulerFactor_nonneg f ((mem_activeSquarefreeDivisors_iff h hh f).mp hf).1 σ hσ

private theorem support_norm_prod_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥) :
    (∏ p ∈ idealPrimeSupport h, idealNorm p) ≤ idealNorm h := by
  have hd : idealRadical h ∣ h := by
    have H := Multiset.prod_dvd_prod_of_le (Multiset.dedup_le (normalizedFactors h))
    have Heq : (normalizedFactors h).prod = h := by
      simpa only [associated_eq_eq] using prod_normalizedFactors hh
    simpa only [idealRadical, idealPrimeSupport, Finset.prod_eq_multiset_prod,
      Multiset.map_id', Multiset.toFinset_val, Heq] using H
  have hnorm := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd)
  have hpos : 0 < Ideal.absNorm h :=
    Nat.pos_of_ne_zero (fun hz => hh (Ideal.absNorm_eq_zero_iff.mp hz))
  have H : idealNorm (idealRadical h) ≤ idealNorm h := by
    unfold idealNorm
    exact_mod_cast Nat.le_of_dvd hpos hnorm
  simpa only [idealNorm, idealRadical, map_prod, Nat.cast_prod] using H

theorem active_subpower (b : ℝ) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (h : Ideal (𝓞 F)), h ≠ ⊥ →
        ∀ (σ : ℝ), 0 ≤ σ →
          activeEulerSum h σ ≤ K * Real.rpow (idealNorm h) b ∧
          ∀ t : Finset (Ideal (𝓞 F)), t ⊆ activeSquarefreeDivisors h →
            (∑ f ∈ t, activeEulerFactor f σ) ≤ K * Real.rpow (idealNorm h) b := by
  let C : ℝ := 4 + Real.sqrt 2
  have hC : 1 ≤ C := by dsimp [C]; have := Real.sqrt_nonneg 2; linarith
  let X : ℝ := Real.rpow C b⁻¹
  have hefin : (Subtype.val '' normBoundedIdeals F X).Finite :=
    (normBoundedIdeals_finite F X).image Subtype.val
  let e : Finset (Ideal (𝓞 F)) := hefin.toFinset
  refine ⟨C ^ e.card, pow_pos (lt_of_lt_of_le zero_lt_one hC) _, ?_⟩
  intro h hh σ hσ
  have hp : ∀ p ∈ idealPrimeSupport h, Prime p := fun p hp => prime_of_support h hp
  have hn : ∀ p ∈ idealPrimeSupport h, 1 ≤ idealNorm p :=
    fun p hps => le_trans (by norm_num) (idealNorm_prime_ge_two p (hp p hps))
  have hpow : ∀ p ∈ idealPrimeSupport h, 1 ≤ Real.rpow (idealNorm p) b :=
    fun p hps => Real.one_le_rpow (hn p hps) hb.le
  have hlocal : ∀ p ∈ idealPrimeSupport h,
      1 + eulerLocal (idealNorm p) σ ≤
        (if p ∈ e then C else 1) * Real.rpow (idealNorm p) b := by
    intro p hps
    have hbound : 1 + eulerLocal (idealNorm p) σ ≤ C := by
      have H := (eulerLocal_bounds _ σ (idealNorm_prime_ge_two p (hp p hps)) hσ).2
      dsimp [C]; linarith
    split_ifs with hpe
    · exact hbound.trans (le_mul_of_one_le_right (le_trans zero_le_one hC) (hpow p hps))
    · have hX : X ≤ idealNorm p := by
        by_contra H
        have hmem : p ∈ e := by
          apply hefin.mem_toFinset.mpr
          refine ⟨⟨p, (hp p hps).ne_zero⟩, ?_, rfl⟩
          exact le_of_lt (lt_of_not_ge H)
        exact hpe hmem
      have HC : Real.rpow X b = C := Real.rpow_inv_rpow (le_trans zero_le_one hC) hb.ne'
      have hx0 : 0 ≤ X := Real.rpow_nonneg (le_trans zero_le_one hC) _
      have H := Real.rpow_le_rpow hx0 hX hb.le
      change Real.rpow X b ≤ Real.rpow (idealNorm p) b at H
      rw [HC] at H
      simpa only [one_mul] using hbound.trans H
  have hconst : (∏ p ∈ idealPrimeSupport h, (if p ∈ e then C else 1)) ≤ C ^ e.card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hC
    apply Finset.card_le_card
    intro p hps
    exact (Finset.mem_filter.mp hps).2
  have hprod : activeEulerSum h σ ≤ C ^ e.card * Real.rpow (idealNorm h) b := by
    rw [activeEulerSum_eq_prod h hh σ]
    calc
      _ ≤ ∏ p ∈ idealPrimeSupport h,
          (if p ∈ e then C else 1) * Real.rpow (idealNorm p) b := by
        apply Finset.prod_le_prod₀ _ hlocal
        intro p hps
        have H := (eulerLocal_bounds _ σ (idealNorm_prime_ge_two p (hp p hps)) hσ).1
        linarith
      _ = (∏ p ∈ idealPrimeSupport h, (if p ∈ e then C else 1)) *
          Real.rpow (∏ p ∈ idealPrimeSupport h, idealNorm p) b := by
        rw [Finset.prod_mul_distrib]
        congr 1
        exact Real.finsetProd_rpow (idealPrimeSupport h) idealNorm
          (fun p hps => le_trans zero_le_one (hn p hps)) b
      _ ≤ C ^ e.card * Real.rpow (idealNorm h) b := by
        apply mul_le_mul hconst
          (Real.rpow_le_rpow (Finset.prod_nonneg (fun p hps => le_trans zero_le_one (hn p hps)))
            (support_norm_prod_le h hh) hb.le)
        · exact Real.rpow_nonneg (Finset.prod_nonneg
            (fun p hps => le_trans zero_le_one (hn p hps))) _
        · exact pow_nonneg (le_trans zero_le_one hC) _
  refine ⟨hprod, ?_⟩
  intro t ht
  exact (activeEulerSum_subset_le h hh σ hσ t ht).trans hprod

end
end DedekindZetaZeroFree
