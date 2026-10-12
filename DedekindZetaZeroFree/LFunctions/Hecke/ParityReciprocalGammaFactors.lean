module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels

@[expose] public section

noncomputable section

open Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity

variable (K : Type) [Field K] [NumberField K]

private lemma differentiable_prod_Gammaℝ (δ : Finset (RayCoset.RealPlaces K)) :
    Differentiable ℂ (fun s : ℂ =>
      ∏ v : RayCoset.RealPlaces K, (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹) := by
  have h := Differentiable.finsetProd (𝕜 := ℂ) (u := Finset.univ)
    (f := fun v : RayCoset.RealPlaces K =>
      fun s : ℂ => (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹)
    (fun v _ => Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const _))
  have hfun : (∏ v : RayCoset.RealPlaces K,
        fun s : ℂ => (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹)
      = (fun s : ℂ =>
        ∏ v : RayCoset.RealPlaces K,
          (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹) := by
    funext s
    rw [Finset.prod_apply]
  rwa [hfun] at h

theorem differentiable_hδ (δ : Finset (RayCoset.RealPlaces K)) :
    Differentiable ℂ (hδ K δ) := by
  unfold hδ
  refine Differentiable.mul (Differentiable.mul (differentiable_const _) ?_) ?_
  · exact differentiable_prod_Gammaℝ K δ
  · exact (Complex.differentiable_Gammaℂ_inv.pow _)

theorem κδ_mul_hδ (δ : Finset (RayCoset.RealPlaces K))
    (s : ℂ) (hs : 1 < s.re) :
    κδ K δ s * hδ K δ s = 1 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hGℂ : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
      (Complex.Gamma_ne_zero_of_re_pos hs0)
  have hfv : ∀ v : RayCoset.RealPlaces K,
      Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0) ≠ 0 := by
    intro v
    by_cases hv : v ∈ δ
    · rw [if_pos hv]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      rw [Complex.add_re, Complex.one_re]
      linarith
    · rw [if_neg hv, add_zero]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hPP' : (∏ v : RayCoset.RealPlaces K,
        Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0)) *
      (∏ v : RayCoset.RealPlaces K,
        (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun v _ => mul_inv_cancel₀ (hfv v))
  have hQQ' : (Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hGℂ, one_pow]
  unfold κδ hδ
  calc ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
        ((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K)⁻¹ *
        (∏ v : RayCoset.RealPlaces K,
          Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0)) *
        (Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (∏ v : RayCoset.RealPlaces K,
            (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹) *
          ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K)
      = ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
          (2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K)⁻¹ *
          (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K) *
        ((∏ v : RayCoset.RealPlaces K,
            Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0)) *
          (∏ v : RayCoset.RealPlaces K,
            (Complex.Gammaℝ (s + if v ∈ δ then (1 : ℂ) else 0))⁻¹)) *
        ((Complex.Gammaℂ s) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ((Complex.Gammaℂ s)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces K) := by
        ring
    _ = 1 := by
        rw [hPP', hQQ',
          inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)),
          inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (4 : ℂ) ≠ 0))]
        ring

theorem hδ_empty_zero : hδ K ∅ 0 = 0 := by
  have hsum := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  have hrank : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hGℝ : Complex.Gammaℝ 0 = 0 := by
    rw [Complex.Gammaℝ_eq_zero_iff]; exact ⟨0, by simp⟩
  have hGℂ : Complex.Gammaℂ 0 = 0 := by
    rw [Complex.Gammaℂ_def, (Complex.Gamma_eq_zero_iff 0).mpr ⟨0, by simp⟩, mul_zero]
  unfold hδ
  simp only [Finset.notMem_empty, ↓reduceIte, add_zero, hGℝ, inv_zero, hGℂ]
  rcases eq_or_ne (NumberField.InfinitePlace.nrRealPlaces K) 0 with h1 | h1
  · have h2 : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
      intro hc
      rw [h1, hc, mul_zero, add_zero] at hsum
      omega
    have hcard : Fintype.card (RayCoset.RealPlaces K) = 0 := h1
    rw [show (∏ _v : RayCoset.RealPlaces K, (0 : ℂ)) = 1 by
      rw [Finset.prod_const, Finset.card_univ, hcard, pow_zero]]
    rw [h1, pow_zero, one_mul, zero_pow h2, mul_zero]
  · have hcard : Fintype.card (RayCoset.RealPlaces K) ≠ 0 := h1
    have hprod : (∏ _v : RayCoset.RealPlaces K, (0 : ℂ)) = 0 := by
      rw [Finset.prod_const, Finset.card_univ]
      exact zero_pow hcard
    rw [hprod]
    ring

end DedekindZetaZeroFree.AbelianQuotient.RayParity

end
