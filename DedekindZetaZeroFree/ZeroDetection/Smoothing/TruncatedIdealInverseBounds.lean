module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.IdealMoebiusInverse

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.Detector

theorem truncatedIdealInverse_bound (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : ℝ), 2 ≤ U →
      ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ →
      ∀ (ω : RayClassCharacter F m), ω.IsPrimitive →
      ∀ (s : ℂ), (1 / 2 : ℝ) ≤ s.re →
        ‖truncatedIdealInverse F ω U s‖ ≤ C * U := by
  classical
  obtain ⟨C, hC, hbound⟩ := ideal_norm_summation_bounds F
  refine ⟨C, hC, ?_⟩
  intro U hU m hm ω hω s hs
  have hU0 : 0 ≤ U := by linarith
  have hU2 : 1 ≤ U ^ (2 : ℕ) := by nlinarith
  let t := (ideals_bounded_norm_finite F (U ^ (2 : ℕ))).toFinset
  let f : Ideal (𝓞 F) → ℂ := fun d =>
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
      (idealMoebius F d : ℂ) * ω d * (Ideal.absNorm d : ℂ) ^ (-s) else 0
  let g : Ideal (𝓞 F) → ℝ := fun d =>
    if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
      (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) else 0
  have hf : Function.support f ⊆ (t : Set (Ideal (𝓞 F))) := by
    intro d hd
    simp only [t, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_contra h
    have h' : ¬ (d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ)) := by
      simpa only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
    exact hd (by simp [f, h'])
  have hg : Function.support g ⊆ (t : Set (Ideal (𝓞 F))) := by
    intro d hd
    simp only [t, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_contra h
    have h' : ¬ (d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ)) := by
      simpa only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
    exact hd (by simp [g, h'])
  have hterm (d : Ideal (𝓞 F)) : ‖f d‖ ≤ g d := by
    by_cases hd : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ)
    · have hn : 0 < Ideal.absNorm d :=
        Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd.1)
      have hn1 : 1 ≤ (Ideal.absNorm d : ℝ) := by exact_mod_cast hn
      have hμ : ‖(idealMoebius F d : ℂ)‖ ≤ 1 := by
        unfold idealMoebius UniqueFactorizationMonoid.moebius
        split <;> simp [Int.cast_pow]
      have hωnorm := RayUnitary.ray_character_norm_le_one F m hm ω d
      have hprod : ‖(idealMoebius F d : ℂ)‖ * ‖ω d‖ ≤ 1 := by
        nlinarith [norm_nonneg (idealMoebius F d : ℂ), norm_nonneg (ω d)]
      simp only [f, g, if_pos hd, norm_mul,
        Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
      calc
        ‖(idealMoebius F d : ℂ)‖ * ‖ω d‖ * (Ideal.absNorm d : ℝ) ^ (-s.re)
            ≤ (Ideal.absNorm d : ℝ) ^ (-s.re) := by
          simpa using mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (by positivity) _)
        _ ≤ (Ideal.absNorm d : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · simp [f, g, hd]
  have hsqrt : (U ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = U := by
    rw [← Real.rpow_natCast_mul hU0]
    norm_num
  calc
    ‖truncatedIdealInverse F ω U s‖ = ‖∑ d ∈ t, f d‖ := by
      exact congrArg norm (finsum_eq_sum_of_support_subset f hf)
    _ ≤ ∑ d ∈ t, ‖f d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ t, g d := Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ᶠ d, g d := (finsum_eq_sum_of_support_subset g hg).symm
    _ ≤ C * U := by simpa only [hsqrt] using (hbound (U ^ (2 : ℕ)) hU2).2

end DedekindZetaZeroFree.Detector
