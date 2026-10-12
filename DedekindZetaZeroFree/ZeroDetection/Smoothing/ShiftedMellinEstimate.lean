module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformWeakConvexity
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.DetectorMellinIdentity
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.GammaWeightedZeroShift
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.TruncatedIdealInverseBounds

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

open MeasureTheory Detector

private lemma shifted_inverse_entire
    (F : Type) [Field F] [NumberField F] {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (U : ℝ) :
    Differentiable ℂ (Detector.truncatedIdealInverse F ω U) := by
  classical
  let t := (ideals_bounded_norm_finite F (U ^ (2 : ℕ))).toFinset
  have he (s : ℂ) : Detector.truncatedIdealInverse F ω U s =
      ∑ d ∈ t, if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ) then
        (idealMoebius F d : ℂ) * ω d * (Ideal.absNorm d : ℂ) ^ (-s) else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro d hd
    simp only [t, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_contra hn
    have hn' : ¬ (d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ)) := by
      simpa only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn
    exact hd (by simp [hn'])
  rw [show Detector.truncatedIdealInverse F ω U = _ from funext he]
  apply Differentiable.fun_sum
  intro d hd
  by_cases hn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ U ^ (2 : ℕ)
  · simp only [if_pos hn]
    apply Differentiable.const_mul
    apply Differentiable.const_cpow differentiable_id.neg
    left
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hn.1
  · simp only [if_neg hn]
    exact differentiable_const _

theorem detector_sz_shifted_estimate
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    let A_F : ℝ := (detector_convexity_bridge F htc C₀ hC₀).choose
    (∀ ε : ℝ, 0 < ε → ∃ C_ε : ℝ, 0 < C_ε ∧
      ∀ U : ℝ, 2 ≤ U →
      ∀ (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥),
      ∀ (ω : RayClassCharacter F 𝔪) (hω : ω.IsPrimitive), ¬ ω.IsPrincipal →
        (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
        ∀ β γ : ℝ, 249 / 250 ≤ β → β ≤ 1 →
          Detector.canonicalRayHeckeL F htc 𝔪 hm ω hω
            ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
          ‖Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ))‖ ≤
            C_ε * U ^ (10 * (1 / 2 - β) + 3 / 2 + ε) * (2 + |γ|) ^ A_F) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < min (1 / 10) (1 / (A_F + 1)) →
      ∃ C : ℝ, 0 < C ∧
        ∀ U : ℝ, 2 ≤ U →
        ∀ (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥),
        ∀ (ω : RayClassCharacter F 𝔪) (hω : ω.IsPrimitive), ¬ ω.IsPrincipal →
          (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
          ∀ β γ : ℝ, 249 / 250 ≤ β → β ≤ 1 →
            Detector.canonicalRayHeckeL F htc 𝔪 hm ω hω
              ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
            |γ| ≤ 4 * U ^ ρ →
            ‖Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ))‖ ≤
              C * U ^ (-2 : ℝ)) := by
  dsimp only
  let A : ℝ := (detector_convexity_bridge F htc C₀ hC₀).choose
  have hA : 0 ≤ A := (detector_convexity_bridge F htc C₀ hC₀).choose_spec.1
  have hbridge := (detector_convexity_bridge F htc C₀ hC₀).choose_spec.2
  obtain ⟨D, hD, hd⟩ := Detector.truncatedIdealInverse_bound F
  obtain ⟨G, hG, hg⟩ := detector_sz_gamma_moments A hA
  have hfirst : ∀ ε : ℝ, 0 < ε → ∃ C_ε : ℝ, 0 < C_ε ∧
      ∀ U : ℝ, 2 ≤ U →
      ∀ (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥),
      ∀ (ω : RayClassCharacter F 𝔪) (hω : ω.IsPrimitive), ¬ ω.IsPrincipal →
        (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
        ∀ β γ : ℝ, 249 / 250 ≤ β → β ≤ 1 →
          Detector.canonicalRayHeckeL F htc 𝔪 hm ω hω
            ((β : ℂ) + Complex.I * (γ : ℂ)) = 0 →
          ‖Detector.smoothedDetector F ω U ((β : ℂ) + Complex.I * (γ : ℂ))‖ ≤
            C_ε * U ^ (10 * (1 / 2 - β) + 3 / 2 + ε) * (2 + |γ|) ^ A := by
    intro ε hε
    obtain ⟨K, hK, hk⟩ := hbridge ε hε
    refine ⟨(1 / (2 * Real.pi)) * D * K * G, by positivity, ?_⟩
    intro U hU m hm ω hω hn hnorm β γ hβ hβ1 hz
    have hUp : 0 < U := by linarith
    let s : ℂ := (β : ℂ) + Complex.I * (γ : ℂ)
    let a : ℝ := 1 / 2 - β
    let X : ℝ := U ^ (10 : ℕ)
    let L := Detector.canonicalRayHeckeL F htc m hm ω hω
    let f : ℂ → ℂ := fun v => L (s + v) * Detector.truncatedIdealInverse F ω U (s + v)
    have hsre : s.re = β := by simp [s]
    have hsim : s.im = γ := by simp [s]
    have ha : a ∈ Set.Icc (-1 / 2 : ℝ) (-124 / 250 : ℝ) := by
      constructor <;> dsimp [a] <;> linarith
    have hXp : 0 < X := by dsimp [X]; positivity
    have hL : L = (nonprincipalRayHeckeData F htc m hm ω hω hn).L := by
      simp [L, Detector.canonicalRayHeckeL, hn]
    have hf : DifferentiableOn ℂ f {v : ℂ | (-3 / 4 : ℝ) < v.re} := by
      apply DifferentiableOn.mul
      · rw [hL]
        apply (nonprincipalRayHeckeData F htc m hm ω hω hn).L_holo.comp
          ((differentiable_const s).add differentiable_id).differentiableOn
        intro v hv
        change 0 < (s + v).re
        rw [Complex.add_re, hsre]
        dsimp at hv
        linarith
      · exact ((shifted_inverse_entire F ω U).comp
          ((differentiable_const s).add differentiable_id)).differentiableOn
    have hf0 : f 0 = 0 := by simp [f, L, s, hz]
    have hbound (σ : ℝ) (hσ : σ ∈ Set.Icc a 2) (t : ℝ) :
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          (D * K * U ^ (3 / 2 + ε)) * (2 + |γ + t|) ^ A := by
      have hre : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).re = β + σ := by
        simp [hsre]
      have him : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).im = γ + t := by
        simp [hsim]
      have hr : 1 / 2 ≤ β + σ := by dsimp [a] at hσ; linarith [hσ.1]
      have hkl := (hk U hU m hm ω hω hnorm _ (by rw [hre]; linarith)
        (by rw [hre]; linarith [hσ.2])).1 hn
          (nonprincipalRayHeckeData F htc m hm ω hω hn)
      rw [← hL, him] at hkl
      have hdl := hd U hU m hm ω hω _ (by rw [hre]; exact hr)
      calc
        _ = ‖L (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ *
          ‖Detector.truncatedIdealInverse F ω U (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := norm_mul _ _
        _ ≤ (K * U ^ (1 / 2 + ε) * (2 + |γ + t|) ^ A) * (D * U) :=
          mul_le_mul hkl hdl (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [show (3 / 2 : ℝ) + ε = (1 / 2 + ε) + 1 by ring,
            Real.rpow_add hUp (1 / 2 + ε) 1, Real.rpow_one]
          ring
    have hGrowth : ∃ M B : ℝ, 0 < M ∧ 0 ≤ B ∧
        ∀ σ ∈ Set.Icc a 2, ∀ t : ℝ,
          ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 + |t|) ^ B := by
      refine ⟨D * K * U ^ (3 / 2 + ε) * (2 + |γ|) ^ A, A, by positivity, hA, ?_⟩
      intro σ hσ t
      have ht : 2 + |γ + t| ≤ (2 + |γ|) * (2 + |t|) := by
        nlinarith [abs_add_le γ t, abs_nonneg γ, abs_nonneg t,
          mul_nonneg (abs_nonneg γ) (abs_nonneg t)]
      calc
        _ ≤ (D * K * U ^ (3 / 2 + ε)) * (2 + |γ + t|) ^ A := hbound σ hσ t
        _ ≤ (D * K * U ^ (3 / 2 + ε)) * ((2 + |γ|) * (2 + |t|)) ^ A := by
          gcongr
        _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
    obtain ⟨hia, hi2, heq⟩ := gamma_zero_shift a X f ha hXp hf hf0 hGrowth
    have hmell := (detector_sz_mellin_identity F htc U hU m hm ω hω s
      (by rw [hsre]; exact hβ) (by rw [hsre]; exact hβ1)).2.2
    have hinitial (t : ℝ) : Detector.initialMellinIntegrand F htc m hm ω hω U s t =
        Complex.Gamma (2 + (t : ℂ) * Complex.I) * f (2 + (t : ℂ) * Complex.I) *
          (X : ℂ) ^ (2 + (t : ℂ) * Complex.I) := by
      dsimp [Detector.initialMellinIntegrand, f, L, X]
      rw [mul_comm Complex.I (t : ℂ)]
      ring
    rw [show Detector.initialMellinIntegrand F htc m hm ω hω U s = _ from funext hinitial,
      heq] at hmell
    obtain ⟨hgi, hgb⟩ := hg a (Or.inl (by simpa only [neg_div] using ha)) γ
    have hmajor (t : ℝ) :
        ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
          f ((a : ℂ) + (t : ℂ) * Complex.I) *
          (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (X ^ a * (D * K * U ^ (3 / 2 + ε))) *
          (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hXp]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
      calc
        _ ≤ ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
          ((D * K * U ^ (3 / 2 + ε)) * (2 + |γ + t|) ^ A) * X ^ a := by
          gcongr
          exact hbound a ⟨le_rfl, by linarith [ha.2]⟩ t
        _ = _ := by ring
    calc
      ‖Detector.smoothedDetector F ω U s‖ = (1 / (2 * Real.pi)) *
          ‖∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
            f ((a : ℂ) + (t : ℂ) * Complex.I) *
            (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [hmell, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
      _ ≤ (1 / (2 * Real.pi)) *
          ((X ^ a * (D * K * U ^ (3 / 2 + ε))) * (G * (2 + |γ|) ^ A)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
              f ((a : ℂ) + (t : ℂ) * Complex.I) *
              (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ t : ℝ, (X ^ a * (D * K * U ^ (3 / 2 + ε))) *
              (‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) :=
            integral_mono hia.norm (hgi.const_mul _) hmajor
          _ = (X ^ a * (D * K * U ^ (3 / 2 + ε))) *
              (∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |γ + t|) ^ A) :=
            integral_const_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hgb (by positivity)
      _ = _ := by
        dsimp [X, a]
        rw [← Real.rpow_natCast_mul hUp.le]
        rw [show 10 * (1 / 2 - β) + 3 / 2 + ε =
          10 * (1 / 2 - β) + (3 / 2 + ε) by ring,
          Real.rpow_add hUp (10 * (1 / 2 - β)) (3 / 2 + ε)]
        norm_num only [Nat.cast_ofNat]
        ring
  refine ⟨hfirst, ?_⟩
  intro ρ hρ hρlt
  obtain ⟨C, hC, hc⟩ := hfirst (1 / 4) (by norm_num)
  refine ⟨C * 6 ^ A, by positivity, ?_⟩
  intro U hU m hm ω hω hn hnorm β γ hβ hβ1 hz hγ
  have hUp : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hUr : 1 ≤ U ^ ρ := Real.one_le_rpow hU1 hρ.le
  have hAr : A * ρ < 1 := by
    have hlt := lt_of_lt_of_le hρlt (min_le_right _ _)
    have hp : 0 < A + 1 := by linarith
    have hh := (lt_div_iff₀ hp).mp hlt
    nlinarith
  have ht : (2 + |γ|) ^ A ≤ 6 ^ A * U ^ (A * ρ) := by
    calc
      _ ≤ (6 * U ^ ρ) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = 6 ^ A * U ^ (ρ * A) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity),
          ← Real.rpow_mul hUp.le]
      _ = _ := by rw [mul_comm ρ A]
  calc
    _ ≤ C * U ^ (10 * (1 / 2 - β) + 3 / 2 + 1 / 4) * (2 + |γ|) ^ A :=
      hc U hU m hm ω hω hn hnorm β γ hβ hβ1 hz
    _ ≤ C * U ^ (10 * (1 / 2 - β) + 3 / 2 + 1 / 4) * (6 ^ A * U ^ (A * ρ)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (C * 6 ^ A) * U ^ ((10 * (1 / 2 - β) + 3 / 2 + 1 / 4) + A * ρ) := by
      rw [Real.rpow_add hUp (10 * (1 / 2 - β) + 3 / 2 + 1 / 4) (A * ρ)]
      ring
    _ ≤ (C * 6 ^ A) * U ^ (-2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU1
      linarith

end
end DedekindZetaZeroFree
