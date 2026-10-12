module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.ReciprocalGammaFactorStripBounds

@[expose] public section

namespace DedekindZetaZeroFree

open scoped NumberField

noncomputable section

private theorem primitive_principal_modulus_top
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F))
    (η : RayClassCharacter F 𝔪) (hprim : η.IsPrimitive) (hp : η.IsPrincipal) : 𝔪 = ⊤ := by
  by_contra hm
  obtain ⟨α, hα, _, _, hcop, hne⟩ := hprim ⊤ (lt_top_iff_ne_top.mpr hm)
  exact hne (hp _ (Ideal.span_singleton_eq_bot.not.mpr hα) hcop)

private theorem order_product_growth
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 10)
    (f g : ℂ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∃ C : ℝ, ∀ s : ℂ, ‖f s‖ ≤ C * Real.exp (‖s‖ ^ (2 : ℝ)))
    (hg : ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
      ‖g s‖ ≤ A * Real.exp (B * |s.im|)) :
    ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖g s * f s‖ ≤ M * Real.exp (K * (1 + |s.im|) ^ 2) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨A * max C 0, B + 4, by positivity, by positivity, ?_⟩
  intro s hs
  have hn : ‖s‖ ≤ 2 * (1 + |s.im|) := by
    have hre : |s.re| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    nlinarith [Complex.norm_le_abs_re_add_abs_im s, abs_nonneg s.im]
  have hn2 : ‖s‖ ^ (2 : ℝ) ≤ 4 * (1 + |s.im|) ^ 2 := by
    rw [Real.rpow_two]
    nlinarith [norm_nonneg s, abs_nonneg s.im]
  have ht2 : |s.im| ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
  calc
    ‖g s * f s‖ = ‖g s‖ * ‖f s‖ := norm_mul _ _
    _ ≤ (A * Real.exp (B * |s.im|)) * (max C 0 * Real.exp (‖s‖ ^ (2 : ℝ))) := by
      apply mul_le_mul (hg s ⟨hs.1.le, hs.2.le⟩)
      · exact (hC s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      · exact norm_nonneg _
      · positivity
    _ = (A * max C 0) * Real.exp (B * |s.im| + ‖s‖ ^ (2 : ℝ)) := by rw [Real.exp_add]; ring
    _ ≤ (A * max C 0) * Real.exp ((B + 4) * (1 + |s.im|) ^ 2) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left ht2 hB]

private theorem reciprocal_strip_bound
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
        ‖heckeReciprocalCompletionFactor F 𝔪 s‖ ≤ A * Real.exp (B * |s.im|) := by
  obtain ⟨G, hG, hGs⟩ := gammaC_inverse_strip_exp_bound (-δ) (1 + δ) (by linarith)
  let q := heckeConductorScale F 𝔪
  let r := NumberField.InfinitePlace.nrComplexPlaces F
  have hq : 1 ≤ q := one_le_heckeConductorScale F 𝔪 hm
  refine ⟨q ^ (δ / 2) * G ^ r, r * Real.pi, by positivity, by positivity, ?_⟩
  intro s hs
  have hpow : ‖(q : ℂ) ^ (-s / 2)‖ ≤ q ^ (δ / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q)]
    apply Real.rpow_le_rpow_of_exponent_le hq
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith [hs.1]
  change ‖(q : ℂ) ^ (-s / 2) * ((Complex.Gammaℂ s)⁻¹) ^ r‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    ‖(q : ℂ) ^ (-s / 2)‖ * ‖(Complex.Gammaℂ s)⁻¹‖ ^ r
        ≤ q ^ (δ / 2) * (G * Real.exp (Real.pi * |s.im|)) ^ r := by
          gcongr
          exact hGs s hs
    _ = q ^ (δ / 2) * G ^ r * Real.exp ((r * Real.pi) * |s.im|) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (r : ℝ) * (Real.pi * |s.im|) = (r * Real.pi) * |s.im| by ring]
      ring

private theorem principal_prefactor_strip_bound
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
        ‖(heckeConductorScale F 𝔪 : ℂ) ^ (-s / 2) *
          (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
          ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1)‖
          ≤ A * Real.exp (B * |s.im|) := by
  obtain ⟨G, hG, hGs⟩ := gammaC_inverse_strip_exp_bound (-δ) (1 + δ) (by linarith)
  obtain ⟨J, hJ, hJs⟩ := gammaC_inverse_strip_exp_bound (1 - δ) (2 + δ) (by linarith)
  let q := heckeConductorScale F 𝔪
  let r := NumberField.InfinitePlace.nrComplexPlaces F - 1
  have hq : 1 ≤ q := one_le_heckeConductorScale F 𝔪 hm
  refine ⟨q ^ (δ / 2) * (2 * Real.pi)⁻¹ * J * G ^ r,
    (r + 1) * Real.pi, by positivity, by positivity, ?_⟩
  intro s hs
  have hpow : ‖(q : ℂ) ^ (-s / 2)‖ ≤ q ^ (δ / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q)]
    apply Real.rpow_le_rpow_of_exponent_le hq
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith [hs.1]
  have hshift : ‖(Complex.Gammaℂ (s + 1))⁻¹‖ ≤ J * Real.exp (Real.pi * |s.im|) := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      hJs (s + 1) ⟨by simpa using (show 1 - δ ≤ s.re + 1 by linarith [hs.1]),
        by simpa using (show s.re + 1 ≤ 2 + δ by linarith [hs.2])⟩
  have hnorm : ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, hnorm]
  calc
    _ ≤ q ^ (δ / 2) * (2 * Real.pi)⁻¹ * (J * Real.exp (Real.pi * |s.im|)) *
        (G * Real.exp (Real.pi * |s.im|)) ^ r := by
      gcongr
      exact hGs s hs
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have he : Real.exp (Real.pi * |s.im|) * Real.exp (r * (Real.pi * |s.im|)) =
          Real.exp ((r + 1) * Real.pi * |s.im|) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (q ^ (δ / 2) * (2 * Real.pi)⁻¹ * J * G ^ r) *
            (Real.exp (Real.pi * |s.im|) * Real.exp (r * (Real.pi * |s.im|))) := by ring
        _ = _ := by rw [he]

private theorem nonprincipal_strip_growth
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (D : NonprincipalRayHeckeData F 𝔪 η)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 10) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖nonprincipalHeckeEntireContinuation F 𝔪 η D s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨A, B, hA, hB, hg⟩ := reciprocal_strip_bound F 𝔪 hm δ hδ
  exact order_product_growth δ hδ hδle D.Λ (heckeReciprocalCompletionFactor F 𝔪)
    A B hA hB (by convert D.order_bound 1 zero_lt_one using 1 <;> norm_num) hg

private theorem principal_strip_growth
    (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (D : PrincipalRayHeckeData F 𝔪 η)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 10) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖principalHeckeEntireRegularization F 𝔪 η D s‖ ≤
          M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨A, B, hA, hB, hg⟩ := principal_prefactor_strip_bound F 𝔪 hm δ hδ
  exact order_product_growth δ hδ hδle D.E _ A B hA hB
    (by convert D.order_bound 1 zero_lt_one using 1 <;> norm_num) hg

private theorem norm_le_detector_strip
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 10)
    (k : ℕ) (hk : 1 ≤ k) (H J : ℝ) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hgr : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hb : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) → ‖f s‖ ≤ H * (2 + |s.im|) ^ k)
    (hr : ∀ s : ℂ, 1 + δ ≤ s.re → s.re ≤ 4 → ‖f s‖ ≤ J * (2 + |s.im|)) :
    ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
      ‖f s‖ ≤ (6 ^ k * H + J) * (2 + |s.im|) ^ k := by
  intro s hs hs4
  by_cases hsright : 1 + δ ≤ s.re
  · have ht : 1 ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
    have htk : 2 + |s.im| ≤ (2 + |s.im|) ^ k := by
      simpa using (pow_le_pow_right₀ ht hk : (2 + |s.im|) ^ 1 ≤ (2 + |s.im|) ^ k)
    calc
      ‖f s‖ ≤ J * (2 + |s.im|) := hr s hsright hs4
      _ ≤ J * (2 + |s.im|) ^ k := mul_le_mul_of_nonneg_left htk hJ
      _ ≤ (6 ^ k * H + J) * (2 + |s.im|) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_left (by positivity)
  · have hstrip : -δ ≤ s.re ∧ s.re ≤ 1 + δ := ⟨by linarith, (lt_of_not_ge hsright).le⟩
    have hPL := norm_le_on_closed_strip_of_polynomial_boundary δ hδ hδle k H hH f
      hf.diffContOnCl hgr hb s hstrip
    exact hPL.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hJ) (by positivity))

private theorem coherent_data_bound
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ (η : RayClassCharacter F 𝔪),
        η.IsPrimitive → ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ( (¬ η.IsPrincipal → ∀ D : NonprincipalRayHeckeData F 𝔪 η,
            ‖D.L s‖ ≤ C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) *
              (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1)) ∧
          (η.IsPrincipal → ∀ D : PrincipalRayHeckeData F 𝔪 η,
            ‖D.R s‖ ≤ C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) *
              (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1))) := by
  obtain ⟨C, hC, hnp, hp⟩ := heckeEntireRegularizations_uniform_boundaries F hF δ hδ hδle
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  let J := 4 * idealAbsoluteSum F (1 + δ)
  have hJ : 0 < J := by
    dsimp [J]
    exact mul_pos (by norm_num) (idealAbsoluteSum_converges F (1 + δ) (by linarith)).2.2.1
  refine ⟨6 ^ k * C + J, by positivity, ?_⟩
  intro 𝔪 hm η hprim s hs hs4
  have hp0 : 0 ≤ (1 : ℝ) / 2 + δ := by linarith
  have hfactor : 1 ≤ (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) :=
    Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm 𝔪); linarith) hp0
  have hcoeff : 6 ^ k * (C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ)) + J ≤
      (6 ^ k * C + J) * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hfactor hJ.le]
  constructor
  · intro hn D
    obtain ⟨hb, hr⟩ := hnp 𝔪 hm η hprim hn D
    have h := norm_le_detector_strip δ hδ hδle k (by dsimp [k]; omega)
      (C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ)) J (by positivity) hJ.le
      (nonprincipalHeckeEntireContinuation F 𝔪 η D)
      (nonprincipalHeckeEntireContinuation_differentiable F hF 𝔪 hm η D)
      (nonprincipal_strip_growth F 𝔪 hm η D δ hδ hδle) (by simpa [k] using hb) ?_ s hs hs4
    · rw [nonprincipalHeckeEntireContinuation_eq F hF 𝔪 hm η D s (by linarith)] at h
      exact h.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
    · intro z hz hz4
      have hb := hr z hz hz4
      have : idealAbsoluteSum F (1 + δ) ≤ J * (2 + |z.im|) := by
        dsimp [J]
        nlinarith [abs_nonneg z.im,
          (idealAbsoluteSum_converges F (1 + δ) (by linarith)).2.2.1]
      exact hb.trans this
  · intro hprincipal D
    have htop := primitive_principal_modulus_top F 𝔪 η hprim hprincipal
    subst 𝔪
    obtain ⟨hb, hr⟩ := hp η hprim hprincipal D
    have h := norm_le_detector_strip δ hδ hδle k (by dsimp [k]; omega)
      C J hC.le hJ.le (principalHeckeEntireRegularization F ⊤ η D)
      (principalHeckeEntireRegularization_differentiable F hF ⊤ hm η D)
      (principal_strip_growth F ⊤ hm η D δ hδ hδle) (by simpa [k] using hb)
      (by simpa [J] using hr) s hs hs4
    rw [principalHeckeEntireRegularization_eq_bridge F hF ⊤ hm η D s (by linarith)] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) hfactor) (by positivity))

theorem detector_convexity_bridge
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A_F : ℝ, 0 ≤ A_F ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ (U : ℝ), 2 ≤ U →
        ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ →
        ∀ (ω : RayClassCharacter F 𝔪), ω.IsPrimitive →
          (Ideal.absNorm 𝔪 : ℝ) ≤ C₀ * U →
          ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
            ( (¬ ω.IsPrincipal → ∀ D : NonprincipalRayHeckeData F 𝔪 ω,
                ‖D.L s‖ ≤ C * U ^ (1 / 2 + ε) * (2 + |s.im|) ^ A_F) ∧
              (ω.IsPrincipal → ∀ D : PrincipalRayHeckeData F 𝔪 ω,
                ‖D.R s‖ ≤ C * U ^ (1 / 2 + ε) * (2 + |s.im|) ^ A_F) ) := by
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  refine ⟨k, by positivity, ?_⟩
  intro ε hε
  let δ := min ε (1 / 10)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδle : δ ≤ 1 / 10 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨B, hB, hbound⟩ := coherent_data_bound F htc δ hδ hδle
  refine ⟨B * (1 + C₀) ^ ((1 : ℝ) / 2 + δ), by positivity, ?_⟩
  intro U hU 𝔪 hm ω hprim hnorm s hs hs4
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hbase : 1 + (Ideal.absNorm 𝔪 : ℝ) ≤ (1 + C₀) * U := by nlinarith
  have hconductor : B * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) ≤
      (B * (1 + C₀) ^ ((1 : ℝ) / 2 + δ)) * U ^ ((1 : ℝ) / 2 + ε) := by
    calc
      _ ≤ B * ((1 + C₀) * U) ^ ((1 : ℝ) / 2 + δ) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = (B * (1 + C₀) ^ ((1 : ℝ) / 2 + δ)) * U ^ ((1 : ℝ) / 2 + δ) := by
        rw [Real.mul_rpow (by positivity) hUp.le]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
  have hh : B * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) *
      (2 + |s.im|) ^ k ≤
        (B * (1 + C₀) ^ ((1 : ℝ) / 2 + δ)) * U ^ ((1 : ℝ) / 2 + ε) *
          (2 + |s.im|) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right hconductor (by positivity)
  obtain ⟨hnp, hp⟩ := hbound 𝔪 hm ω hprim s hs hs4
  exact ⟨fun hn D => (hnp hn D).trans hh, fun hn D => (hp hn D).trans hh⟩

end
end DedekindZetaZeroFree
