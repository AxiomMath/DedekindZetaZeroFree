module

public import DedekindZetaZeroFree.LFunctions.Hecke.EntireRegularizations
public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds
public import DedekindZetaZeroFree.Analysis.Gamma.ShiftAndReflectedRatioBounds

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

private lemma principal_E_reflection (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η) :
    ∀ s, D.E s = D.E (1-s) := by
  have he : ∀ s : ℂ, 0 < s.re → s ≠ 1 → D.E s = s*(s-1)*D.Λ s := by
    intro s hs hs1
    rw [D.E_eq s hs, D.regularized s hs hs1, D.completed s hs hs1]
    ring
  have hf : Differentiable ℂ (fun s : ℂ => D.E (1-s)) :=
    D.E_entire.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have eqn := (D.E_entire.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hf.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ (1/2 : ℂ))
  have hn : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ nhds (1/2 : ℂ) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    · norm_num
  have hh : D.E =ᶠ[nhds (1/2 : ℂ)] (fun s => D.E (1-s)) := by
    filter_upwards [hn] with s hs
    have hs0 : s ≠ 0 := by intro h; subst s; simp at hs
    have hs1 : s ≠ 1 := by intro h; subst s; simp at hs
    have ht : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2]
    have ht1 : 1-s ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    rw [he s hs.1 hs1, he (1-s) ht ht1, D.reflection s hs0 hs1]
    ring
  intro s
  exact eqn hh (Set.mem_univ s)

private lemma principal_prefactor (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (s : ℂ) :
    s * ((heckeConductorScale F m : ℂ) ^ (-s / 2) *
      (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s + 1))⁻¹ *
      ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1)) =
    heckeReciprocalCompletionFactor F m s := by
  have hr := one_le_nrComplexPlaces_of_totallyComplex F hF
  have hg : (Complex.Gammaℂ s)⁻¹ =
      s * (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (Complex.Gammaℂ (s+1))⁻¹ := by
    simp only [Complex.Gammaℂ_def, mul_inv_rev]
    rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
    have hp : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hc : (2 * (Real.pi : ℂ)) ^ (-(s+1)) =
        (2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ))⁻¹ := by
      rw [show -(s+1) = -s + (-1 : ℂ) by ring, Complex.cpow_add _ _ hp]
      simp only [Complex.cpow_neg_one, mul_inv_rev]
    rw [hc]
    push_cast
    field_simp
  unfold heckeReciprocalCompletionFactor
  conv_rhs => rw [← Nat.sub_add_cancel hr, pow_succ]
  rw [hg]
  ring

private lemma completion_ratio_norm (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (δ : ℝ) (s : ℂ) (hs : s.re = -δ) :
    ‖heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)‖ =
      heckeConductorScale F m ^ ((1:ℝ)/2+δ) *
      ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ^
        NumberField.InfinitePlace.nrComplexPlaces F := by
  have hQ : 0 < heckeConductorScale F m := lt_of_lt_of_le zero_lt_one (one_le_heckeConductorScale F m hm)
  have hc : (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) =
      (heckeConductorScale F m : ℂ) := by unfold heckeConductorScale; rw [Complex.ofReal_mul]; norm_cast
  unfold heckeReciprocalCompletionFactor heckeCompletionFactor
  rw [hc]
  simp only [norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  rw [show (-s/2).re = δ/2 by simp [hs],
    show ((1-s)/2).re = (1+δ)/2 by simp [hs]]
  rw [show (1:ℝ)/2+δ = δ/2 + (1+δ)/2 by ring, Real.rpow_add hQ, mul_pow]
  ring

private lemma nonprincipal_left_formula (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
    (D : NonprincipalRayHeckeData F m η) (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : s.re = -δ) :
    nonprincipalHeckeEntireContinuation F m η D s =
      D.W * (heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)) *
        (∑' I : Ideal (𝓞 F), (starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-(1-s))) := by
  have ht : 1 < (1-s).re := by simp [hs]; linarith
  have hd := (conjugateHeckeDirichlet_right_edge F (1+δ) (by linarith) m hm η (1-s) (by simp [hs])).1.hasSum
  have he := hd.mul_left (heckeCompletionFactor F m (1-s))
  have hx := (D.dual_series (1-s) ht).unique he
  rw [nonprincipalHeckeEntireContinuation, D.reflection, hx]
  ring

private lemma principal_left_formula (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hs : s.re = -δ) :
    principalHeckeEntireRegularization F m η D s =
      (s-1) * (heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)) * D.L (1-s) := by
  have ht : 0 < (1-s).re := by simp [hs]; linarith
  have ht1 : 1-s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [hs] at hr
    linarith
  rw [principalHeckeEntireRegularization, principal_E_reflection F m η D s,
    D.E_eq (1-s) ht, D.regularized (1-s) ht ht1]
  have hp := principal_prefactor F hF m s
  linear_combination (s-1) * heckeCompletionFactor F m (1-s) * D.L (1-s) * hp

private lemma left_ratio_bound (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖heckeReciprocalCompletionFactor F m s * heckeCompletionFactor F m (1-s)‖ ≤
      ((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F) := by
  rw [completion_ratio_norm F m hm δ s hs]
  have hA : 0 ≤ ((|NumberField.discr F| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (NumberField.discr F)
  rw [heckeConductorScale, Real.mul_rpow hA (Nat.cast_nonneg _)]
  have hx := pow_le_pow_left₀ (norm_nonneg _) (hb s hs) (NumberField.InfinitePlace.nrComplexPlaces F)
  calc
    _ ≤ (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ)) *
          (K*(2+|s.im|)^2)^NumberField.InfinitePlace.nrComplexPlaces F :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

private lemma principal_strip_bound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (η : RayClassCharacter F (⊤ : Ideal (𝓞 F)))
    (D : PrincipalRayHeckeData F ⊤ η) (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : 1+δ ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖principalHeckeEntireRegularization F ⊤ η D s‖ ≤ 4*idealAbsoluteSum F (1+δ)*(2+|s.im|) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; subst s; simp at hs; linarith
  rw [principalHeckeEntireRegularization_eq F hF ⊤ top_ne_bot η D s hs0 hs1, norm_mul]
  have hb := heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) ⊤ top_ne_bot η s hs (D.L s)
    (D.series s (by linarith))
  have hn : ‖s-1‖ ≤ 4*(2+|s.im|) := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
        rw [abs_of_nonneg (by linarith : 0 ≤ s.re-1)]
        nlinarith [abs_nonneg s.im]
  calc
    _ ≤ (4*(2+|s.im|))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul hn hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma nonprincipal_strip_bound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : RayClassCharacter F m) (D : NonprincipalRayHeckeData F m η)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hs : 1+δ ≤ s.re) :
    ‖nonprincipalHeckeEntireContinuation F m η D s‖ ≤ idealAbsoluteSum F (1+δ) := by
  rw [nonprincipalHeckeEntireContinuation_eq F hF m hm η D s (by linarith)]
  exact heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) m hm η s hs (D.L s)
    (D.series s (by linarith))

private lemma nonprincipal_left_bound (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (η : RayClassCharacter F m)
    (D : NonprincipalRayHeckeData F m η) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖nonprincipalHeckeEntireContinuation F m η D s‖ ≤
      (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      idealAbsoluteSum F (1+δ)) *
      (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F) := by
  rw [nonprincipal_left_formula F m hm η D δ hδ s hs, norm_mul, norm_mul, D.root_norm, one_mul]
  have hd := (conjugateHeckeDirichlet_right_edge F (1+δ) (by linarith) m hm η (1-s) (by simp [hs])).2
  have hx := left_ratio_bound F m hm δ K hδ hK hb s hs
  calc
    _ ≤ _ * idealAbsoluteSum F (1+δ) := mul_le_mul hx hd (norm_nonneg _) (by positivity)
    _ = _ := by ring

private lemma principal_left_bound (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (η : RayClassCharacter F (⊤ : Ideal (𝓞 F))) (D : PrincipalRayHeckeData F ⊤ η)
    (δ K : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/10) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖principalHeckeEntireRegularization F ⊤ η D s‖ ≤
      (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      idealAbsoluteSum F (1+δ)) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F+1) := by
  rw [principal_left_formula F hF ⊤ η D δ hδ s hs, norm_mul, norm_mul]
  have hx := left_ratio_bound F ⊤ top_ne_bot δ K hδ hK hb s hs
  simp only [Ideal.absNorm_top, Nat.cast_one, Real.one_rpow, mul_one] at hx
  have hd := heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) ⊤ top_ne_bot η (1-s)
    (by simp [hs]) (D.L (1-s)) (D.series (1-s) (by simp [hs]; linarith))
  have hn : ‖s-1‖ ≤ 2+|s.im| := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hs]
        rw [abs_of_nonpos (by linarith : -δ-1 ≤ 0)]
        linarith
  calc
    _ ≤ ((2+|s.im|)*(_))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul (mul_le_mul hn hx (norm_nonneg _) (by positivity)) hd (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem heckeEntireRegularizations_uniform_boundaries
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (δ : ℝ) (hδ : 0 < δ) (hδ_upper : δ ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
          (hprim : η.IsPrimitive) (hnp : ¬ η.IsPrincipal)
          (D : NonprincipalRayHeckeData F 𝔪 η),
        (∀ (s : ℂ), (s.re = -δ ∨ s.re = 1 + δ) →
          ‖nonprincipalHeckeEntireContinuation F 𝔪 η D s‖ ≤
            C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) *
              (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1)) ∧
        (∀ (s : ℂ), 1 + δ ≤ s.re → s.re ≤ 4 →
          ‖nonprincipalHeckeEntireContinuation F 𝔪 η D s‖ ≤
            idealAbsoluteSum F (1 + δ))) ∧
      (∀ (η : RayClassCharacter F (⊤ : Ideal (𝓞 F)))
          (hprim : η.IsPrimitive) (hp : η.IsPrincipal)
          (D : PrincipalRayHeckeData F ⊤ η),
        (∀ (s : ℂ), (s.re = -δ ∨ s.re = 1 + δ) →
          ‖principalHeckeEntireRegularization F ⊤ η D s‖ ≤
            C * (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1)) ∧
        (∀ (s : ℂ), 1 + δ ≤ s.re → s.re ≤ 4 →
          ‖principalHeckeEntireRegularization F ⊤ η D s‖ ≤
            4 * idealAbsoluteSum F (1 + δ) * (2 + |s.im|))) := by
  obtain ⟨K, hK, hb⟩ := gammaC_reflected_ratio_left_bound δ hδ hδ_upper
  let B := idealAbsoluteSum F (1+δ)
  have hB : 0 < B := (idealAbsoluteSum_converges F (1+δ) (by linarith)).2.2.1
  let A := (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) *
    K ^ NumberField.InfinitePlace.nrComplexPlaces F * B)
  let C := max A (4*B)
  have hC4 : 4*B ≤ C := le_max_right _ _
  have hCA : A ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 4*B) hC4
  have hBC : B ≤ C := (by linarith : B ≤ 4*B).trans hC4
  have hH (s : ℂ) : 1 ≤ 2+|s.im| := by linarith [abs_nonneg s.im]
  have hHpow (s : ℂ) : 1 ≤ (2+|s.im|)^(2*NumberField.InfinitePlace.nrComplexPlaces F+1) :=
    one_le_pow₀ (hH s)
  have hHinc (s : ℂ) : (2+|s.im|)^(2*NumberField.InfinitePlace.nrComplexPlaces F) ≤
      (2+|s.im|)^(2*NumberField.InfinitePlace.nrComplexPlaces F+1) := by
    exact pow_le_pow_right₀ (hH s) (Nat.le_succ _)
  have hHbase (s : ℂ) : 2+|s.im| ≤ (2+|s.im|)^(2*NumberField.InfinitePlace.nrComplexPlaces F+1) := by
    simpa using pow_le_pow_right₀ (hH s) (by omega : 1 ≤ 2*NumberField.InfinitePlace.nrComplexPlaces F+1)
  refine ⟨C, hC, ?_, ?_⟩
  · intro m hm η hprim hnp D
    have hM : 1 ≤ (1+(Ideal.absNorm m : ℝ)) ^ ((1:ℝ)/2+δ) :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (Ideal.absNorm m) (α := ℝ)]) (by linarith)
    refine ⟨?_, fun s hs _ => nonprincipal_strip_bound F hF m hm η D δ hδ s hs⟩
    intro s hs
    rcases hs with hs | hs
    · have hx := nonprincipal_left_bound F m hm η D δ K hδ hK.le hb s hs
      change ‖nonprincipalHeckeEntireContinuation F m η D s‖ ≤ A * _ * _ at hx
      have hMp : (Ideal.absNorm m : ℝ)^((1:ℝ)/2+δ) ≤
          (1+(Ideal.absNorm m : ℝ))^((1:ℝ)/2+δ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
      exact hx.trans (mul_le_mul
        (mul_le_mul hCA hMp (by positivity) hC.le) (hHinc s) (by positivity) (by positivity))
    · have hx := nonprincipal_strip_bound F hF m hm η D δ hδ s hs.ge
      change ‖nonprincipalHeckeEntireContinuation F m η D s‖ ≤ B at hx
      calc
        _ ≤ C := hx.trans hBC
        _ ≤ C * (1+(Ideal.absNorm m : ℝ))^((1:ℝ)/2+δ) := le_mul_of_one_le_right hC.le hM
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (hHpow s)
  · intro η hprim hp D
    refine ⟨?_, principal_strip_bound F hF η D δ hδ⟩
    intro s hs
    rcases hs with hs | hs
    · exact (principal_left_bound F hF η D δ K hδ hδ_upper hK.le hb s hs).trans
        (mul_le_mul_of_nonneg_right hCA (by positivity))
    · have hx := principal_strip_bound F hF η D δ hδ s hs.ge (by linarith)
      exact hx.trans (mul_le_mul hC4 (hHbase s) (by positivity) hC.le)

end
end DedekindZetaZeroFree
