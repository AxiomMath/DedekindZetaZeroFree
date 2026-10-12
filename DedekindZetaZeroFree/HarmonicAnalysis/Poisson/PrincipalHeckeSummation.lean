module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalMellinResidues
public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalStripGrowth
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SubquadraticGrowthAndGaussianRegulation

@[expose] public section

section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter

namespace DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

 def numerator {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * (principalDiscriminant F : ℂ) ^ (-s / 2) *
    (Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) * Q s * data.E s
private lemma numerator_diff {F : Type} [Field F] [NumberField F]
    (data : PrincipalHeckeData F) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (X : ℝ) (hX : 0 < X) : Differentiable ℂ (numerator data Q X) := by
  unfold numerator
  apply Differentiable.mul _ data.E_differentiable
  apply Differentiable.mul _ hQ
  apply Differentiable.mul _ (Complex.differentiable_Gammaℂ_inv.pow _)
  exact (differentiable_id.const_cpow (by simp [hX.ne'])).mul
    ((differentiable_neg.div_const _).const_cpow
      (by simp [ne_of_gt (principalDiscriminant_pos F)]))
private lemma dslope_diff (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ] at *
  exact (Complex.differentiableOn_dslope (by simp)).mpr hf
private lemma regular_algebra (f : ℂ → ℂ) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dslope (dslope f 0) 1 s = f s / (s * (s - 1)) - (f 1 / (s - 1) + (-f 0) / s) := by
  rw [dslope_of_ne _ hs1, slope_def_field, dslope_of_ne _ hs0,
    slope_def_field, dslope_of_ne _ (by norm_num : (1 : ℂ) ≠ 0), slope_def_field]
  simp only [sub_zero, div_one]
  field_simp
  <;> ring
private lemma residues_numerator {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (data : PrincipalHeckeData F)
    (h : ℝ → ℂ) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = h 0 / 2)
    (X : ℝ) (hX : 0 < X) :
    numerator data Q X 1 = principalMellinResidueOne data Q X ∧
    -(numerator data Q X 0) = principalMellinResidueZero data h := by
  have hc := (numerator_diff data Q hQ X hX).continuous
  have ht1 : Tendsto (fun s : ℂ => numerator data Q X s / s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (numerator data Q X 1)) := by
    have H := ((hc.continuousAt.tendsto.div tendsto_id (by norm_num : (1 : ℂ) ≠ 0)).mono_left (y := 𝓝[≠] (1 : ℂ)) nhdsWithin_le_nhds)
    convert H using 1 <;> first | rfl | (norm_num <;> ring)
  have he1 : (fun s : ℂ => (s - 1) * principalMellinIntegrand data Q X s) =ᶠ[𝓝[≠] 1]
      (fun s => numerator data Q X s / s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s ≠ _ at hs
    unfold principalMellinIntegrand numerator
    field_simp [hs, sub_ne_zero.mpr hs]
  have ht0 : Tendsto (fun s : ℂ => numerator data Q X s / (s - 1))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-numerator data Q X 0)) := by
    have H := ((hc.continuousAt.tendsto.div (tendsto_id.sub tendsto_const_nhds)
      (by norm_num : (0 : ℂ) - 1 ≠ 0)).mono_left (y := 𝓝[≠] (0 : ℂ)) nhdsWithin_le_nhds)
    convert H using 1 <;> first | rfl | (norm_num <;> ring)
  have he0 : (fun s : ℂ => s * principalMellinIntegrand data Q X s) =ᶠ[𝓝[≠] 0]
      (fun s => numerator data Q X s / (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s ≠ _ at hs
    unfold principalMellinIntegrand numerator
    field_simp [hs, sub_ne_zero.mpr hs]
  exact ⟨(tendsto_nhds_unique (ht1.congr' he1.symm)
      (principalMellinIntegrand_residue_one hF data Q hQ X hX)),
    (tendsto_nhds_unique (ht0.congr' he0.symm)
      (principalMellinIntegrand_residue_zero hF data h Q hQ hQ0 X hX))⟩
private lemma integrand_growth {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (data : PrincipalHeckeData F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (a b : ℝ) (hab : a ≤ b) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ σ t : ℝ, σ ∈ Set.Icc a b → 1 ≤ |t| →
      ‖principalMellinIntegrand data (Vendor.originMellinQ h) X
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := by
  obtain ⟨CG, AG, hCG, hAG, hG⟩ := Vendor.inverse_Gammaℂ_strip_exp_bound a b
    (principalComplexPlaces F)
  obtain ⟨CH, hCH, hH⟩ := Vendor.Gammaℂ_mul_originMellinQ_rapid_decay h hh hc a b hab 0
  obtain ⟨CE, hE⟩ := data.E_growth (1 / 2) (by norm_num)
  have hCE : 0 ≤ CE := by
    have := hE 0
    simp only [norm_zero, Real.zero_rpow (by norm_num : (1 + (1 / 2 : ℝ)) ≠ 0), Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hD := (principalDiscriminant_pos F).le
  let B := 1 + max |a| |b|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpowcont : ContinuousOn (fun σ : ℝ =>
      X ^ σ * (principalDiscriminant F) ^ (-σ / 2)) (Set.Icc a b) := by
    exact ((Real.continuous_const_rpow hX.ne').mul
      ((Real.continuous_const_rpow (principalDiscriminant_pos F).ne').comp
        (by fun_prop))).continuousOn
  obtain ⟨CP, hCP⟩ := isCompact_Icc.exists_bound_of_continuousOn hpowcont
  let P := max CP 0
  have hP : 0 ≤ P := le_max_right _ _
  refine ⟨P * CG * CH * CE, AG + B ^ (3 / 2 : ℝ), by positivity, by positivity, ?_⟩
  intro σ t hσ ht
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht; linarith
  have hGamma : Complex.Gammaℂ s ≠ 0 := by
    unfold Complex.Gammaℂ
    apply mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Real.pi_ne_zero]))
    apply Complex.Gamma_ne_zero
    intro n hn
    apply ht0
    have := congrArg Complex.im hn
    simpa [hsim] using this
  have hidentity : principalMellinIntegrand data (Vendor.originMellinQ h) X s =
      (X : ℂ) ^ s * (principalDiscriminant F : ℂ) ^ (-s / 2) *
      (Complex.Gammaℂ s)⁻¹ ^ principalComplexPlaces F *
      (Complex.Gammaℂ s * Vendor.originMellinQ h s) * data.E s / (s * (s - 1)) := by
    unfold principalMellinIntegrand
    rw [show principalComplexPlaces F = (principalComplexPlaces F - 1) + 1 by
      have := principalComplexPlaces_pos F hF; omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    simp [mul_assoc, hGamma]
  have hPole : 1 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul]
    have h1 : 1 ≤ ‖s‖ := ht.trans (by simpa [hsim] using Complex.abs_im_le_norm s)
    have h2 : 1 ≤ ‖s - 1‖ := ht.trans (by simpa [hsim] using Complex.abs_im_le_norm (s - 1))
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hreal : X ^ σ * principalDiscriminant F ^ (-σ / 2) ≤ P := by
    have := hCP σ hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  have hH' : ‖Complex.Gammaℂ s * Vendor.originMellinQ h s‖ ≤ CH := by
    simpa [s] using hH σ t hσ.1 hσ.2 ht
  have hG' : ‖(Complex.Gammaℂ s)⁻¹‖ ^ principalComplexPlaces F ≤ CG * Real.exp (AG * |t|) := by
    simpa [hsim] using hG s (hsre ▸ hσ)
  have hn : ‖s‖ ≤ B * (1 + |t|) := by
    have hσabs : |σ| ≤ max |a| |b| := by
      rw [abs_le]
      exact ⟨(neg_abs_le a).trans hσ.1 |>.trans' (neg_le_neg (le_max_left _ _)),
        hσ.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    calc ‖s‖ ≤ |σ| + |t| := by simpa [s] using norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
      _ ≤ B * (1 + |t|) := by dsimp [B]; nlinarith [abs_nonneg t, le_max_left |a| |b|, abs_nonneg a]
  have hE' : ‖data.E s‖ ≤ CE * Real.exp (B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ)) := by
    apply (hE s).trans
    apply mul_le_mul_of_nonneg_left _ hCE
    apply Real.exp_le_exp.mpr
    rw [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
    calc ‖s‖ ^ (3 / 2 : ℝ) ≤ (B * (1 + |t|)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num)
      _ = _ := Real.mul_rpow hB (by positivity)
  have hExp : AG * |t| ≤ AG * (1 + |t|) ^ (3 / 2 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hAG
    exact (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.self_le_rpow_of_one_le (by linarith [abs_nonneg t]) (by norm_num))
  rw [hidentity, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos (principalDiscriminant_pos F), hsre,
    show (-s / 2).re = -σ / 2 by simp [hsre]]
  calc X ^ σ * principalDiscriminant F ^ (-σ / 2) *
        ‖(Complex.Gammaℂ s)⁻¹‖ ^ principalComplexPlaces F *
        ‖Complex.Gammaℂ s * Vendor.originMellinQ h s‖ * ‖data.E s‖ / ‖s * (s - 1)‖
      ≤ X ^ σ * principalDiscriminant F ^ (-σ / 2) *
        ‖(Complex.Gammaℂ s)⁻¹‖ ^ principalComplexPlaces F *
        ‖Complex.Gammaℂ s * Vendor.originMellinQ h s‖ * ‖data.E s‖ :=
      div_le_self (by positivity) hPole
    _ ≤ P * (CG * Real.exp (AG * |t|)) * CH *
        (CE * Real.exp (B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ))) := by
      gcongr
    _ = P * CG * CH * CE * Real.exp (AG * |t| + B ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ)) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith

theorem principalMellinIntegrand_contour_shift
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (data : PrincipalHeckeData F) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (a b : ℝ)
    (ha : -1 < a) (ha0 : a < 0) (hb : 1 < b)
    (hleft : Complex.VerticalIntegrable
      (principalMellinIntegrand data (Vendor.originMellinQ h) X) a)
    (hright : Complex.VerticalIntegrable
      (principalMellinIntegrand data (Vendor.originMellinQ h) X) b) :
    Vendor.verticalIntegral b (principalMellinIntegrand data (Vendor.originMellinQ h) X) -
      Vendor.verticalIntegral a (principalMellinIntegrand data (Vendor.originMellinQ h) X) =
        principalMellinResidueOne data (Vendor.originMellinQ h) X +
          principalMellinResidueZero data h := by
  let Q := Vendor.originMellinQ h
  have hQ := Vendor.originMellinQ_differentiable h hh hcompact
  have hQ0 := Vendor.originMellinQ_zero h hh hcompact
  have hnum := numerator_diff data Q hQ X hX
  obtain ⟨hR1, hR0⟩ := residues_numerator hF data h Q hQ hQ0 X hX
  let p : Fin 2 → ℝ := ![1, 0]
  let R : Fin 2 → ℂ := ![principalMellinResidueOne data Q X,
    principalMellinResidueZero data h]
  have hp : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at *
  have hpstrip : ∀ j, p j ∈ Set.Ioo a b := by
    intro j
    fin_cases j <;> simp [p] <;> constructor <;> linarith
  have hdiff : DifferentiableOn ℂ (principalMellinIntegrand data Q X)
      (Set.univ \ Set.range (fun j => (p j : ℂ))) := by
    intro s hs
    have h0 : s ≠ 0 := by
      intro h
      apply hs.2
      exact ⟨1, by simp [p, h]⟩
    have h1 : s ≠ 1 := by
      intro h
      apply hs.2
      exact ⟨0, by simp [p, h]⟩
    exact ((hnum s).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1))
      (mul_ne_zero h0 (sub_ne_zero.mpr h1))).differentiableWithinAt
  have hregular : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Set.univ ∧
      ∀ s ∈ Set.univ, (∀ j, s ≠ (p j : ℂ)) →
        g s = principalMellinIntegrand data Q X s - ∑ j : Fin 2, R j / (s - (p j : ℂ)) := by
    refine ⟨dslope (dslope (numerator data Q X) 0) 1,
      (dslope_diff _ (dslope_diff _ hnum 0) 1).differentiableOn, ?_⟩
    intro s hs hsp
    have h0 : s ≠ 0 := by simpa [p] using hsp 1
    have h1 : s ≠ 1 := by simpa [p] using hsp 0
    rw [regular_algebra _ s h0 h1]
    simp only [Fin.sum_univ_two, R, p, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Complex.ofReal_one, Complex.ofReal_zero, sub_zero]
    rw [hR1, ← hR0]
    rfl
  have hshift := Vendor.verticalIntegral_sub_eq_sum_residues_of_subquadratic_strip_growth
    (a := a) (b := b) (by linarith) 2 p R hp hpstrip
    (principalMellinIntegrand data Q X) Set.univ isOpen_univ (by simp) hdiff hregular
    hleft hright (integrand_growth hF data h hh hcompact X hX a b (by linarith))
  simpa [Fin.sum_univ_two, R, Q] using hshift

end DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

theorem principalMellinIntegrand_one_sub_eq_dual
    {F : Type} [Field F] [NumberField F] (data : PrincipalHeckeData F)
    (h : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : 1 < s.re) :
    principalMellinIntegrand data (Vendor.originMellinQ h) X (1 - s) =
      (X : ℂ) * (B (principalDiscriminant F) (principalComplexPlaces F) h s *
        (X : ℂ) ^ (-s) * idealCoefficientLSeries (principalCharacter F) s) := by
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h1; rw [h1] at hs; norm_num at hs
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : 1 - s ≠ 1 := by
    intro hh; exact hs0 (by linear_combination -hh)

  have hE : data.E (1 - s) = s * (s - 1) * data.Lambda s := by
    rw [data.E_eq_mul_Lambda (1 - s) h1s0 h1s1,
      ← data.Lambda_functional_equation s hs0 hs1]
    ring

  have hL : (∑' I : Ideal (𝓞 F),
      if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) =
      idealCoefficientLSeries (principalCharacter F) s := by
    rw [idealCoefficientLSeries]
    rw [show (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (principalCharacter F).toFun I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) =
        (∑' I : ↑({I : Ideal (𝓞 F) | I ≠ ⊥}),
          (principalCharacter F).toFun I.val * (Ideal.absNorm I.val : ℂ) ^ (-s))
        from rfl]
    rw [tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥})
      (fun I => (principalCharacter F).toFun I * (Ideal.absNorm I : ℂ) ^ (-s))]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥
    · simp [Set.indicator, hI]
    · simp [Set.indicator, hI, principalCharacter_apply]
  have hLam := data.Lambda_dirichlet s hs
  have hXne : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hDne : (principalDiscriminant F : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (principalDiscriminant_pos F))

  have hXpow : (X : ℂ) ^ (1 - s) = (X : ℂ) * (X : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + (-s) by ring,
      Complex.cpow_add 1 (-s) hXne, Complex.cpow_one]
  have hDpow : (principalDiscriminant F : ℂ) ^ (-(1 - s) / 2) *
      (principalDiscriminant F : ℂ) ^ (s / 2) =
      (principalDiscriminant F : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_add (-(1 - s) / 2) (s / 2) hDne]
    congr 1
    ring
  have hden : (1 - s) * ((1 - s) - 1) = s * (s - 1) := by ring
  have hdenne : (1 - s) * ((1 - s) - 1) ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  rw [principalMellinIntegrand, B]
  rw [hE, hLam, hL]
  rw [div_eq_iff hdenne]
  rw [hXpow, ← hDpow, hden]
  ring

end DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

theorem principalMellinIntegrand_eq_primal
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (data : PrincipalHeckeData F) (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : 1 < s.re) :
    principalMellinIntegrand data (Vendor.originMellinQ h) X s =
      mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries (principalCharacter F) s := by
  have hs0 : s ≠ 0 := by intro hc; rw [hc] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro hc; rw [hc] at hs; norm_num at hs
  have hD : (principalDiscriminant F : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalDiscriminant_pos F)
  have hG : Complex.Gammaℂ s ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
      (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hr : 1 ≤ principalComplexPlaces F := principalComplexPlaces_pos F hF
  have hAD : (principalDiscriminant F : ℂ) ^ (-s / 2) *
      (principalDiscriminant F : ℂ) ^ (s / 2) = 1 := by
    rw [← Complex.cpow_add _ _ hD, show -s / 2 + s / 2 = 0 by ring, Complex.cpow_zero]
  have hBC : (Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) *
      (Complex.Gammaℂ s) ^ principalComplexPlaces F = Complex.Gammaℂ s := by
    obtain ⟨n, hn⟩ : ∃ n, principalComplexPlaces F = n + 1 :=
      ⟨principalComplexPlaces F - 1, (Nat.succ_pred_eq_of_pos hr).symm⟩
    rw [hn, Nat.add_sub_cancel]
    rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hG, one_pow, one_mul]
  have hGQ : Complex.Gammaℂ s * Vendor.originMellinQ h s = mellin h s :=
    Vendor.Gammaℂ_mul_originMellinQ_eq_mellin h hh hcompact s (by linarith)
  have hZ : (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) =
      idealCoefficientLSeries (principalCharacter F) s := by
    rw [idealCoefficientLSeries]
    symm
    have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
        if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
        {I : Ideal (𝓞 F) | I ≠ ⊥} := by
      intro I hI
      by_contra heq
      simp only [Set.mem_setOf_eq, not_not] at heq
      subst I
      simpa [Function.mem_support] using hI
    calc
      (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          principalCharacter F I.val * (Ideal.absNorm I.val : ℂ) ^ (-s))
          = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
              (if I.val = ⊥ then 0 else (Ideal.absNorm I.val : ℂ) ^ (-s)) := by
            apply tsum_congr
            intro I
            simp [I.property]
      _ = ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s) :=
            tsum_subtype_eq_of_support_subset hsupp
  rw [principalMellinIntegrand]
  rw [mul_div_assoc, ← data.Lambda_eq_div s hs0 hs1, data.Lambda_dirichlet s hs]
  calc
    (X : ℂ) ^ s * (principalDiscriminant F : ℂ) ^ (-s / 2) *
        (Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) *
        Vendor.originMellinQ h s *
        ((principalDiscriminant F : ℂ) ^ (s / 2) *
          (Complex.Gammaℂ s) ^ principalComplexPlaces F *
          (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)))
        = ((X : ℂ) ^ s * Vendor.originMellinQ h s) *
            ((principalDiscriminant F : ℂ) ^ (-s / 2) *
              (principalDiscriminant F : ℂ) ^ (s / 2)) *
            ((Complex.Gammaℂ s)⁻¹ ^ (principalComplexPlaces F - 1) *
              (Complex.Gammaℂ s) ^ principalComplexPlaces F) *
            (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
          ring
    _ = ((X : ℂ) ^ s * Vendor.originMellinQ h s) * 1 * Complex.Gammaℂ s *
            (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
          rw [hAD, hBC]
    _ = (X : ℂ) ^ s * (Complex.Gammaℂ s * Vendor.originMellinQ h s) *
            (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
          ring
    _ = (X : ℂ) ^ s * mellin h s *
            (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else (Ideal.absNorm I : ℂ) ^ (-s)) := by
          rw [hGQ]
    _ = mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries (principalCharacter F) s := by
          rw [hZ]; ring

end DedekindZetaZeroFree.LargeSieve.PrincipalPoisson

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem principalPoisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) :
    let T : ℝ → ℂ := fun x => if 0 < x then
      mellinInv 2 (fun s =>
        (principalDiscriminant F : ℂ) ^ (s - 1 / 2) *
        Complex.Gammaℂ s ^ principalComplexPlaces F *
        (Complex.Gammaℂ (1 - s))⁻¹ ^ (principalComplexPlaces F - 1) *
        Vendor.originMellinQ h (1 - s)) x else 0
    Summable (fun I : Ideal (𝓞 F) =>
      ‖if I = ⊥ then (0 : ℂ) else T (X * (Ideal.absNorm I : ℝ))‖) ∧
    Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℂ) else T (X * (Ideal.absNorm I : ℝ))) ∧
    (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else h ((Ideal.absNorm I : ℝ) / X)) =
      principalPoleCoefficient F hF /
          ((Real.sqrt (principalDiscriminant F) : ℂ) *
            Complex.Gammaℂ 1 ^ principalComplexPlaces F) *
        (X : ℂ) * Vendor.originMellinH h 1 -
      (if principalComplexPlaces F = 1 then
        principalPoleCoefficient F hF * h 0 / 2 else 0) +
      (X : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        T (X * (Ideal.absNorm I : ℝ)) := by
  let data := principalHeckeData F hF
  let B₀ := B (principalDiscriminant F) (principalComplexPlaces F) h
  let T₀ := fieldTransform (principalDiscriminant F) (principalComplexPlaces F) h
  let J := principalMellinIntegrand data (Vendor.originMellinQ h) X
  let P := fun s : ℂ => mellin h s * (X : ℂ) ^ s *
    idealCoefficientLSeries (principalCharacter F) s
  let G := fun s : ℂ => B₀ s * (X : ℂ) ^ (-s) *
    idealCoefficientLSeries (principalCharacter F) s
  have ha0 : principalCharacter F ⊥ = 0 := by simp
  have ha : ∀ I : Ideal (𝓞 F), ‖principalCharacter F I‖ ≤ 1 := by
    intro I
    simp only [principalCharacter_apply]
    split_ifs <;> simp
  have hB : Complex.VerticalIntegrable B₀ (3 / 2) := by
    simpa [Complex.VerticalIntegrable] using
      B_inverse_integrable (principalDiscriminant F) (principalComplexPlaces F) h
        (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF) hh hcompact
        (3 / 2) 1 (by norm_num) (by norm_num)
  have hT : ∀ x : ℝ, 0 < x → T₀ x = mellinInv (3 / 2) B₀ x := by
    intro x hx
    simp only [T₀, fieldTransform, if_pos hx]
    exact (B_mellinInv_eq (principalDiscriminant F) (principalComplexPlaces F) h
      (principalDiscriminant_pos F) (principalComplexPlaces_pos F hF) hh hcompact
      (3 / 2) x (by norm_num) hx).symm
  obtain ⟨hnorm, hsum, hG, hdual⟩ := idealMellin_dual_interchange
    (principalCharacter F) ha0 ha B₀ T₀ (c := 3 / 2) (X := X) (q := 1)
    (by norm_num) hX (by norm_num) hB hT
  simp only [div_one] at hnorm hsum hG hdual
  have hnorm' : Summable (fun I : Ideal (𝓞 F) =>
      ‖if I = ⊥ then (0 : ℂ) else T₀ (X * (Ideal.absNorm I : ℝ))‖) := by
    have hn : Summable ((fun I : Ideal (𝓞 F) =>
        ‖T₀ (X * (Ideal.absNorm I : ℝ))‖) ∘
        (Subtype.val : {I : Ideal (𝓞 F) | I ≠ ⊥} → Ideal (𝓞 F))) :=
      hnorm.congr fun I => by simp [I.property]
    have hi := (summable_subtype_iff_indicator).mp hn
    exact hi.congr fun I => by
      by_cases hI : I = ⊥ <;> simp [Set.indicator_apply, hI]
  have hsum' : Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℂ) else T₀ (X * (Ideal.absNorm I : ℝ))) := by
    have hn : Summable ((fun I : Ideal (𝓞 F) => T₀ (X * (Ideal.absNorm I : ℝ))) ∘
        (Subtype.val : {I : Ideal (𝓞 F) | I ≠ ⊥} → Ideal (𝓞 F))) :=
      hsum.congr fun I => by simp [I.property]
    have hi := (summable_subtype_iff_indicator).mp hn
    exact hi.congr fun I => by
      by_cases hI : I = ⊥ <;> simp [Set.indicator_apply, hI]
  have htsum : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      principalCharacter F I.val * T₀ (X * (Ideal.absNorm I.val : ℝ))) =
      ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else T₀ (X * (Ideal.absNorm I : ℝ)) := by
    have hs : Function.support (fun I : Ideal (𝓞 F) =>
        if I = ⊥ then (0 : ℂ) else T₀ (X * (Ideal.absNorm I : ℝ))) ⊆
        {I : Ideal (𝓞 F) | I ≠ ⊥} := by
      intro I hI
      by_contra heq
      simp only [Set.mem_setOf_eq, not_not] at heq
      subst I
      simpa [Function.mem_support] using hI
    calc
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          if I.val = ⊥ then 0 else T₀ (X * (Ideal.absNorm I.val : ℝ)) := by
        apply tsum_congr
        intro I
        simp [I.property]
      _ = _ := tsum_subtype_eq_of_support_subset hs
  have hprimalLine : ∀ t : ℝ, J (2 + t * Complex.I) = P (2 + t * Complex.I) := by
    intro t
    exact PrincipalPoisson.principalMellinIntegrand_eq_primal hF data h hh hcompact X hX
      _ (by norm_num)
  have hdualLine : ∀ t : ℝ,
      J (1 - ((3 / 2 : ℂ) + t * Complex.I)) =
        (X : ℂ) * G ((3 / 2 : ℂ) + t * Complex.I) := by
    intro t
    exact PrincipalPoisson.principalMellinIntegrand_one_sub_eq_dual data h X hX
      _ (by norm_num)
  have hright : Complex.VerticalIntegrable J 2 := by
    exact (idealMellin_verticalIntegrable (principalCharacter F) ha0 ha hh hcompact
      hX (by norm_num : (1 : ℝ) < 2)).congr
      (Filter.Eventually.of_forall fun t => (hprimalLine t).symm)
  have hleft : Complex.VerticalIntegrable J (-1 / 2) := by
    have hint := (hG.const_mul (X : ℂ)).comp_neg
    apply hint.congr
    filter_upwards [] with t
    change (X : ℂ) * G (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * Complex.I) =
      J ((-1 / 2 : ℝ) + t * Complex.I)
    have heq := hdualLine (-t)
    push_cast at heq ⊢
    rw [← heq]
    congr 1
    ring
  have hsource : (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
      h ((Ideal.absNorm I : ℝ) / X)) = Vendor.verticalIntegral 2 J := by
    have hm := idealMellin_finsum_eq_verticalIntegral (principalCharacter F) ha0 ha
      hh hcompact hX (by norm_num : (1 : ℝ) < 2)
    have hp : Vendor.verticalIntegral 2 P = Vendor.verticalIntegral 2 J := by
      unfold Vendor.verticalIntegral
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t => (hprimalLine t).symm
    have hw : idealMellinWeight (principalCharacter F) h X =
        fun I => if I = ⊥ then 0 else h ((Ideal.absNorm I : ℝ) / X) := by
      funext I
      by_cases hI : I = ⊥ <;> simp [idealMellinWeight, hI]
    rw [hw] at hm
    exact hm.trans hp
  have htarget : Vendor.verticalIntegral (-1 / 2) J =
      (X : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        T₀ (X * (Ideal.absNorm I : ℝ)) := by
    have href := Vendor.verticalIntegral_one_sub (3 / 2) J
    have hc : (1 - (3 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [hc] at href
    rw [← href]
    have heq : Vendor.verticalIntegral (3 / 2) (fun s => J (1 - s)) =
        Vendor.verticalIntegral (3 / 2) (fun s => (X : ℂ) * G s) := by
      unfold Vendor.verticalIntegral
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hdualLine t
    rw [heq, Vendor.verticalIntegral_const_mul _ _ G hG, hdual, htsum]
  have hshift := PrincipalPoisson.principalMellinIntegrand_contour_shift
    hF data h hh hcompact X hX (-1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) hleft hright
  have hres : principalMellinResidueOne data (Vendor.originMellinQ h) X +
      principalMellinResidueZero data h =
        principalPoleCoefficient F hF /
          ((Real.sqrt (principalDiscriminant F) : ℂ) *
            Complex.Gammaℂ 1 ^ principalComplexPlaces F) *
          (X : ℂ) * Vendor.originMellinH h 1 -
        (if principalComplexPlaces F = 1 then
          principalPoleCoefficient F hF * h 0 / 2 else 0) := by
    simp only [principalMellinResidueOne, principalMellinResidueZero,
      Vendor.originMellinH, principalPoleCoefficient, data]
    split_ifs <;> ring
  change Summable (fun I : Ideal (𝓞 F) =>
      ‖if I = ⊥ then (0 : ℂ) else T₀ (X * (Ideal.absNorm I : ℝ))‖) ∧
    Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℂ) else T₀ (X * (Ideal.absNorm I : ℝ))) ∧ _
  refine ⟨hnorm', hsum', ?_⟩
  rw [hsource]
  change Vendor.verticalIntegral 2 J = _
  change Vendor.verticalIntegral 2 J =
    (principalPoleCoefficient F hF /
        ((Real.sqrt (principalDiscriminant F) : ℂ) *
          Complex.Gammaℂ 1 ^ principalComplexPlaces F) *
        (X : ℂ) * Vendor.originMellinH h 1 -
      (if principalComplexPlaces F = 1 then
        principalPoleCoefficient F hF * h 0 / 2 else 0)) +
      (X : ℂ) * ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
        T₀ (X * (Ideal.absNorm I : ℝ))
  rw [← hres]
  rw [htarget] at hshift
  exact (sub_eq_iff_eq_add).mp hshift

end DedekindZetaZeroFree.LargeSieve

end

end
