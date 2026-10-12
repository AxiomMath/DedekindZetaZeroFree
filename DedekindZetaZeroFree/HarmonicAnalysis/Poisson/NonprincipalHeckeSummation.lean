module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses
public import DedekindZetaZeroFree.Analysis.Gamma.ReciprocalStripGrowth
public import DedekindZetaZeroFree.LFunctions.Hecke.IdealCoefficientMellinSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.InverseMellinRepresentation
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterFiniteOrder
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SubquadraticGrowthAndGaussianRegulation

@[expose] public section

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

private lemma cpow_strip_bound (Y : ℝ) (hY : 0 < Y) (c a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Set.Icc a b →
      ‖(Y : ℂ) ^ ((c : ℂ) * s)‖ ≤ B := by
  have hd : Differentiable ℂ (fun s : ℂ => (Y : ℂ) ^ ((c : ℂ) * s)) :=
    ((differentiable_id.const_mul (c : ℂ))).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hd.continuous.comp Complex.continuous_ofReal).norm.continuousOn)
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  have he : ‖(Y : ℂ) ^ ((c : ℂ) * s)‖ =
      ‖(Y : ℂ) ^ ((c : ℂ) * (s.re : ℂ))‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY,
      Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp
  rw [he]
  have hb := hB s.re hs
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
  exact hb.trans (le_max_left _ _)

private lemma Gammaℂ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · intro h0
    rw [Complex.Gamma_eq_zero_iff] at h0
    obtain ⟨m, hm⟩ := h0
    exact hs (by rw [hm]; simp)

def mellinIntegrand {F : Type} [Field F] [NumberField F]
    {m : Ideal (𝓞 F)} {η : DedekindZetaZeroFree.RayClassCharacter F m}
    (w : EntireHeckeWitness η) (h : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  w.Λ s *
    ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (-s / 2)) *
    ((Complex.Gammaℂ s)⁻¹) ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
    Vendor.originMellinQ h s * (X : ℂ) ^ s

theorem mellinIntegrand_regularity
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (w : EntireHeckeWitness η)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (a b : ℝ) :
    Differentiable ℂ (mellinIntegrand w h X) ∧
      ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
        ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
          ‖mellinIntegrand w h X ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := by
  let Y : ℝ := (|NumberField.discr F| : ℤ) * (Ideal.absNorm m : ℝ)
  have hY : 0 < Y := by
    dsimp [Y]
    apply mul_pos
    · exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero F)
    · exact_mod_cast Nat.pos_of_ne_zero (fun h0 => hm (Ideal.absNorm_eq_zero_iff.mp h0))
  have hcast : (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) = (Y : ℂ) := by
    dsimp [Y]; simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]
  constructor
  · unfold mellinIntegrand
    rw [hcast]
    exact (((w.differentiable.mul
      (((differentiable_id.neg).div_const 2).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).mul
      (Complex.differentiable_Gammaℂ_inv.pow _)).mul
      (Vendor.originMellinQ_differentiable h hh hcompact)).mul
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')))
  · by_cases hab : a ≤ b
    swap
    · refine ⟨0, 0, le_rfl, le_rfl, fun σ t hσ ht => ?_⟩
      exact (hab (hσ.1.trans hσ.2)).elim
    obtain ⟨B, hB, hboundB⟩ := cpow_strip_bound Y hY (-1 / 2) a b
    obtain ⟨E, hE, hboundE⟩ := cpow_strip_bound X hX 1 a b
    obtain ⟨G, A, hG, hA, hboundG⟩ :=
      Vendor.inverse_Gammaℂ_strip_exp_bound a b
        (NumberField.InfinitePlace.nrComplexPlaces F - 1 + 1)
    obtain ⟨H, hH, hboundH⟩ :=
      Vendor.Gammaℂ_mul_originMellinQ_rapid_decay h hh hcompact a b hab 0
    obtain ⟨L, hboundL⟩ := w.growth (1 / 2) (by norm_num)
    let R : ℝ := 1 + |a| + |b|
    have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a, abs_nonneg b]
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    refine ⟨max L 0 * B * G * H * E, R ^ (3 / 2 : ℝ) + A, by positivity,
      by positivity, ?_⟩
    intro σ t hσ ht
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    have hsre : s.re = σ := by simp [s]
    have hsim : s.im = t := by simp [s]
    have hsmem : s.re ∈ Set.Icc a b := by rwa [hsre]
    have hg0 : Complex.Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_im_ne_zero (by
      rw [hsim]; intro h0; simp [h0] at ht; linarith)
    have hsource : ‖Vendor.originMellinQ h s‖ ≤ ‖(Complex.Gammaℂ s)⁻¹‖ * H := by
      have heq : Vendor.originMellinQ h s = (Complex.Gammaℂ s)⁻¹ *
          (Complex.Gammaℂ s * Vendor.originMellinQ h s) := by
        rw [← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
      rw [heq, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [s] using hboundH σ t hσ.1 hσ.2 ht
    have hnorms : ‖s‖ ≤ R * (1 + |t|) := by
      have habs : |σ| ≤ |a| + |b| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le a, hσ.1, abs_nonneg b]
        · linarith [le_abs_self b, hσ.2, abs_nonneg a]
      have hn := Complex.norm_le_abs_re_add_abs_im s
      rw [hsre, hsim] at hn
      have : |a| + |b| + |t| ≤ R * (1 + |t|) := by
        dsimp [R]; nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg t]
      exact (hn.trans (by linarith : |σ| + |t| ≤ |a| + |b| + |t|)).trans this
    have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hup : |t| ≤ (1 + |t|) ^ (3 / 2 : ℝ) := by
      calc |t| ≤ 1 + |t| := by linarith
        _ = (1 + |t|) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 + |t|) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
    have hpower : ‖s‖ ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ) := by
      calc ‖s‖ ^ (3 / 2 : ℝ) ≤ (R * (1 + |t|)) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hnorms (by norm_num)
        _ = _ := Real.mul_rpow hR0 (by positivity)
    have hL : ‖w.Λ s‖ ≤ max L 0 *
        Real.exp (R ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ)) := by
      have hL0 : ‖w.Λ s‖ ≤ L * Real.exp (‖s‖ ^ (3 / 2 : ℝ)) := by
        convert hboundL s using 1 <;> norm_num
      exact hL0.trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr hpower)
        (Real.exp_nonneg _) (le_max_right _ _))
    have hB' : ‖(Y : ℂ) ^ (-s / 2)‖ ≤ B := by
      convert hboundB s hsmem using 1 <;> congr 2 <;> push_cast <;> ring
    have hE' : ‖(X : ℂ) ^ s‖ ≤ E := by simpa using hboundE s hsmem
    have hG' := hboundG s hsmem
    rw [hsim] at hG'
    have hsmall : ‖(Complex.Gammaℂ s)⁻¹‖ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
        ‖Vendor.originMellinQ h s‖ ≤ G * Real.exp (A * |t|) * H := by
      calc _ ≤ ‖(Complex.Gammaℂ s)⁻¹‖ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
            (‖(Complex.Gammaℂ s)⁻¹‖ * H) :=
          mul_le_mul_of_nonneg_left hsource (by positivity)
        _ = ‖(Complex.Gammaℂ s)⁻¹‖ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1 + 1) * H := by
          rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hG' hH.le
    have hprod : ‖mellinIntegrand w h X s‖ ≤
        (max L 0 * Real.exp (R ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ))) *
          B * (G * Real.exp (A * |t|) * H) * E := by
      unfold mellinIntegrand
      rw [hcast, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
      rw [mul_assoc (‖w.Λ s‖ * _) _ _]
      apply mul_le_mul _ hE' (norm_nonneg _) (by positivity)
      exact mul_le_mul (mul_le_mul hL hB' (norm_nonneg _) (by positivity))
        hsmall (by positivity) (by positivity)
    calc ‖mellinIntegrand w h X s‖ ≤ _ := hprod
      _ = (max L 0 * B * G * H * E) *
          Real.exp (R ^ (3 / 2 : ℝ) * (1 + |t|) ^ (3 / 2 : ℝ) + A * |t|) := by
        rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have := mul_le_mul_of_nonneg_left hup hA
        nlinarith)) (by positivity)

end DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

private lemma reflection_powers (D q X : ℝ) (hD : 0 < D) (hq : 0 < q)
    (hX : 0 < X) (s : ℂ) :
    ((D : ℂ) * (q : ℂ)) ^ (s / 2) *
      ((D : ℂ) * (q : ℂ)) ^ (-(1 - s) / 2) * (X : ℂ) ^ (1 - s) =
    ((X : ℂ) / (Real.sqrt q : ℂ)) * (D : ℂ) ^ (s - 1 / 2) *
      ((X / q : ℝ) : ℂ) ^ (-s) := by
  have hDq : (D : ℂ) * (q : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne') (Complex.ofReal_ne_zero.mpr hq.ne')
  have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hXne : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hhalf : (q : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt q : ℂ)⁻¹ := by
    rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hq.le]
    norm_num
  rw [← Complex.cpow_add _ _ hDq,
    show s / 2 + -(1 - s) / 2 = s - 1 / 2 by ring,
    Complex.mul_cpow_ofReal_nonneg hD.le hq.le,
    show (1 - s : ℂ) = 1 + -s by ring,
    Complex.cpow_add _ _ hXne, Complex.cpow_one,
    show (s - 1 / 2 : ℂ) = s + -(1 / 2) by ring,
    Complex.cpow_add _ _ hqne, hhalf, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX.le hq.le,
    Complex.cpow_neg (q : ℂ) s]
  simp only [div_inv_eq_mul, div_eq_mul_inv, inv_inv]
  ring

private lemma reflected_integrand_eq
    {F : Type} [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (w : EntireHeckeWitness η)
    (h : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : 1 < s.re) :
    mellinIntegrand w h X (1 - s) =
      (w.W * (X : ℂ) / (Real.sqrt (Ideal.absNorm m : ℝ) : ℂ)) *
        (B ((|NumberField.discr F| : ℤ) : ℝ)
          (NumberField.InfinitePlace.nrComplexPlaces F) h s *
        ((X / (Ideal.absNorm m : ℝ) : ℝ) : ℂ) ^ (-s) *
        idealCoefficientLSeries (fun I => (starRingEnd ℂ) (η I)) s) := by
  have hD : 0 < ((|NumberField.discr F| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero F)
  have hq : 0 < (Ideal.absNorm m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hm)
  have hL : w.Λdual s = heckeCompletionFactor F m s *
      idealCoefficientLSeries (fun I => (starRingEnd ℂ) (η I)) s := by
    rw [← (w.hasSum_dual s hs).tsum_eq, tsum_mul_left, idealCoefficientLSeries]
    congr 1
    have hT := tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥})
      (fun I => (starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s))
    calc
      _ = ∑' I : Ideal (𝓞 F), ({I : Ideal (𝓞 F) | I ≠ ⊥}).indicator
          (fun J => (starRingEnd ℂ) (η J) * (Ideal.absNorm J : ℂ) ^ (-s)) I := by
        apply tsum_congr
        intro I
        by_cases hI : I = ⊥
        · simp [Set.indicator, hI, RayOperations.map_bot]
        · simp [Set.indicator, hI]
      _ = _ := hT.symm
  rw [mellinIntegrand, w.functionalEquation,
    show (1 - (1 - s) : ℂ) = s by ring, hL, heckeCompletionFactor, B]
  have hp := reflection_powers ((|NumberField.discr F| : ℤ) : ℝ)
    (Ideal.absNorm m : ℝ) X hD hq hX s
  simp only [Complex.ofReal_intCast, Complex.ofReal_natCast] at hp ⊢
  calc
    _ = w.W *
        ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (-(1 - s) / 2) *
          (X : ℂ) ^ (1 - s)) *
        (Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (Complex.Gammaℂ (1 - s))⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
          Vendor.originMellinQ h (1 - s)) *
        idealCoefficientLSeries (fun I => (starRingEnd ℂ) (η I)) s := by ring
    _ = _ := by rw [hp]; ring

theorem mellinIntegrand_reflection_dual
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (w : EntireHeckeWitness η)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (c : ℝ) (hc : 1 < c) :
    let q : ℝ := Ideal.absNorm m
    let D : ℝ := ((|NumberField.discr F| : ℤ) : ℝ)
    let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
    Complex.VerticalIntegrable (mellinIntegrand w h X) (1 - c) ∧
      Summable (fun I : Ideal (𝓞 F) =>
        ‖if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
          fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)‖) ∧
      Summable (fun I : Ideal (𝓞 F) =>
        if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
          fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)) ∧
      Vendor.verticalIntegral (1 - c) (mellinIntegrand w h X) =
        (w.W * (X : ℂ) / (Real.sqrt q : ℂ)) *
          ∑' I : Ideal (𝓞 F),
            if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
              fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q) := by
  dsimp only
  let q : ℝ := Ideal.absNorm m
  let D : ℝ := ((|NumberField.discr F| : ℤ) : ℝ)
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
  let a : Ideal (𝓞 F) → ℂ := fun I => (starRingEnd ℂ) (η I)
  let G : ℂ → ℂ := fun s => B D r h s * ((X / q : ℝ) : ℂ) ^ (-s) *
    idealCoefficientLSeries a s
  let k : ℂ := w.W * (X : ℂ) / (Real.sqrt q : ℂ)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hm)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero F)
  have hr : 1 ≤ r := by
    have hfin := NumberField.IsTotallyComplex.finrank (K := F)
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    dsimp [r]
    omega
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have ha0 : a ⊥ = 0 := by simp [a, RayOperations.map_bot]
  have ha : ∀ I, ‖a I‖ ≤ 1 := by
    intro I
    simpa [a] using RayOperations.norm_le_one η I
  have hB : Complex.VerticalIntegrable (B D r h) c := by
    simpa [Complex.VerticalIntegrable] using
      B_inverse_integrable D r h hD hr hh hcompact c 1 hc0 zero_lt_one
  have hT : ∀ x : ℝ, 0 < x → fieldTransform D r h x = mellinInv c (B D r h) x := by
    intro x hx
    rw [fieldTransform, if_pos hx]
    exact (B_mellinInv_eq D r h hD hr hh hcompact c x hc0 hx).symm
  obtain ⟨hnorm, hsum, hG, hdual⟩ :=
    idealMellin_dual_interchange a ha0 ha (B D r h) (fieldTransform D r h)
      hc hX hq hB hT
  have hline : ∀ t : ℝ, mellinIntegrand w h X (1 - ((c : ℂ) + t * Complex.I)) =
      k * G ((c : ℂ) + t * Complex.I) := by
    intro t
    exact reflected_integrand_eq m hm η w h X hX _ (by simpa using hc)
  have hleft : Complex.VerticalIntegrable (mellinIntegrand w h X) (1 - c) := by
    have hint := (hG.const_mul k).comp_neg
    apply hint.congr
    filter_upwards [] with t
    change k * G ((c : ℂ) + (-t : ℝ) * Complex.I) =
      mellinIntegrand w h X (((1 - c : ℝ) : ℂ) + t * Complex.I)
    rw [← hline (-t)]
    congr 1
    push_cast
    ring
  let f : Ideal (𝓞 F) → ℂ := fun I => a I * fieldTransform D r h
    (X * (Ideal.absNorm I : ℝ) / q)
  have hsumAll : Summable (fun I : Ideal (𝓞 F) => if I = ⊥ then 0 else f I) := by
    have hs : Summable (({I : Ideal (𝓞 F) | I ≠ ⊥}).indicator f) :=
      summable_subtype_iff_indicator.mp hsum
    exact hs.congr fun I => by by_cases hI : I = ⊥ <;> simp [Set.indicator, hI]
  have hnormAll : Summable (fun I : Ideal (𝓞 F) => ‖if I = ⊥ then 0 else f I‖) := by
    have hs : Summable (({I : Ideal (𝓞 F) | I ≠ ⊥}).indicator (fun I => ‖f I‖)) :=
      summable_subtype_iff_indicator.mp hnorm
    exact hs.congr fun I => by by_cases hI : I = ⊥ <;> simp [Set.indicator, hI]
  have htsum : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, f I.val) =
      ∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else f I := by
    exact (tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥}) f).trans
      (tsum_congr fun I => by by_cases hI : I = ⊥ <;> simp [Set.indicator, hI])
  refine ⟨hleft, hnormAll, hsumAll, ?_⟩
  rw [← Vendor.verticalIntegral_one_sub c]
  have heq : Vendor.verticalIntegral c (fun s => mellinIntegrand w h X (1 - s)) =
      Vendor.verticalIntegral c (fun s => k * G s) := by
    unfold Vendor.verticalIntegral
    congr 1
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hline)
  rw [heq, Vendor.verticalIntegral_const_mul c k G hG, hdual, htsum]

end DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

theorem mellinIntegrand_source_line
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (w : EntireHeckeWitness η)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (σ : ℝ) (hσ : 1 < σ) :
    Complex.VerticalIntegrable (mellinIntegrand w h X) σ ∧
      (∑ᶠ I : Ideal (𝓞 F), idealMellinWeight η.toFun h X I) =
        Vendor.verticalIntegral σ (mellinIntegrand w h X) := by
  have ha0 : η.toFun ⊥ = 0 := by
    exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  have ha : ∀ I : Ideal (𝓞 F), ‖η.toFun I‖ ≤ 1 :=
    RayOperations.norm_le_one η
  have heq : ∀ s : ℂ, 1 < s.re → mellinIntegrand w h X s =
      mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries η.toFun s := by
    intro s hs
    have hD : (((|NumberField.discr F| : ℤ) : ℂ) *
        (Ideal.absNorm m : ℂ)) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero F)).ne'
      · exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hm)
    have hG : Complex.Gammaℂ s ≠ 0 := by
      rw [Complex.Gammaℂ_def]
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_)
        (Complex.Gamma_ne_zero_of_re_pos (by linarith))
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    have hr : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces F := by
      have hfin := NumberField.IsTotallyComplex.finrank (K := F)
      have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
      omega
    have hAD :
        ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (-s / 2)) *
        ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2)) = 1 := by
      rw [← Complex.cpow_add _ _ hD, show -s / 2 + s / 2 = 0 by ring,
        Complex.cpow_zero]
    have hBC : (Complex.Gammaℂ s)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F =
        Complex.Gammaℂ s := by
      obtain ⟨n, hn⟩ : ∃ n, NumberField.InfinitePlace.nrComplexPlaces F = n + 1 :=
        ⟨NumberField.InfinitePlace.nrComplexPlaces F - 1,
          (Nat.succ_pred_eq_of_pos hr).symm⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hG, one_pow, one_mul]
    have hL : (∑' I : Ideal (𝓞 F), η.toFun I * (Ideal.absNorm I : ℂ) ^ (-s)) =
        idealCoefficientLSeries η.toFun s := by
      symm
      unfold idealCoefficientLSeries
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal (𝓞 F) | I ≠ ⊥})
        (f := fun I : Ideal (𝓞 F) => η.toFun I * (Ideal.absNorm I : ℂ) ^ (-s))
      intro I hI
      change I ≠ ⊥
      intro hbot
      subst I
      simpa [Function.mem_support, ha0] using hI
    have hΛ : w.Λ s = heckeCompletionFactor F m s * idealCoefficientLSeries η.toFun s := by
      rw [← (w.hasSum s hs).tsum_eq, tsum_mul_left, hL]
    have hGQ := Vendor.Gammaℂ_mul_originMellinQ_eq_mellin h hh hcompact s
      (show 0 < s.re by linarith)
    rw [mellinIntegrand, hΛ, heckeCompletionFactor]
    calc
      _ = (Vendor.originMellinQ h s * (X : ℂ) ^ s) *
          (((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (-s / 2)) *
            ((((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2))) *
          ((Complex.Gammaℂ s)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces F - 1) *
            Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F) *
          idealCoefficientLSeries η.toFun s := by ring
      _ = mellin h s * (X : ℂ) ^ s * idealCoefficientLSeries η.toFun s := by
        rw [hAD, hBC]
        calc
          _ = (Complex.Gammaℂ s * Vendor.originMellinQ h s) * (X : ℂ) ^ s *
              idealCoefficientLSeries η.toFun s := by ring
          _ = _ := by rw [hGQ]
  have hline : ∀ t : ℝ, mellinIntegrand w h X ((σ : ℂ) + t * Complex.I) =
      mellin h ((σ : ℂ) + t * Complex.I) * (X : ℂ) ^ ((σ : ℂ) + t * Complex.I) *
        idealCoefficientLSeries η.toFun ((σ : ℂ) + t * Complex.I) := by
    intro t
    exact heq _ (by simpa using hσ)
  refine ⟨?_, ?_⟩
  · exact (idealMellin_verticalIntegrable η.toFun ha0 ha hh hcompact hX hσ).congr
      (Filter.Eventually.of_forall fun t => (hline t).symm)
  · rw [idealMellin_finsum_eq_verticalIntegral η.toFun ha0 ha hh hcompact hX hσ]
    unfold Vendor.verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun t => (hline t).symm

end DedekindZetaZeroFree.LargeSieve.NonprincipalPoisson

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem nonprincipalPoisson_of_witness
    {F : Type} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (w : EntireHeckeWitness η) :
    let q : ℝ := Ideal.absNorm m
    let D : ℝ := ((|NumberField.discr F| : ℤ) : ℝ)
    let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
    ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
      ∀ X : ℝ, 0 < X →
        Summable (fun I : Ideal (𝓞 F) =>
          ‖if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
            fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)‖) ∧
        Summable (fun I : Ideal (𝓞 F) =>
          if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
            fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)) ∧
        (∑ᶠ I : Ideal (𝓞 F), idealMellinWeight η.toFun h X I) =
          (w.W * (X : ℂ) / (Real.sqrt q : ℂ)) *
            ∑' I : Ideal (𝓞 F),
              if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
                fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q) := by
  dsimp only
  intro h hh hcompact X hX
  obtain ⟨hright, hsource⟩ :=
    NonprincipalPoisson.mellinIntegrand_source_line hF m hm η w h hh hcompact
      X hX 2 (by norm_num)
  obtain ⟨hleft, habs, hsum, hdual⟩ :=
    NonprincipalPoisson.mellinIntegrand_reflection_dual hF m hm η w h hh hcompact
      X hX (3 / 2) (by norm_num)
  have hline : (1 - (3 / 2 : ℝ)) = -1 / 2 := by norm_num
  rw [hline] at hleft hdual
  obtain ⟨hhol, hgrowth⟩ :=
    NonprincipalPoisson.mellinIntegrand_regularity hF m hm η w h hh hcompact
      X hX (-1 / 2) 2
  have hshift := Vendor.integral_eq_of_subquadratic_strip_growth
    (a := -1 / 2) (b := 2) (by norm_num)
    (NonprincipalPoisson.mellinIntegrand w h X)
    (fun s _ _ => hhol s) hleft hright hgrowth
  exact ⟨habs, hsum, hsource.trans (hshift.symm.trans hdual)⟩

end DedekindZetaZeroFree.LargeSieve

end

end

section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve

theorem nonprincipalPoisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprim : η.IsPrimitive) (hnonprincipal : ¬ η.IsPrincipal) :
    let q : ℝ := Ideal.absNorm m
    let D : ℝ := ((|NumberField.discr F| : ℤ) : ℝ)
    let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
    ∃ W : ℂ, ‖W‖ = 1 ∧
      ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
        ∀ X : ℝ, 0 < X →
          Summable (fun I : Ideal (𝓞 F) =>
            ‖if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
              fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)‖) ∧
          Summable (fun I : Ideal (𝓞 F) =>
            if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
              fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q)) ∧
          (∑ᶠ I : Ideal (𝓞 F), idealMellinWeight η.toFun h X I) =
            (W * (X : ℂ) / (Real.sqrt q : ℂ)) *
              ∑' I : Ideal (𝓞 F),
                if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
                  fieldTransform D r h (X * (Ideal.absNorm I : ℝ) / q) := by
  obtain ⟨w⟩ := exists_entireHeckeWitness hF hm η hprim hnonprincipal
  exact ⟨w.W, w.norm_W, nonprincipalPoisson_of_witness hF m hm η w⟩

end DedekindZetaZeroFree.LargeSieve

end

end
