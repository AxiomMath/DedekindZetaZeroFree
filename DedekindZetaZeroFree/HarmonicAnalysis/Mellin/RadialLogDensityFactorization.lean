module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.RealSignedLogSchwartzKernel
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.ComplexAngularLogSchwartzKernel
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.ArchimedeanHaarTensorDisintegration

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation
noncomputable section
open MeasureTheory

 def oneKernel (g : SchwartzMap ℝ ℂ) (σ t : ℝ) : ℂ :=
  g (Real.exp (t / 2)) * (Real.exp (σ * t) : ℂ)
private theorem oneKernel_integrable (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (oneKernel g σ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * (σ + 1))
  let C₀ := SchwartzMap.seminorm ℝ 0 0 g
  let C₁ := SchwartzMap.seminorm ℝ k 0 g
  let M : ℝ → ℝ := fun t => (C₀ + C₁) * if t ≤ 0 then Real.exp (σ * t) else Real.exp (-t)
  have hb : ∀ t, ‖oneKernel g σ t‖ ≤ M t := by
    intro t
    simp only [oneKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    by_cases ht : t ≤ 0
    · simp only [M, if_pos ht]
      exact (mul_le_mul_of_nonneg_right (g.norm_le_seminorm ℝ _) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (apply_nonneg _ _)) (Real.exp_pos _).le)
    · simp only [M, if_neg ht]
      have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
      have hg := g.norm_pow_mul_le_seminorm ℝ k (Real.exp (t / 2))
      have hpow : ‖Real.exp (t / 2)‖ ^ k = Real.exp ((k : ℝ) / 2 * t) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
        congr 1
        ring
      rw [hpow] at hg
      have hgb : ‖g (Real.exp (t / 2))‖ ≤ C₁ / Real.exp ((k : ℝ) / 2 * t) := by
        exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hg)
      have hh : σ - (k : ℝ) / 2 ≤ -1 := by linarith
      calc
        ‖g (Real.exp (t / 2))‖ * Real.exp (σ * t) ≤
            (C₁ / Real.exp ((k : ℝ) / 2 * t)) * Real.exp (σ * t) :=
          mul_le_mul_of_nonneg_right hgb (Real.exp_pos _).le
        _ = C₁ * Real.exp ((σ - (k : ℝ) / 2) * t) := by
          rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ C₁ * Real.exp (-t) := by
          apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
          apply Real.exp_le_exp.mpr
          nlinarith
        _ ≤ (C₀ + C₁) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (apply_nonneg _ _)) (Real.exp_pos _).le
  have hl : IntegrableOn M (Set.Iic 0) := by
    apply ((integrableOn_exp_mul_Iic hσ 0).const_mul (C₀ + C₁)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Iic] with t ht
    simp only [M, Set.mem_Iic.mp ht, if_true]
  have hr : IntegrableOn M (Set.Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul (C₀ + C₁)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [M, not_le.mpr (Set.mem_Ioi.mp ht), if_false, neg_one_mul]
  have hi : Integrable M := by
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hl.union hr
  apply hi.mono' _ (Filter.Eventually.of_forall hb)
  have hc : Continuous (oneKernel g σ) := g.continuous.comp (by fun_prop) |>.mul (by fun_prop)
  exact hc.aestronglyMeasurable

private theorem positive_log_substitution (f : ℝ → ℂ) :
    (IntegrableOn f (Set.Ioi 0) ↔
      Integrable (fun t : ℝ => (Real.exp (t / 2) / 2) • f (Real.exp (t / 2)))) ∧
    (∫ x : ℝ in Set.Ioi 0, f x) =
      ∫ t : ℝ, (Real.exp (t / 2) / 2) • f (Real.exp (t / 2)) := by
  have hrange : (fun t : ℝ => Real.exp (t / 2)) '' Set.univ = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioi]
    constructor
    · rintro ⟨t, rfl⟩; exact Real.exp_pos _
    · intro hx
      exact ⟨2 * Real.log x, by simpa using Real.exp_log hx⟩
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) / 2) t := by
    simpa only [div_eq_mul_inv, one_mul, id_eq] using
      ((hasDerivAt_id t).div_const 2).exp
  have hinj : Function.Injective (fun t : ℝ => Real.exp (t / 2)) := by
    intro t u h
    exact (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp (Real.exp_injective h)
  rw [← hrange]
  constructor
  · simpa only [integrableOn_univ, abs_of_pos (by positivity : 0 < Real.exp (_ / 2) / 2)] using
      integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn f
  · simpa only [setIntegral_univ, abs_of_pos (by positivity : 0 < Real.exp (_ / 2) / 2)] using
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn f
private theorem log_values (σ t : ℝ) :
    Real.log (Real.exp (t / 2) ^ 2) = t ∧
    ((Real.exp (t / 2) ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) = (Real.exp (σ * t) : ℂ) := by
  have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, Real.log_exp]
  constructor
  · rfl
  · rw [← Complex.ofReal_cpow (Real.exp_pos t).le σ, ← Real.exp_mul]
    rw [mul_comm]

 def reflected (g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) g

private theorem positive_test (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :
    IntegrableOn (fun x : ℝ => (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / (x : ℂ)) *
      φ (Real.log (x ^ 2))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / (x : ℂ)) *
      φ (Real.log (x ^ 2))) =
      ∫ t : ℝ, (1 / 2 : ℂ) * oneKernel g σ t * φ t := by
  let f : ℝ → ℂ := fun x => (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / (x : ℂ)) *
    φ (Real.log (x ^ 2))
  have heq : (fun t => (Real.exp (t / 2) / 2) • f (Real.exp (t / 2))) =
      (fun t => (1 / 2 : ℂ) * oneKernel g σ t * φ t) := by
    funext t
    obtain ⟨hl, hc⟩ := log_values σ t
    simp only [f, hl, hc, Complex.real_smul, oneKernel]
    push_cast
    field_simp
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable (fun t : ℝ => (1 / 2 : ℂ) * oneKernel g σ t * φ t) :=
    ((oneKernel_integrable g σ hσ).const_mul _).mul_bdd hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hs := positive_log_substitution f
  rw [heq] at hs
  exact ⟨hs.1.mpr hi, hs.2⟩

theorem real_multiplicative_haar_log_test
    (g : SchwartzMap ℝ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (rawRealSignedLogKernel g σ) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
        (∫ x : ℝ,
          (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / ((|x| : ℝ) : ℂ)) *
            φ (Real.log (x ^ 2))) =
          ∫ t : ℝ, rawRealSignedLogKernel g σ t * φ t := by
  obtain ⟨k, hk⟩ := real_signed_log_kernel_isSchwartz g σ hσ
  have hi : Integrable (rawRealSignedLogKernel g σ) := by
    exact k.integrable.congr (Filter.Eventually.of_forall hk)
  refine ⟨hi, ?_⟩
  intro φ hφ hb
  let f : ℝ → ℂ := fun x =>
    (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / ((|x| : ℝ) : ℂ)) * φ (Real.log (x ^ 2))
  have hp := positive_test g σ hσ φ hφ hb
  have hn := positive_test (reflected g) σ hσ φ hφ hb
  have hpos : IntegrableOn f (Set.Ioi 0) := by
    apply hp.1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simp only [f, abs_of_pos (Set.mem_Ioi.mp hx)]
  have hneg : IntegrableOn (fun x => f (-x)) (Set.Ioi 0) := by
    apply hn.1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    change (g (-x) * _ / (x : ℂ)) * _ = _
    simp only [f, neg_sq, abs_neg, abs_of_pos (Set.mem_Ioi.mp hx)]
  have hleft : IntegrableOn f (Set.Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio).mpr
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding |>.mpr hneg
    simpa [Function.comp_def] using h
  have hright : (∫ x : ℝ in Set.Ioi 0, f x) =
      ∫ t : ℝ, (1 / 2 : ℂ) * oneKernel g σ t * φ t := by
    rw [← hp.2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [f, abs_of_pos (Set.mem_Ioi.mp hx)]
  have hleft_eq : (∫ x : ℝ in Set.Iic 0, f x) =
      ∫ t : ℝ, (1 / 2 : ℂ) * oneKernel (reflected g) σ t * φ t := by
    rw [← neg_zero, ← integral_comp_neg_Ioi, ← hn.2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change _ = (g (-x) * _ / (x : ℂ)) * _
    simp only [f, neg_sq, abs_neg, abs_of_pos (Set.mem_Ioi.mp hx)]
  change (∫ x : ℝ, f x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hpos, hleft_eq, hright]
  have hip := ((oneKernel_integrable g σ hσ).const_mul (1 / 2 : ℂ)).mul_bdd
    hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb.choose_spec)
  have hin := ((oneKernel_integrable (reflected g) σ hσ).const_mul (1 / 2 : ℂ)).mul_bdd
    hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb.choose_spec)
  rw [← integral_add hin hip]
  apply integral_congr_ae
  filter_upwards with t
  change (1 / 2 : ℂ) * (g (-Real.exp (t / 2)) * _) * φ t +
    (1 / 2 : ℂ) * (g (Real.exp (t / 2)) * _) * φ t = _
  simp only [rawRealSignedLogKernel]
  ring

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation
noncomputable section
open MeasureTheory Set MeasureTheory.Measure

 def pol (g : ℂ → ℂ) (σ : ℝ) (φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) *
    (p.1 ^ (2 * σ - 1) : ℝ) * φ (Real.log (p.1 ^ 2))
private lemma pol_meas (g : SchwartzMap ℂ ℂ) (σ : ℝ) (φ : ℝ → ℂ)
    (hφ : Continuous φ) : AEStronglyMeasurable (pol g σ φ) := by
  unfold pol
  apply Measurable.aestronglyMeasurable
  apply Measurable.mul
  · apply Measurable.mul
    · exact g.continuous.measurable.comp (by fun_prop)
    · exact Complex.continuous_ofReal.measurable.comp (measurable_fst.pow_const _)
  · exact hφ.measurable.comp (Real.measurable_log.comp (by fun_prop))
private lemma circle_norm (r θ : ℝ) (hr : 0 < r) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
private lemma pol_bound (g : SchwartzMap ℂ ℂ) (σ : ℝ) (φ : ℝ → ℂ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) (m : ℕ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    ‖pol g σ φ p‖ ≤ (SchwartzMap.seminorm ℝ m 0 g * C) * p.1 ^ (2 * σ - 1 - m) := by
  have hn := circle_norm p.1 p.2 hp
  have hs := SchwartzMap.norm_pow_mul_le_seminorm ℝ g m
    ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
  rw [hn] at hs
  have hg : ‖g ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))‖ ≤
      SchwartzMap.seminorm ℝ m 0 g / p.1 ^ m := (le_div_iff₀ (pow_pos hp m)).mpr (by simpa [mul_comm] using hs)
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC 0)
  unfold pol
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  calc
    _ ≤ (SchwartzMap.seminorm ℝ m 0 g / p.1 ^ m) * p.1 ^ (2 * σ - 1) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hp.le _)) (hC _) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_sub hp (2 * σ - 1) (m : ℝ), Real.rpow_natCast]; ring
private lemma pol_int (g : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    IntegrableOn (pol g σ φ) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * σ)
  have hsmall : IntegrableOn (fun r : ℝ => r ^ (2 * σ - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < 2 * σ - 1)).1
  have hlarge : IntegrableOn (fun r : ℝ => r ^ (2 * σ - 1 - m)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) := integrable_const _
  have h₁ : IntegrableOn (pol g σ φ) (Ioc 0 1 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, volume_eq_prod, ← Measure.prod_restrict]
    apply ((hsmall.const_mul (SchwartzMap.seminorm ℝ 0 0 g * C)).mul_prod hθ).mono'
    · rw [Measure.prod_restrict, ← volume_eq_prod]; exact (pol_meas g σ φ hφ).restrict
    · have ha := ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ))) ((measurableSet_Ioc (a := (0 : ℝ)) (b := 1)).prod (measurableSet_Ioo (a := -Real.pi) (b := Real.pi)))
      rw [volume_eq_prod, ← Measure.prod_restrict] at ha
      filter_upwards [ha] with p hp
      have hp := hp.1
      simpa [mul_one] using pol_bound g σ φ C hC 0 p hp.1
  have h₂ : IntegrableOn (pol g σ φ) (Ioi 1 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, volume_eq_prod, ← Measure.prod_restrict]
    apply ((hlarge.const_mul (SchwartzMap.seminorm ℝ m 0 g * C)).mul_prod hθ).mono'
    · rw [Measure.prod_restrict, ← volume_eq_prod]; exact (pol_meas g σ φ hφ).restrict
    · have ha := ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ))) ((measurableSet_Ioi (a := (1 : ℝ))).prod (measurableSet_Ioo (a := -Real.pi) (b := Real.pi)))
      rw [volume_eq_prod, ← Measure.prod_restrict] at ha
      filter_upwards [ha] with p hp
      have hp := hp.1
      simpa [mul_one] using pol_bound g σ φ C hC m p (lt_trans (by norm_num) hp)
  have heq : (Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) ∪
      (Ioi 1 ×ˢ Ioo (-Real.pi) Real.pi) = Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [mem_union, mem_prod, mem_Ioc, mem_Ioi, mem_Ioo]
    constructor
    · rintro (h | h)
      · exact ⟨h.1.1, h.2⟩
      · exact ⟨lt_trans (by norm_num) h.1, h.2⟩
    · intro h
      by_cases hp : p.1 ≤ 1
      · exact Or.inl ⟨⟨h.1, hp⟩, h.2⟩
      · exact Or.inr ⟨lt_of_not_ge hp, h.2⟩
  rw [← heq]
  exact h₁.union h₂
private lemma circle_integral_shift (g : ℂ → ℂ) (r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      ∫ θ : ℝ in Icc 0 (2 * Real.pi), g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hp : Function.Periodic (fun θ : ℝ => g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (2 * Real.pi) := by
    intro θ
    apply congrArg g
    apply congrArg (fun z : ℂ => (r : ℂ) * z)
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      Complex.exp_mul_I_periodic (θ : ℂ)
  have hi := hp.intervalIntegral_add_eq (-Real.pi) 0
  simp only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hi
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    ← integral_Icc_eq_integral_Ioc] at hi
  exact hi
private lemma polar_algebra (g : ℂ → ℂ) (σ : ℝ) (φ : ℝ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p.1 • ((g (Complex.polarCoord.symm p) *
      ((‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) /
      ((‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ)) *
      φ (Real.log (‖Complex.polarCoord.symm p‖ ^ 2))) = pol g σ φ p := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos hp, Complex.polarCoord_symm_apply,
    ← Complex.exp_ofReal_mul_I]
  rw [← Complex.ofReal_cpow (sq_nonneg p.1) σ]
  have hr : (p.1 ^ 2 : ℝ) ^ σ = p.1 ^ (2 * σ) := by
    rw [← Real.rpow_natCast p.1 2, ← Real.rpow_mul hp.le]; norm_num
  rw [hr, Complex.real_smul, pol]
  have ht : p.1 ^ (2 * σ - 1) = p.1 ^ (2 * σ) / p.1 := by
    rw [Real.rpow_sub hp, Real.rpow_one]
  rw [ht]
  push_cast
  field_simp
  <;> ring
private lemma polar_test (g : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    (∫ z : ℂ, (g z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) /
      ((‖z‖ ^ 2 : ℝ) : ℂ)) * φ (Real.log (‖z‖ ^ 2))) =
    ∫ r : ℝ in Ioi 0, (∫ θ : ℝ in Icc 0 (2 * Real.pi),
      g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
      ((r ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) * φ (Real.log (r ^ 2)) / (r : ℂ) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  calc
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, pol g σ φ p := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact polar_algebra g σ φ p hp.1
    _ = ∫ r : ℝ in Ioi 0, ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, pol g σ φ (r, θ) := by
      rw [volume_eq_prod]
      exact setIntegral_prod _ (by simpa [← volume_eq_prod] using pol_int g σ hσ φ hφ C hC)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp only [pol]
      rw [integral_mul_const, integral_mul_const, circle_integral_shift]
      rw [← Complex.ofReal_cpow (sq_nonneg r) σ]
      have he : (r ^ 2 : ℝ) ^ σ = r ^ (2 * σ) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]; norm_num
      rw [he, Real.rpow_sub hr, Real.rpow_one]
      push_cast
      ring

private theorem radialLogIdentity
    (g : ℂ → ℂ) (σ : ℝ) (φ : ℝ → ℂ) :
    (∫ r : ℝ in Set.Ioi 0,
      ((∫ θ : ℝ in Set.Icc 0 (2 * Real.pi),
          g ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
        ((r ^ 2 : ℝ) : ℂ) ^ (σ : ℂ)) *
        φ (Real.log (r ^ 2)) / (r : ℂ)) =
      ∫ t : ℝ, rawComplexAngularLogKernel g σ t * φ t := by
  have hrange : (fun t : ℝ => Real.exp (t / 2)) '' Set.univ = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioi]
    constructor
    · rintro ⟨t, rfl⟩; exact Real.exp_pos _
    · intro hx
      exact ⟨2 * Real.log x, by simpa using Real.exp_log hx⟩
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (u / 2))
      (Real.exp (t / 2) / 2) t := by
    simpa only [div_eq_mul_inv, one_mul, id_eq] using
      ((hasDerivAt_id t).div_const 2).exp
  have hinj : Function.Injective (fun t : ℝ => Real.exp (t / 2)) := by
    intro t u h
    exact (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp (Real.exp_injective h)
  rw [← hrange]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn]
  rw [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with t
  have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [he, Real.log_exp,
    abs_of_pos (by positivity : 0 < Real.exp (t / 2) / 2),
    Complex.real_smul, rawComplexAngularLogKernel]
  rw [← Complex.ofReal_cpow (Real.exp_pos t).le σ, ← Real.exp_mul]
  push_cast
  field_simp
  simp only [mul_comm]

theorem complex_multiplicative_haar_log_test
    (g : SchwartzMap ℂ ℂ) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (rawComplexAngularLogKernel g σ) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
        (∫ z : ℂ,
          (g z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) /
            ((‖z‖ ^ 2 : ℝ) : ℂ)) * φ (Real.log (‖z‖ ^ 2))) =
          ∫ t : ℝ, rawComplexAngularLogKernel g σ t * φ t := by
  obtain ⟨k, hk⟩ := complex_angular_log_kernel_isSchwartz g σ hσ
  constructor
  · exact k.integrable.congr (Filter.Eventually.of_forall hk)
  · intro φ hφ hbound
    obtain ⟨C, hC⟩ := hbound
    exact (polar_test g σ hσ φ hφ C hC).trans
      (radialLogIdentity g σ φ)

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity.RadialIsolation

end

section

namespace DedekindZetaZeroFree.ProbeSheetLogDensityRegularity
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

theorem finite_positive_weights_pushforward
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    (ν : Measure X) (L : X → ℝ) (hL : Measurable L)
    (u : ι → X → ℝ) (hu : ∀ i, Measurable (u i))
    (hu0 : ∀ i x, 0 ≤ u i x) (hui : ∀ i, Integrable (u i) ν)
    (c : ι → ℂ) :
    ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ) (w : ℝ → ℂ),
      Integrable w μ ∧ ∀ φ : ℝ → ℂ, Continuous φ →
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ x, (∑ i, c i * (u i x : ℂ)) * φ (L x) ∂ν) =
        ∫ s, w s * φ s ∂μ := by
  classical
  let ρ : ι → Measure ℝ := fun i =>
    Measure.map L (ν.withDensity (fun x => ENNReal.ofReal (u i x)))
  have hρ : ∀ i, IsFiniteMeasure (ρ i) := by
    intro i
    letI := isFiniteMeasure_withDensity_ofReal (hui i).2
    dsimp [ρ]
    infer_instance
  letI := hρ
  let μ : Measure ℝ := ∑ i, ρ i
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  letI := hμ
  have hle : ∀ i, ρ i ≤ μ := by
    intro i
    exact Finset.single_le_sum (fun j _ => (show 0 ≤ ρ j from bot_le)) (Finset.mem_univ i)
  have hac : ∀ i, ρ i ≪ μ := fun i => (hle i).absolutelyContinuous
  let d : ι → ℝ → ℝ := fun i s => ((ρ i).rnDeriv μ s).toReal
  have hd : ∀ i, Integrable (d i) μ := fun i => Measure.integrable_toReal_rnDeriv
  let w : ℝ → ℂ := fun s => ∑ i, c i * (d i s : ℂ)
  have hw : Integrable w μ :=
    integrable_finset_sum Finset.univ (fun i _ => (hd i).ofReal.const_mul (c i))
  refine ⟨μ, hμ, w, hw, ?_⟩
  intro φ hφ hb
  obtain ⟨C, hC⟩ := hb
  have hφρ : ∀ i, Integrable φ (ρ i) := fun i =>
    Integrable.of_bound hφ.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hlocal : ∀ i,
      (∫ s, (d i s : ℂ) * φ s ∂μ) =
        ∫ x, (u i x : ℂ) * φ (L x) ∂ν := by
    intro i
    calc
      _ = ∫ s, φ s ∂ρ i := by
        simpa only [d, Complex.real_smul, smul_eq_mul] using
          (integral_rnDeriv_smul (f := φ) (hac i))
      _ = ∫ x, φ (L x) ∂ν.withDensity (fun x => ENNReal.ofReal (u i x)) :=
        integral_map hL.aemeasurable hφ.aestronglyMeasurable
      _ = _ := by
        rw [integral_withDensity_eq_integral_toReal_smul
          (hu i).ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
        simp only [ENNReal.toReal_ofReal (hu0 i _), Complex.real_smul, smul_eq_mul]
  have huint : ∀ i, Integrable (fun x => c i * (u i x : ℂ) * φ (L x)) ν :=
    fun i => ((hui i).ofReal.const_mul (c i)).mul_bdd
      (hφ.measurable.comp hL).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC _)
  have hdφ : ∀ i, Integrable (fun s => c i * (d i s : ℂ) * φ s) μ :=
    fun i => ((hd i).ofReal.const_mul (c i)).mul_bdd
      hφ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  simp only [w, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => huint i),
    integral_finset_sum _ (fun i _ => hdφ i)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, integral_const_mul, hlocal i]

theorem integrable_weight_pushforward_finite
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (L : X → ℝ) (hL : Measurable L)
    (a : X → ℂ) (ha : Integrable a ν) :
    ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ) (w : ℝ → ℂ),
      Integrable w μ ∧ ∀ φ : ℝ → ℂ, Continuous φ →
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ x, a x * φ (L x) ∂ν) = ∫ s, w s * φ s ∂μ := by
  let b := ha.aestronglyMeasurable.mk a
  have hb : Measurable b := ha.aestronglyMeasurable.measurable_mk
  have hab : a =ᵐ[ν] b := ha.aestronglyMeasurable.ae_eq_mk
  have hbi : Integrable b ν := ha.congr hab
  let u : Fin 4 → X → ℝ := ![
    fun x => ((b x).re.toNNReal : ℝ),
    fun x => ((-(b x).re).toNNReal : ℝ),
    fun x => ((b x).im.toNNReal : ℝ),
    fun x => ((-(b x).im).toNNReal : ℝ)]
  let c : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
  have hu : ∀ i, Measurable (u i) := by
    intro i
    fin_cases i <;> dsimp [u] <;> fun_prop
  have hu0 : ∀ i x, 0 ≤ u i x := by
    intro i x
    fin_cases i <;> dsimp [u] <;> positivity
  have hui : ∀ i, Integrable (u i) ν := by
    intro i
    fin_cases i
    · exact hbi.re.real_toNNReal
    · exact hbi.re.neg.real_toNNReal
    · exact hbi.im.real_toNNReal
    · exact hbi.im.neg.real_toNNReal
  have hdecomp : ∀ x, (∑ i, c i * (u i x : ℂ)) = b x := by
    intro x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      u, c, zero_add, add_zero]
    have hr : ((b x).re.toNNReal : ℝ) - ((-(b x).re).toNNReal : ℝ) = (b x).re := by
      simp only [Real.coe_toNNReal']
      exact max_zero_sub_max_neg_zero_eq_self _
    have hi : ((b x).im.toNNReal : ℝ) - ((-(b x).im).toNNReal : ℝ) = (b x).im := by
      simp only [Real.coe_toNNReal']
      exact max_zero_sub_max_neg_zero_eq_self _
    simp only [Real.coe_toNNReal'] at hr hi
    apply Complex.ext <;> simp <;> linarith
  obtain ⟨μ, hμ, w, hw, he⟩ :=
    finite_positive_weights_pushforward ν L hL u hu hu0 hui c
  refine ⟨μ, hμ, w, hw, ?_⟩
  intro φ hφ hbound
  calc
    _ = ∫ x, b x * φ (L x) ∂ν := integral_congr_ae (hab.mul (Filter.EventuallyEq.rfl))
    _ = ∫ x, (∑ i, c i * (u i x : ℂ)) * φ (L x) ∂ν := by
      simp only [hdecomp]
    _ = _ := he φ hφ hbound

theorem radial_mixture_test_identity
    (μ : Measure ℝ) [SFinite μ] (w k : ℝ → ℂ)
    (hw : Integrable w μ) (hk : Integrable k)
    (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hb : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :
    (∫ t : ℝ, (∫ s : ℝ, w s * k (t - s) ∂μ) * φ t) =
      ∫ s : ℝ, w s * (∫ r : ℝ, k r * φ (r + s)) ∂μ := by
  obtain ⟨C, hC⟩ := hb
  have hK : Integrable (fun p : ℝ × ℝ => w p.2 * k (p.1 - p.2))
      (volume.prod μ) := hw.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hk
  have hKφ : Integrable (fun p : ℝ × ℝ =>
      (w p.2 * k (p.1 - p.2)) * φ p.1) (volume.prod μ) :=
    hK.mul_bdd (hφ.measurable.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p.1)
  calc
    _ = ∫ t : ℝ, ∫ s : ℝ, (w s * k (t - s)) * φ t ∂μ := by
      simp only [integral_mul_const]
    _ = ∫ s : ℝ, (∫ t : ℝ, (w s * k (t - s)) * φ t) ∂μ :=
      integral_integral_swap hKφ
    _ = _ := by
      congr 1
      funext s
      have he := integral_add_right_eq_self (μ := volume)
        (fun t : ℝ => (w s * k (t - s)) * φ t) s
      rw [← he]
      simp only [add_sub_cancel_right, mul_assoc, integral_const_mul]

theorem radial_kernel_test_continuous_bounded
    (k : ℝ → ℂ) (hk : Integrable k) (φ : ℝ → ℂ)
    (hφ : Continuous φ) (hb : ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) :
    Continuous (fun s : ℝ => ∫ r : ℝ, k r * φ (r + s)) ∧
      ∃ B : ℝ, ∀ s : ℝ, ‖∫ r : ℝ, k r * φ (r + s)‖ ≤ B := by
  obtain ⟨C, hC⟩ := hb
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun r : ℝ => k r * φ (r + s)) volume := by
    intro s
    exact hk.aestronglyMeasurable.mul
      (hφ.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hbound : ∀ s : ℝ, ∀ᵐ r : ℝ, ‖k r * φ (r + s)‖ ≤ ‖k r‖ * C := by
    intro s
    exact Filter.Eventually.of_forall fun r => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hki : ∀ s : ℝ, Integrable (fun r : ℝ => k r * φ (r + s)) := by
    intro s
    exact hk.mul_bdd
      (hφ.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => hC _)
  constructor
  · apply continuous_of_dominated hmeas hbound (hk.norm.mul_const C)
    exact Filter.Eventually.of_forall fun r =>
      continuous_const.mul (hφ.comp (continuous_const.add continuous_id))
  · refine ⟨(∫ r : ℝ, ‖k r‖) * C, fun s => ?_⟩
    calc
      _ ≤ ∫ r : ℝ, ‖k r * φ (r + s)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ r : ℝ, ‖k r‖ * C :=
        integral_mono_ae (hki s).norm (hk.norm.mul_const C) (hbound s)
      _ = _ := integral_mul_const _ _

theorem radial_factorization_of_residual_integral
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (L : X → ℝ) (hL : Measurable L)
    (a : X → ℂ) (ha : Integrable a ν)
    (k : ℝ → ℂ) (hk : Integrable k) :
    ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ) (w : ℝ → ℂ),
      Integrable w μ ∧ ∀ φ : ℝ → ℂ, Continuous φ →
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
      (∫ x, a x * (∫ r : ℝ, k r * φ (r + L x)) ∂ν) =
        ∫ t : ℝ, (∫ s : ℝ, w s * k (t - s) ∂μ) * φ t := by
  obtain ⟨μ, hμ, w, hw, he⟩ := integrable_weight_pushforward_finite ν L hL a ha
  letI := hμ
  refine ⟨μ, hμ, w, hw, ?_⟩
  intro φ hφ hb
  obtain ⟨hJ, hJb⟩ := radial_kernel_test_continuous_bounded k hk φ hφ hb
  calc
    _ = ∫ s : ℝ, w s * (∫ r : ℝ, k r * φ (r + s)) ∂μ := he _ hJ hJb
    _ = _ := (radial_mixture_test_identity μ w k hw hk φ hφ hb).symm

theorem schwartzTensor_log_pushforward_radial_factorization
    {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ν : @Measure (SLocalProduct F S)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F S)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F S) _ (borel _)) ν)
    (h : SLocalProduct F S → ℂ)
    (hh : ProbeSheetVerticalDecay.IsSchwartzTensor F S h)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ) (w k : ℝ → ℂ),
      Integrable w μ ∧
      ((∃ g : SchwartzMap ℝ ℂ, k = rawRealSignedLogKernel g σ) ∨
       (∃ g : SchwartzMap ℂ ℂ, k = rawComplexAngularLogKernel g σ)) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C) →
        (∫ y : (SLocalProduct F S)ˣ,
          (h y.val * (ProbeWeight.modulus F S y : ℂ) ^ (σ : ℂ)) *
            φ (Real.log (ProbeWeight.modulus F S y)) ∂ν) =
          ∫ t : ℝ, (∫ s : ℝ, w s * k (t - s) ∂μ) * φ t := by
  obtain ⟨v, η, hη, L, a, hL, ha, hcases⟩ :=
    RadialIsolation.schwartzTensor_isolate_archimedean_integral S ν hν h hh σ hσ
  letI : MeasurableSpace (RadialIsolation.RemainingCoordinates S v) := borel _
  letI := hη
  rcases hcases with ⟨g, _, htest⟩ | ⟨g, _, htest⟩
  · obtain ⟨hk, hlocal⟩ := RadialIsolation.real_multiplicative_haar_log_test g σ hσ
    obtain ⟨μ, hμ, w, hw, he⟩ :=
      radial_factorization_of_residual_integral η L hL a ha
        (rawRealSignedLogKernel g σ) hk
    refine ⟨μ, hμ, w, rawRealSignedLogKernel g σ, hw, Or.inl ⟨g, rfl⟩, ?_⟩
    intro φ hφ hb
    calc
      _ = ∫ p, a p * (∫ x : ℝ,
          (g x * ((x ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) / ((|x| : ℝ) : ℂ)) *
            φ (Real.log (x ^ 2) + L p)) ∂η := htest φ hφ hb
      _ = ∫ p, a p * (∫ r : ℝ,
          rawRealSignedLogKernel g σ r * φ (r + L p)) ∂η := by
        congr 1
        funext p
        rw [hlocal (fun r => φ (r + L p))
          (hφ.comp (continuous_id.add continuous_const))
          (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun r => hC _⟩)]
      _ = _ := he φ hφ hb
  · obtain ⟨hk, hlocal⟩ := RadialIsolation.complex_multiplicative_haar_log_test g σ hσ
    obtain ⟨μ, hμ, w, hw, he⟩ :=
      radial_factorization_of_residual_integral η L hL a ha
        (rawComplexAngularLogKernel g σ) hk
    refine ⟨μ, hμ, w, rawComplexAngularLogKernel g σ, hw, Or.inr ⟨g, rfl⟩, ?_⟩
    intro φ hφ hb
    calc
      _ = ∫ p, a p * (∫ z : ℂ,
          (g z * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (σ : ℂ) /
            ((‖z‖ ^ 2 : ℝ) : ℂ)) *
            φ (Real.log (‖z‖ ^ 2) + L p)) ∂η := htest φ hφ hb
      _ = ∫ p, a p * (∫ r : ℝ,
          rawComplexAngularLogKernel g σ r * φ (r + L p)) ∂η := by
        congr 1
        funext p
        rw [hlocal (fun r => φ (r + L p))
          (hφ.comp (continuous_id.add continuous_const))
          (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun r => hC _⟩)]
      _ = _ := he φ hφ hb

end
end DedekindZetaZeroFree.ProbeSheetLogDensityRegularity

end
