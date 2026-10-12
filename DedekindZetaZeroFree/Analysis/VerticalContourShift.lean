module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/ContinuationContour.lean.
Source: PrincipalMellinResidues.lean.
-/

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology

def comparisonClosedStrip (a b : ℝ) : Set ℂ :=
  {s | a ≤ s.re ∧ s.re ≤ b}

def comparisonVerticalIntegral (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, f ((σ : ℂ) + (t : ℂ) * I)

namespace ComparisonShiftProof

lemma inverse_vertical_continuous (c : ℝ) (hc : c≠0) :
    Continuous (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c≠0) :
    (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).re at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).re) =
        (fun t : ℝ => c/(c^2+t^2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp only [neg_div, Real.arctan_neg, ofReal_re]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).im at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).im) =
        (fun t : ℝ => -(t/(c^2+t^2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc]
    simp only [neg_sq, sub_self, zero_div, neg_zero, ofReal_im]

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0<c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c<0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹‖ ≤ T⁻¹ * |b-a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x:ℂ)+(ε*T)*I-p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b-a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z≠p)
    (hF : F z = A z / (z-p)) :
    dslope A p z = F z - A p * (z-p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x≠p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z-p))
    (hi : Integrable (fun t : ℝ => F ((x:ℂ)+t*I))) :
    (∫ t : ℝ in -T..T, dslope A (p:ℂ) ((x:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((x:ℂ)+t*I)) -
        A p * (∫ t : ℝ in -T..T, (((x-p:ℝ):ℂ)+t*I)⁻¹) := by
  have he (t : ℝ) : dslope A (p:ℂ) ((x:ℂ)+t*I) =
      F ((x:ℂ)+t*I) - A p * ((((x-p:ℝ):ℂ)+t*I)⁻¹) := by
    have hn : (x:ℂ)+t*I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    convert h using 1; push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x-p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤z.re ∧ z.re≤b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a≤b) (hy : y≠0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b}) :
    ContinuousOn (fun x : ℝ => A ((x:ℂ)+y*I) / ((x:ℂ)+y*I-p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x hx h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a≤b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ε : ℝ) (hε : |ε|=1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε*T≠0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x:ℂ)+(ε*T)*I≠p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have he (x : ℝ) (hx : x∈uIcc a b) := hF ((x:ℂ)+(ε*T)*I)
    (by have := (uIcc_of_le hab ▸ hx).1; simpa using this)
    (by have := (uIcc_of_le hab ▸ hx).2; simpa using this) (hn x)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(ε*T)*I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p:=p) hab hy hA).congr ?_).intervalIntegrable
    intro x hx
    simpa using he x hx
  have hki : IntervalIntegrable (fun x : ℝ => ((x:ℂ)+(ε*T)*I-p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (dslope_eq_sub_pole (hn x) (he x hx)).symm

theorem simple_pole_of_boundary_control (A F : ℂ → ℂ) {a b p : ℝ}
    (hap : a<p) (hpb : p<b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ha : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    comparisonVerticalIntegral b F = comparisonVerticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hnb : {z : ℂ | a≤z.re ∧ z.re≤b} ∈ 𝓝 (p:ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a<(p:ℂ).re ∧ (p:ℂ).re<b from ⟨hap,hpb⟩))
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((a:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((a:ℂ)+t*I)) - A p * (-(Real.pi:ℂ)))) := by
    simp_rw [dslope_vertical_truncated A F p a _ hap.ne
      (fun z hz => hF z (by simp [hz]) (by simpa [hz] using hab)
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hap.ne this)) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a-p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((b:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((b:ℂ)+t*I)) - A p * (Real.pi:ℂ))) := by
    simp_rw [dslope_vertical_truncated A F p b _ hpb.ne'
      (fun z hz => hF z (by simpa [hz] using hab) (by simp [hz])
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hpb.ne' this)) hb]
    exact hbF.sub ((inverse_vertical_limit_pos (b-p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A F hab hA hF (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A F hab hA hF 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  have he' : (∫ t : ℝ, F ((b:ℂ)+t*I)) =
      (∫ t : ℝ, F ((a:ℂ)+t*I)) + 2*(Real.pi:ℂ)*A p := by
    linear_combination -he
  unfold comparisonVerticalIntegral
  rw [he']
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm]

lemma integrable_tail (g : ℝ → ℂ) (C : ℝ) (hg : Continuous g)
    (hbound : ∀ t : ℝ, 1 ≤ |t| → ‖g t‖ ≤ C * (1 + |t|) ^ (-2 : ℝ)) :
    Integrable g := by
  have hi : Integrable (fun t : ℝ => C * (1 + |t|) ^ (-2 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by simp)).const_mul C
  have hc : IntegrableOn g (Icc (-1) 1) := hg.integrableOn_Icc
  have ht : IntegrableOn g (Icc (-1) 1)ᶜ := by
    apply hi.integrableOn.mono' hg.aestronglyMeasurable.restrict
    apply ae_restrict_of_forall_mem measurableSet_Icc.compl
    intro t ht
    apply hbound t
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [abs_of_neg (by linarith)]
      linarith
    · exact (le_abs_self t).trans' ht.le
  simpa only [union_compl_self, integrableOn_univ] using hc.union ht

lemma horizontal_decay_limit (F : ℂ → ℂ) (a b C ε : ℝ) (hab : a ≤ b)
    (hε : |ε| = 1)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, 1 ≤ |y| →
      ‖F ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (ε*T) * I)) atTop (𝓝 0) := by
  have hr : Tendsto (fun T : ℝ => (1 + T) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using (hr.const_mul C).mul_const |b-a|)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have he : |ε*T| = T := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hh := hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx)
    (ε*T) (by simpa [he] using hT)
  rw [he, ofReal_mul, Real.rpow_neg (by linarith : 0 ≤ 1 + T), Real.rpow_two] at hh
  exact hh

end ComparisonShiftProof

theorem verticalIntegral_integrable_of_strip_decay
    (a b C : ℝ) (f : ℂ → ℂ) (U : Set ℂ)
    (hab : a < b) (hC : 0 ≤ C)
    (hU : IsOpen U) (hstrip : comparisonClosedStrip a b ⊆ U)
    (hhol : DifferentiableOn ℂ f U)
    (hdecay : ∀ s ∈ comparisonClosedStrip a b,
      ‖f s‖ ≤ C * (1 + |s.im|) ^ (-2 : ℝ)) :
    ∀ σ ∈ Set.Icc a b, Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) := by
  intro σ hσ
  have hc : Continuous (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by
      intro t
      apply hstrip
      simpa [comparisonClosedStrip] using hσ)
  apply ComparisonShiftProof.integrable_tail _ C hc
  intro t ht
  simpa using hdecay ((σ : ℂ) + (t : ℂ) * I)
    (by simpa [comparisonClosedStrip] using hσ)

theorem verticalIntegral_eq_of_strip_decay
    (a b C : ℝ) (f : ℂ → ℂ) (U : Set ℂ)
    (hab : a < b) (hC : 0 ≤ C)
    (hU : IsOpen U) (hstrip : comparisonClosedStrip a b ⊆ U)
    (hhol : DifferentiableOn ℂ f U)
    (hdecay : ∀ s ∈ comparisonClosedStrip a b,
      ‖f s‖ ≤ C * (1 + |s.im|) ^ (-2 : ℝ)) :
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I) := by
  have hFs : DifferentiableOn ℂ f {s : ℂ | a ≤ s.re ∧ s.re ≤ b} :=
    hhol.mono hstrip
  have hi := verticalIntegral_integrable_of_strip_decay a b C f U hab hC hU hstrip hhol hdecay
  have hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, 1 ≤ |y| →
      ‖f ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ (-2 : ℝ) := by
    intro x hx y hy
    simpa using hdecay ((x : ℂ) + y * I) (by simpa [comparisonClosedStrip] using hx)
  exact ComparisonShiftProof.rectangle_limits f hab.le hFs
    (intervalIntegral_tendsto_integral (hi a ⟨le_rfl, hab.le⟩) tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral (hi b ⟨hab.le, le_rfl⟩) tendsto_neg_atTop_atBot tendsto_id)
    (by simpa using ComparisonShiftProof.horizontal_decay_limit f a b C (-1) hab.le (by norm_num) hbound)
    (by simpa using ComparisonShiftProof.horizontal_decay_limit f a b C 1 hab.le (by norm_num) hbound)

theorem verticalIntegral_rectangle_difference
    (a b T : ℝ) (f : ℂ → ℂ)
    (hab : a < b) (hT : 0 < T)
    (hhol : DifferentiableOn ℂ f
      {s : ℂ | a ≤ s.re ∧ s.re ≤ b ∧ -T ≤ s.im ∧ s.im ≤ T}) :
    (∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * I)) -
        (∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * I)) =
      -I * ((∫ x : ℝ in a..b, f ((x : ℂ) + (-T : ℝ) * I)) -
        (∫ x : ℝ in a..b, f ((x : ℂ) + (T : ℂ) * I))) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (-T : ℝ) * I) ((b : ℂ) + (T : ℂ) * I) (hhol.mono ?_)
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, zero_add,
      mul_one, smul_eq_mul] at h
    have h' := congrArg (fun z : ℂ => I * z) h
    simp only [mul_add, mul_sub, ← mul_assoc, I_mul_I, neg_one_mul, mul_zero] at h'
    linear_combination h'
  · intro s hs
    have hs' : s ∈ Set.Icc a b ×ℂ Set.Icc (-T) T := by
      simpa [Set.uIcc_of_le hab.le,
        Set.uIcc_of_le (show -T ≤ T by linarith)] using hs
    exact ⟨hs'.1.1, hs'.1.2, hs'.2.1, hs'.2.2⟩

end
end DedekindZetaZeroFree
