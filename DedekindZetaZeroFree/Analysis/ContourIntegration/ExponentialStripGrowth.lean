module

public import DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean.
-/

noncomputable section
open MeasureTheory Filter intervalIntegral
open scoped NumberField Classical Topology Interval

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def stripReg (f : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  f s * Complex.exp ((ε : ℂ) * s ^ 2)

private lemma norm_exp_eps_sq (ε x T : ℝ) :
    ‖Complex.exp ((ε : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I) ^ 2)‖
      = Real.exp (ε * (x ^ 2 - T ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
    sub_zero, zero_mul, mul_one, sub_neg_eq_add, zero_add]

private lemma tendsto_stripReg_zero (f : ℂ → ℂ) (s : ℂ) :
    Tendsto (fun ε : ℝ => stripReg f ε s) (𝓝[>] (0 : ℝ)) (𝓝 (f s)) := by
  have h1 : Tendsto (fun ε : ℝ => (ε : ℂ) * s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h.mul_const (s ^ 2)
  have h2 : Tendsto (fun ε : ℝ => Complex.exp ((ε : ℂ) * s ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Complex.continuous_exp.tendsto 0).comp h1
    have h' : Tendsto (fun ε : ℝ => Complex.exp ((ε : ℂ) * s ^ 2)) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.exp 0)) := h
    rwa [Complex.exp_zero] at h'
  simpa [stripReg] using tendsto_const_nhds.mul h2

theorem integral_eq_of_exponential_strip_growth {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    (ha : Complex.VerticalIntegrable f a)
    (hb : Complex.VerticalIntegrable f b)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a b → ∀ t : ℝ,
        ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ B * Real.exp (A * |t|)) :
    verticalIntegral a f = verticalIntegral b f := by
  obtain ⟨A, B, hA, hB, hgrow⟩ := hgrowth

  have hIntReg : ∀ (ε : ℝ) (c : ℝ), 0 ≤ ε → Complex.VerticalIntegrable f c →
      Integrable (fun y : ℝ => stripReg f ε ((c : ℂ) + y * Complex.I)) := by
    intro ε c hε hc
    refine (hc.norm.const_mul (Real.exp (ε * c ^ 2))).mono' ?_ ?_
    · exact hc.aestronglyMeasurable.mul (by fun_prop)
    · refine Eventually.of_forall fun y => ?_
      rw [stripReg, norm_mul, norm_exp_eps_sq]
      have h1 : Real.exp (ε * (c ^ 2 - y ^ 2)) ≤ Real.exp (ε * c ^ 2) :=
        Real.exp_le_exp.mpr (by
          rw [mul_sub]
          linarith [mul_nonneg hε (sq_nonneg y)])
      calc ‖f ((c : ℂ) + y * Complex.I)‖ * Real.exp (ε * (c ^ 2 - y ^ 2))
          = Real.exp (ε * (c ^ 2 - y ^ 2)) * ‖f ((c : ℂ) + y * Complex.I)‖ := mul_comm _ _
        _ ≤ Real.exp (ε * c ^ 2) * ‖f ((c : ℂ) + y * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

  have key : ∀ ε : ℝ, 0 < ε →
      (∫ y : ℝ, stripReg f ε ((a : ℂ) + y * Complex.I)) =
      (∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I)) := by
    intro ε hε
    have hIntA := hIntReg ε a hε.le ha
    have hIntB := hIntReg ε b hε.le hb
    set VA : ℝ → ℂ := fun T => ∫ y in (-T)..T, stripReg f ε ((a : ℂ) + y * Complex.I)
      with hVA
    set VB : ℝ → ℂ := fun T => ∫ y in (-T)..T, stripReg f ε ((b : ℂ) + y * Complex.I)
      with hVB

    have hC : ∀ T : ℝ,
        Complex.I * ((∫ y in (-T)..T, stripReg f ε ((b : ℂ) + y * Complex.I)) -
            (∫ y in (-T)..T, stripReg f ε ((a : ℂ) + y * Complex.I))) =
          (∫ x in a..b, stripReg f ε ((x : ℂ) + (T : ℂ) * Complex.I)) -
            (∫ x in a..b, stripReg f ε ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
      intro T
      have hd : DifferentiableOn ℂ (stripReg f ε) ([[a, b]] ×ℂ [[(-T : ℝ), T]]) := by
        intro s hs
        rw [Complex.mem_reProdIm] at hs
        have hsr : a ≤ s.re ∧ s.re ≤ b := by
          have h := hs.1
          rwa [Set.uIcc_of_le hab] at h
        have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.exp ((ε : ℂ) * s ^ 2)) s :=
          ((differentiableAt_const (c := (ε : ℂ))).mul (differentiableAt_id.pow 2)).cexp
        exact ((hf s hsr.1 hsr.2).mul h2).differentiableWithinAt
      have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (stripReg f ε)
        (Complex.mk a (-T)) (Complex.mk b T) hd
      simp only [smul_eq_mul] at h
      linear_combination h

    set M : ℝ := max |a| |b| with hM
    have hMnonneg : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
    have hxM : ∀ x : ℝ, x ∈ Set.Icc a b → |x| ≤ M := by
      intro x hx
      rw [abs_le]
      exact ⟨le_trans (le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le a)) hx.1,
        le_trans hx.2 (le_trans (le_abs_self b) (le_max_right _ _))⟩
    have hxMsq : ∀ x : ℝ, x ∈ Set.Icc a b → x ^ 2 ≤ M ^ 2 := by
      intro x hx
      rw [← sq_abs x, sq, sq]
      exact mul_le_mul (hxM x hx) (hxM x hx) (abs_nonneg x) hMnonneg
    have hbound : ∀ x : ℝ, x ∈ Set.Icc a b → ∀ t : ℝ,
        ‖stripReg f ε ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          B * Real.exp (ε * M ^ 2 + A * |t| - ε * t ^ 2) := by
      intro x hx t
      calc ‖stripReg f ε ((x : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖f ((x : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (ε * (x ^ 2 - t ^ 2)) := by
            rw [stripReg, norm_mul, norm_exp_eps_sq]
        _ ≤ (B * Real.exp (A * |t|)) * Real.exp (ε * (x ^ 2 - t ^ 2)) :=
            mul_le_mul_of_nonneg_right (hgrow x hx t) (Real.exp_nonneg _)
        _ = B * Real.exp (A * |t| + ε * (x ^ 2 - t ^ 2)) := by
            rw [Real.exp_add]; ring
        _ ≤ B * Real.exp (ε * M ^ 2 + A * |t| - ε * t ^ 2) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
            nlinarith [hxMsq x hx, hε.le]
    have hu : Tendsto (fun T : ℝ => ε * T ^ 2 - A * T - ε * M ^ 2) atTop atTop := by
      have hlin : Tendsto (fun T : ℝ => ε * T + (-A)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-A)
          ((tendsto_const_mul_atTop_of_pos hε).mpr tendsto_id)
      have hmul : Tendsto (fun T : ℝ => T * (ε * T + (-A))) atTop atTop :=
        tendsto_id.atTop_mul_atTop₀ hlin
      have hfin : Tendsto (fun T : ℝ => T * (ε * T + (-A)) + (-(ε * M ^ 2))) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-(ε * M ^ 2)) hmul
      refine hfin.congr' (Eventually.of_forall fun T => ?_)
      ring_nf
    have hexp : Tendsto (fun T : ℝ => Real.exp (ε * M ^ 2 + A * T - ε * T ^ 2))
        atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hu)
      refine h.congr' (Eventually.of_forall fun T => ?_)
      simp only [Function.comp_apply, Real.exp_injective.eq_iff]
      ring_nf
    have hexp' : Tendsto (fun T : ℝ => Real.exp (ε * M ^ 2 + A * |T| - ε * T ^ 2))
        atTop (𝓝 0) := by
      refine hexp.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [abs_of_nonneg hT]
    have hHB : Tendsto (fun T : ℝ => B * Real.exp (ε * M ^ 2 + A * |T| - ε * T ^ 2))
        atTop (𝓝 0) := by
      simpa using hexp'.const_mul B
    have hHA : Tendsto (fun T : ℝ => ∫ x in a..b, stripReg f ε ((x : ℂ) + (T : ℂ) * Complex.I))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _)
        (Eventually.of_forall fun T => ?_) (by simpa using hHB.mul_const |b - a|)
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      have hx' : x ∈ Set.Icc a b := by
        have h := hx
        rw [Set.uIoc_of_le hab] at h
        exact Set.Ioc_subset_Icc_self h
      exact hbound x hx' T
    have hHAm : Tendsto
        (fun T : ℝ => ∫ x in a..b, stripReg f ε ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _)
        (Eventually.of_forall fun T => ?_) (by simpa using hHB.mul_const |b - a|)
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      have hx' : x ∈ Set.Icc a b := by
        have h := hx
        rw [Set.uIoc_of_le hab] at h
        exact Set.Ioc_subset_Icc_self h
      simpa only [abs_neg, neg_sq] using hbound x hx' (-T)

    have tVA : Tendsto VA atTop (𝓝 (∫ y : ℝ, stripReg f ε ((a : ℂ) + y * Complex.I))) := by
      rw [hVA]
      exact intervalIntegral_tendsto_integral hIntA tendsto_neg_atTop_atBot tendsto_id
    have tVB : Tendsto VB atTop (𝓝 (∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I))) := by
      rw [hVB]
      exact intervalIntegral_tendsto_integral hIntB tendsto_neg_atTop_atBot tendsto_id
    have t1 : Tendsto (fun T : ℝ => Complex.I *
          ((∫ y in (-T)..T, stripReg f ε ((b : ℂ) + y * Complex.I)) -
            (∫ y in (-T)..T, stripReg f ε ((a : ℂ) + y * Complex.I))))
        atTop (𝓝 (Complex.I * ((∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I)) -
            (∫ y : ℝ, stripReg f ε ((a : ℂ) + y * Complex.I))))) :=
      (tVB.sub tVA).const_mul Complex.I
    have t2 : Tendsto (fun T : ℝ => Complex.I *
          ((∫ y in (-T)..T, stripReg f ε ((b : ℂ) + y * Complex.I)) -
            (∫ y in (-T)..T, stripReg f ε ((a : ℂ) + y * Complex.I))))
        atTop (𝓝 0) := by
      have h3 : Tendsto (fun T : ℝ =>
          (∫ x in a..b, stripReg f ε ((x : ℂ) + (T : ℂ) * Complex.I)) -
            (∫ x in a..b, stripReg f ε ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
          atTop (𝓝 0) := by simpa using hHA.sub hHAm
      exact Tendsto.congr' (Eventually.of_forall fun T => (hC T).symm) h3
    have hlim : Complex.I * ((∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I)) -
        (∫ y : ℝ, stripReg f ε ((a : ℂ) + y * Complex.I))) = 0 :=
      tendsto_nhds_unique t1 t2
    rcases mul_eq_zero.mp hlim with h0 | h0
    · exact absurd h0 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h0).symm

  have hlimit : ∀ c : ℝ, Complex.VerticalIntegrable f c →
      Tendsto (fun ε : ℝ => ∫ y : ℝ, stripReg f ε ((c : ℂ) + y * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ y : ℝ, f ((c : ℂ) + y * Complex.I))) := by
    intro c hc
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => Real.exp (c ^ 2) * ‖f ((c : ℂ) + y * Complex.I)‖) ?_ ?_ ?_ ?_
    · filter_upwards with ε
      exact hc.aestronglyMeasurable.mul (by fun_prop)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      refine Eventually.of_forall fun y => ?_
      rw [stripReg, norm_mul, norm_exp_eps_sq]
      calc ‖f ((c : ℂ) + y * Complex.I)‖ * Real.exp (ε * (c ^ 2 - y ^ 2))
          = Real.exp (ε * (c ^ 2 - y ^ 2)) * ‖f ((c : ℂ) + y * Complex.I)‖ := mul_comm _ _
        _ ≤ Real.exp (c ^ 2) * ‖f ((c : ℂ) + y * Complex.I)‖ := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
            nlinarith [mul_nonneg hε.1.le (sq_nonneg y),
              mul_le_of_le_one_left (sq_nonneg c) hε.2.le]
    · exact hc.norm.const_mul _
    · refine Eventually.of_forall fun y => tendsto_stripReg_zero f ((c : ℂ) + y * Complex.I)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ y : ℝ, stripReg f ε ((a : ℂ) + y * Complex.I)) =
      (∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact key ε hε
  have hBeq : Tendsto (fun ε : ℝ => ∫ y : ℝ, stripReg f ε ((b : ℂ) + y * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ y : ℝ, f ((a : ℂ) + y * Complex.I))) :=
    Tendsto.congr' hev (hlimit a ha)
  have heq : (∫ y : ℝ, f ((a : ℂ) + y * Complex.I)) =
      (∫ y : ℝ, f ((b : ℂ) + y * Complex.I)) :=
    tendsto_nhds_unique hBeq (hlimit b hb)
  simp only [verticalIntegral, heq]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
