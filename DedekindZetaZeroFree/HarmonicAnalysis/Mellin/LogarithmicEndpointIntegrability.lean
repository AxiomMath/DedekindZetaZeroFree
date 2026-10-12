module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicWeights
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginLaurentAndLogarithmicResidues

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Classical Topology ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor
namespace LogMellinPhysical

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}

private lemma contDiffOn_eulerIter {a : ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (j : ℕ) : ContDiffOn ℝ ∞ (EulerIter j a) (Set.Ioi 0) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    have hderiv : ContDiffOn ℝ ∞ (deriv (EulerIter j a)) (Set.Ioi 0) :=
      ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hmul : ContDiffOn ℝ ∞
        (fun x : ℝ => (x : ℂ) * deriv (EulerIter j a) x) (Set.Ioi 0) :=
      (Complex.ofRealCLM.contDiff.contDiffOn).mul hderiv
    refine hmul.congr ?_
    intro x hx
    exact EulerIter_succ_of_pos j a x hx

private lemma eulerIter_add_of_pos {a b : ℝ → ℂ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (hb : ContDiffOn ℝ ∞ b (Set.Ioi 0)) (j : ℕ) :
    ∀ x : ℝ, 0 < x →
      EulerIter j (fun y => a y + b y) x = EulerIter j a x + EulerIter j b x := by
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    have hda : DifferentiableAt ℝ (EulerIter j a) x :=
      ((contDiffOn_eulerIter ha j).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hdb : DifferentiableAt ℝ (EulerIter j b) x :=
      ((contDiffOn_eulerIter hb j).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hcongr : EulerIter j (fun y => a y + b y) =ᶠ[𝓝 x]
        (fun y => EulerIter j a y + EulerIter j b y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih y hy
    rw [EulerIter_succ_of_pos _ _ _ hx, EulerIter_succ_of_pos _ _ _ hx,
      EulerIter_succ_of_pos _ _ _ hx, hcongr.deriv_eq,
      show deriv (fun y => EulerIter j a y + EulerIter j b y) x =
          deriv (EulerIter j a) x + deriv (EulerIter j b) x from deriv_add hda hdb]
    ring

private lemma log_pow_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Real.log x| ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * x ^ (-ε) := by
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have ht : 0 ≤ -Real.log x := by linarith
  have habs : |Real.log x| = -Real.log x := abs_of_nonpos hlog
  have hεk : (0 : ℝ) < ε ^ k := pow_pos hε k
  have hbound := Real.pow_div_factorial_le_exp (ε * (-Real.log x)) (mul_nonneg hε.le ht) k
  rw [mul_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (k.factorial : ℝ))] at hbound
  have hexp : Real.exp (ε * (-Real.log x)) = x ^ (-ε) := by
    rw [Real.rpow_def_of_pos hx0]; congr 1; ring
  rw [hexp] at hbound
  rw [habs]
  calc (-Real.log x) ^ k
      ≤ ((k.factorial : ℝ) * x ^ (-ε)) / ε ^ k := by
        rw [le_div_iff₀ hεk]; linarith [hbound]
    _ = ((k.factorial : ℝ) / ε ^ k) * x ^ (-ε) := by ring

private lemma polynomial_eval_log_bound (Q : Polynomial ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖Q.eval (Real.log x : ℂ)‖ ≤ C * x ^ (-ε) := by
  refine ⟨∑ k ∈ Q.support, ‖Q.coeff k‖ * ((k.factorial : ℝ) / ε ^ k), by positivity, ?_⟩
  intro x hx0 hx1
  have hz : ‖(Real.log x : ℂ)‖ = |Real.log x| := by
    have h2 : ‖(Real.log x : ℂ)‖ ^ 2 = |Real.log x| ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
      ring
    nlinarith [norm_nonneg (Real.log x : ℂ), abs_nonneg (Real.log x)]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc ‖∑ e ∈ Q.support, Q.coeff e * (Real.log x : ℂ) ^ e‖
      ≤ ∑ e ∈ Q.support, ‖Q.coeff e * (Real.log x : ℂ) ^ e‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ Q.support, ‖Q.coeff e‖ * (((e.factorial : ℝ) / ε ^ e) * x ^ (-ε)) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [norm_mul, norm_pow, hz]
        gcongr
        exact log_pow_le_rpow e ε hε x hx0 hx1
    _ = (∑ e ∈ Q.support, ‖Q.coeff e‖ * ((e.factorial : ℝ) / ε ^ e)) * x ^ (-ε) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun e _ => by ring

private lemma contDiffOn_eval_log (P : Polynomial ℂ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => P.eval (Real.log y : ℂ)) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => P.eval z) := by
    have h : ContDiff ℂ ∞ (fun z : ℂ => P.aeval z) := Polynomial.contDiff_aeval P ∞
    have h' : ContDiff ℝ ∞ (fun z : ℂ => P.aeval z) := h.restrict_scalars ℝ
    simpa only [Polynomial.coe_aeval_eq_eval] using h'
  have h2 : ContDiffOn ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) (Set.Ioi 0) := by
    have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
      Real.contDiffOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hx)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  exact h1.comp_contDiffOn h2

private lemma eulerIter_sub_originPolynomial_eq (h : LogMellinPhysical f δ P) (j : ℕ) :
    ∀ x : ℝ, 0 < x →
      EulerIter j f x =
        EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x +
          Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j]) P) := by
  intro x hx
  have hf' : ContDiffOn ℝ ∞ (fun y : ℝ => f y - P.eval (Real.log y : ℂ)) (Set.Ioi 0) :=
    h.contDiffOn.sub (contDiffOn_eval_log P)
  have hp' : ContDiffOn ℝ ∞ (fun y : ℝ => P.eval (Real.log y : ℂ)) (Set.Ioi 0) :=
    contDiffOn_eval_log P
  have hsplit := eulerIter_add_of_pos hf' hp' j x hx
  have hfun : (fun y : ℝ => (f y - P.eval (Real.log y : ℂ)) + P.eval (Real.log y : ℂ)) = f := by
    funext y; ring
  rw [hfun] at hsplit
  rw [hsplit, EulerIter_eval_log_polynomial P j x hx]

private lemma eulerIter_eq_remainder_of_degree_lt (h : LogMellinPhysical f δ P) (j : ℕ)
    (hj : P.natDegree < j) :
    ∀ x : ℝ, 0 < x →
      EulerIter j f x = EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x := by
  intro x hx
  rw [eulerIter_sub_originPolynomial_eq h j x hx, Polynomial.iterate_derivative_eq_zero hj]
  simp

theorem euler_origin_bound (h : LogMellinPhysical f δ P) (j : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖EulerIter j f x‖ ≤ C * Real.rpow x (-ε) := by
  obtain ⟨C₁, hC₁, hbound₁⟩ := h.origin_remainder j
  obtain ⟨C₂, hC₂, hbound₂⟩ := polynomial_eval_log_bound ((Polynomial.derivative^[j]) P) ε hε
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro x hx0 hx1
  rw [eulerIter_sub_originPolynomial_eq h j x hx0]
  calc ‖EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x +
          Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j]) P)‖
      ≤ ‖EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x‖ +
          ‖Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j]) P)‖ := norm_add_le _ _
    _ ≤ C₁ * Real.rpow x δ + C₂ * Real.rpow x (-ε) :=
        add_le_add (hbound₁ x hx0 hx1) (hbound₂ x hx0 hx1)
    _ ≤ (C₁ + C₂) * Real.rpow x (-ε) := by
        have hδ : Real.rpow x δ ≤ Real.rpow x (-ε) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith [h.delta_pos, hε])
        calc C₁ * Real.rpow x δ + C₂ * Real.rpow x (-ε)
            ≤ C₁ * Real.rpow x (-ε) + C₂ * Real.rpow x (-ε) := by
              gcongr
          _ = (C₁ + C₂) * Real.rpow x (-ε) := by ring

theorem euler_mellinConvergent (h : LogMellinPhysical f δ P) (j : ℕ)
    (s : ℂ) (hs : 0 < s.re) : MellinConvergent (EulerIter j f) s := by
  obtain ⟨N, hN⟩ := exists_nat_gt s.re
  obtain ⟨C₂, hC₂, hbound₂⟩ := h.rapid_decay j N
  obtain ⟨C₁, hC₁, hbound₁⟩ := euler_origin_bound h j (s.re / 4) (by linarith)
  refine mellinConvergent_of_isBigO_rpow (a := (N : ℝ)) (b := s.re / 2) ?_ ?_ ?_ ?_ ?_
  · exact (contDiffOn_eulerIter h.contDiffOn j).continuousOn.locallyIntegrableOn measurableSet_Ioi
  · refine IsBigO.of_bound C₂ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
    exact hbound₂ x hx
  · exact hN
  · refine IsBigO.of_bound C₁ ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc ‖EulerIter j f x‖ ≤ C₁ * Real.rpow x (-(s.re / 4)) := hbound₁ x hx.1 hx.2
      _ ≤ C₁ * Real.rpow x (-(s.re / 2)) := by
          have hle : -(s.re / 2) ≤ -(s.re / 4) := by linarith
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hle) hC₁
  · linarith

theorem euler_cpow_tendsto_atTop (h : LogMellinPhysical f δ P) (j : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * EulerIter j f x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt s.re
  obtain ⟨C, hC, hbound⟩ := h.rapid_decay j N
  have hNpos : 0 < (N : ℝ) - s.re := by linarith
  have hlim : Tendsto (fun x : ℝ => C * Real.rpow x (-((N : ℝ) - s.re))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hNpos).const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hfx := hbound x hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hexp : s.re + -(N : ℝ) = -((N : ℝ) - s.re) := by ring
  calc x ^ s.re * ‖EulerIter j f x‖
      ≤ x ^ s.re * (C * Real.rpow x (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hfx (Real.rpow_nonneg hx0.le _)
    _ = C * Real.rpow x (-((N : ℝ) - s.re)) := by
        have hprod : x ^ s.re * Real.rpow x (-(N : ℝ)) = Real.rpow x (-((N : ℝ) - s.re)) := by
          have := Real.rpow_add hx0 s.re (-(N : ℝ))
          rw [hexp] at this
          exact this.symm
        rw [mul_left_comm (x ^ s.re) C, hprod]

theorem euler_cpow_tendsto_origin (h : LogMellinPhysical f δ P) (j : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * EulerIter j f x)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := euler_origin_bound h j (s.re / 2) (by linarith)
  have ht : Tendsto (fun x : ℝ => C * Real.rpow x (s.re / 2)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Tendsto (fun x : ℝ => Real.rpow x (s.re / 2)) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const (0 : ℝ) (s.re / 2) (Or.inr (by linarith))).tendsto
      simpa [Real.zero_rpow (by linarith : s.re / 2 ≠ 0)] using h
    simpa using tendsto_const_nhds.mul (hcont.mono_left nhdsWithin_le_nhds)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with x hx
  have hfx := hbound x hx.1 hx.2
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hexp : s.re + -(s.re / 2) = s.re / 2 := by ring
  calc x ^ s.re * ‖EulerIter j f x‖
      ≤ x ^ s.re * (C * Real.rpow x (-(s.re / 2))) :=
        mul_le_mul_of_nonneg_left hfx (Real.rpow_nonneg hx.1.le _)
    _ = C * Real.rpow x (s.re / 2) := by
        have hprod : x ^ s.re * Real.rpow x (-(s.re / 2)) = Real.rpow x (s.re / 2) := by
          have := Real.rpow_add hx.1 s.re (-(s.re / 2))
          rw [hexp] at this
          exact this.symm
        rw [mul_left_comm (x ^ s.re) C, hprod]

theorem high_euler_mellinConvergent (h : LogMellinPhysical f δ P) (j : ℕ)
    (hj : P.natDegree < j) (s : ℂ) (hs : -δ < s.re) :
    MellinConvergent (EulerIter j f) s := by
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b : ℝ, -δ ≤ b ∧ b < s.re :=
    ⟨(-δ + s.re) / 2, by linarith, by linarith⟩
  obtain ⟨N, hN⟩ := exists_nat_gt s.re
  obtain ⟨C₂, hC₂, hbound₂⟩ := h.rapid_decay j N
  obtain ⟨C₁, hC₁, hbound₁⟩ := h.origin_remainder j
  refine mellinConvergent_of_isBigO_rpow (a := (N : ℝ)) (b := b) ?_ ?_ ?_ ?_ hb₂
  · exact (contDiffOn_eulerIter h.contDiffOn j).continuousOn.locallyIntegrableOn measurableSet_Ioi
  · refine IsBigO.of_bound C₂ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
    exact hbound₂ x hx
  · exact hN
  · refine IsBigO.of_bound (max C₁ 1) ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
      eulerIter_eq_remainder_of_degree_lt h j hj x hx.1]
    calc ‖EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x‖
        ≤ C₁ * Real.rpow x δ := hbound₁ x hx.1 hx.2
      _ ≤ max C₁ 1 * Real.rpow x (-b) := by
          have hδ : Real.rpow x δ ≤ Real.rpow x (-b) :=
            Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
          calc C₁ * Real.rpow x δ ≤ C₁ * Real.rpow x (-b) :=
                mul_le_mul_of_nonneg_left hδ hC₁
            _ ≤ max C₁ 1 * Real.rpow x (-b) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.1.le _)

theorem high_euler_uniform_mellin_norm (h : LogMellinPhysical f δ P) (j : ℕ)
    (hj : P.natDegree < j) (u v : ℝ) (hu : -δ < u) (huv : u ≤ v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      MellinConvergent (EulerIter j f) s ∧
      (∫ x in Set.Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * EulerIter j f x‖) ≤ C := by
  obtain ⟨n, hn⟩ := exists_nat_gt v
  obtain ⟨C₂, hC₂, hbound₂⟩ := h.rapid_decay j n
  obtain ⟨C₁, hC₁, hbound₁⟩ := h.origin_remainder j
  have huδ : 0 < u + δ := by linarith
  have hnv : 0 < (n : ℝ) - v := by linarith
  set h₁ : ℝ → ℝ := fun x => C₁ * x ^ (u - 1 + δ) with hh₁
  set h₂ : ℝ → ℝ := fun x => C₂ * x ^ (v - 1 - (n : ℝ)) with hh₂
  have hint₁ : IntegrableOn h₁ (Set.Ioc (0 : ℝ) 1) volume := by
    rw [hh₁]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow'
        (by linarith : -1 < u - 1 + δ))).const_mul C₁
  have hint₂ : IntegrableOn h₂ (Set.Ioi (1 : ℝ)) volume := by
    rw [hh₂]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : v - 1 - (n : ℝ) < -1) one_pos).const_mul C₂
  have hintG₁ : IntegrableOn ((Set.Ioc (0 : ℝ) 1).indicator h₁) (Set.Ioi 0) volume := by
    rw [integrableOn_indicator_iff measurableSet_Ioc.nullMeasurableSet]
    exact hint₁.mono_set (fun x hx => hx.1)
  have hintG₂ : IntegrableOn ((Set.Ioi (1 : ℝ)).indicator h₂) (Set.Ioi 0) volume := by
    rw [integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet]
    exact hint₂.mono_set (fun x hx => hx.1)
  set G : ℝ → ℝ := fun x =>
    (Set.Ioc (0 : ℝ) 1).indicator h₁ x + (Set.Ioi (1 : ℝ)).indicator h₂ x with hG
  have hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) volume := by
    rw [hG]
    exact hintG₁.add hintG₂
  refine ⟨C₁ / (u + δ) + C₂ / ((n : ℝ) - v), by positivity, ?_⟩
  intro s hs1 hs2
  refine ⟨high_euler_mellinConvergent h j hj s (by linarith), ?_⟩
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖(x : ℂ) ^ (s - 1) * EulerIter j f x‖ ≤ G x := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [hG]; simp only [Pi.add_apply]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
    rcases le_or_gt x 1 with hle | hgt
    · rw [Set.indicator_of_mem (show x ∈ Set.Ioc (0 : ℝ) 1 from ⟨hx0, hle⟩),
        Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith), add_zero]
      have hfx : ‖EulerIter j f x‖ ≤ C₁ * x ^ δ := by
        rw [eulerIter_eq_remainder_of_degree_lt h j hj x hx0]
        exact hbound₁ x hx0 hle
      calc x ^ (s.re - 1) * ‖EulerIter j f x‖
          ≤ x ^ (s.re - 1) * (C₁ * x ^ δ) :=
            mul_le_mul_of_nonneg_left hfx (Real.rpow_nonneg hx0.le _)
        _ = C₁ * x ^ (s.re - 1 + δ) := by
            rw [mul_left_comm (x ^ (s.re - 1)) C₁, ← Real.rpow_add hx0]
        _ ≤ C₁ * x ^ (u - 1 + δ) := by
            have hle' : x ^ (s.re - 1 + δ) ≤ x ^ (u - 1 + δ) :=
              Real.rpow_le_rpow_of_exponent_ge hx0 hle (by linarith)
            exact mul_le_mul_of_nonneg_left hle' hC₁
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioc]; intro hcon; linarith [hcon.2]),
        Set.indicator_of_mem (show x ∈ Set.Ioi (1 : ℝ) from hgt), zero_add]
      have hfx : ‖EulerIter j f x‖ ≤ C₂ * x ^ (-(n : ℝ)) := hbound₂ x hgt.le
      calc x ^ (s.re - 1) * ‖EulerIter j f x‖
          ≤ x ^ (s.re - 1) * (C₂ * x ^ (-(n : ℝ))) :=
            mul_le_mul_of_nonneg_left hfx (Real.rpow_nonneg hx0.le _)
        _ = C₂ * x ^ (s.re - 1 - (n : ℝ)) := by
            rw [mul_left_comm (x ^ (s.re - 1)) C₂, ← Real.rpow_add hx0]; ring_nf
        _ ≤ C₂ * x ^ (v - 1 - (n : ℝ)) := by
            have hle' : x ^ (s.re - 1 - (n : ℝ)) ≤ x ^ (v - 1 - (n : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
            exact mul_le_mul_of_nonneg_left hle' hC₂
  have hfin : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) * EulerIter j f x‖)
      (Set.Ioi (0 : ℝ)) volume :=
    (high_euler_mellinConvergent h j hj s (by linarith)).norm
  calc ∫ x in Set.Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * EulerIter j f x‖
      ≤ ∫ x in Set.Ioi (0 : ℝ), G x :=
        setIntegral_mono_on hfin hGint measurableSet_Ioi hpt
    _ = C₁ / (u + δ) + C₂ / ((n : ℝ) - v) := by
        rw [hG]; simp only [Pi.add_apply]
        rw [integral_add hintG₁ hintG₂]
        congr 1
        · rw [integral_indicator measurableSet_Ioc, hh₁,
              Measure.restrict_restrict_of_subset (fun x hx => hx.1),
              integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
              integral_rpow (Or.inl (by linarith : -1 < u - 1 + δ))]
          rw [Real.one_rpow, Real.zero_rpow (by linarith : u - 1 + δ + 1 ≠ 0), sub_zero]
          ring
        · rw [integral_indicator measurableSet_Ioi, hh₂,
              Measure.restrict_restrict_of_subset (fun x hx => by
                simp only [Set.mem_Ioi] at hx ⊢; linarith),
              integral_const_mul,
              integral_Ioi_rpow_of_lt (by linarith : v - 1 - (n : ℝ) < -1) one_pos,
              Real.one_rpow]
          rw [show v - 1 - ↑n + 1 = -(↑n - v) by ring, neg_div_neg_eq]
          ring

end LogMellinPhysical
end DedekindZetaZeroFree.LargeSieve.Vendor

end
