module

public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory Complex

private lemma norm_exp_sq_le (w : ℂ) (K : ℝ) (hK : w.re ^ 2 ≤ K) :
    ‖Complex.exp (w ^ 2)‖ ≤ Real.exp K * Real.exp (-(w.im ^ 2)) := by
  rw [Complex.norm_exp]
  have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  rw [h2, sub_eq_add_neg, Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hK) (Real.exp_nonneg _)

private lemma rpow_two_add_le (x B : ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B) :
    (2 + x) ^ B ≤ 2 ^ B * (1 + x) ^ B := by
  have h : (2 + x) ^ B ≤ (2 * (1 + x)) ^ B :=
    Real.rpow_le_rpow (by linarith) (by linarith) hB
  rwa [Real.mul_rpow (by norm_num) (by linarith)] at h

def comparisonRapidStripDecay (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ s ∈ comparisonClosedStrip a b, ‖f s‖ ≤ C * (1 + |s.im|) ^ (-A)

def comparisonGaussianMellinWeight (M W : ℂ → ℂ) (ξ w z : ℂ) : ℂ :=
  Complex.exp ((ξ + z - 1) ^ 2) * M z * W w

def comparisonHeightEnvelope (A t τ ν : ℝ) : ℝ :=
  Real.exp (-(t + ν) ^ 2) * (1 + |ν|) ^ (-A) * (1 + |τ|) ^ (-A)

theorem comparisonGaussianMellinWeight_polynomial_bound
    (M W : ℂ → ℂ) (a b c d e f A B D : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) (he : 0 < e)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hM : comparisonRapidStripDecay M e f)
    (hW : comparisonRapidStripDecay W c d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip a b → w ∈ comparisonClosedStrip c d →
      z ∈ comparisonClosedStrip e f →
      ‖comparisonGaussianMellinWeight M W ξ w z‖ *
          (2 + |w.im|) ^ B * (2 + |z.im|) ^ D ≤
        C * comparisonHeightEnvelope A ξ.im w.im z.im := by
  obtain ⟨CM, hCMpos, hCM⟩ := hM (A + D) (by linarith)
  obtain ⟨CW, hCWpos, hCW⟩ := hW (A + B) (by linarith)
  refine ⟨Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * CM * CW * 2 ^ (B + D),
    by positivity, ?_⟩
  intro ξ w z hξ hw hz
  simp only [comparisonClosedStrip, Set.mem_setOf_eq] at hξ hw hz
  obtain ⟨hξa, hξb⟩ := hξ
  obtain ⟨hwc, hwd⟩ := hw
  obtain ⟨hze, hzf⟩ := hz
  have hK : (ξ + z - 1).re ^ 2 ≤ (|a| + |e| + |b| + |f| + 1) ^ 2 := by
    have hre : (ξ + z - 1).re = ξ.re + z.re - 1 := by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, sub_zero]
    rw [hre]
    have habs : |ξ.re + z.re - 1| ≤ |a| + |e| + |b| + |f| + 1 := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 := neg_abs_le a; have h2 := neg_abs_le e
        have h3 := abs_nonneg b; have h4 := abs_nonneg f; linarith
      · have h1 := le_abs_self b; have h2 := le_abs_self f
        have h3 := abs_nonneg a; have h4 := abs_nonneg e; linarith
    have h2 := pow_le_pow_left₀ (abs_nonneg (ξ.re + z.re - 1)) habs 2
    rwa [sq_abs] at h2
  have hexp : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ ≤
      Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) := by
    have h := norm_exp_sq_le (ξ + z - 1) ((|a| + |e| + |b| + |f| + 1) ^ 2) hK
    simpa only [Complex.add_im, Complex.sub_im, Complex.one_im, sub_zero] using h
  have hMz : ‖M z‖ ≤ CM * (1 + |z.im|) ^ (-(A + D)) :=
    hCM z (by simp only [comparisonClosedStrip, Set.mem_setOf_eq]; exact ⟨hze, hzf⟩)
  have hWw : ‖W w‖ ≤ CW * (1 + |w.im|) ^ (-(A + B)) :=
    hCW w (by simp only [comparisonClosedStrip, Set.mem_setOf_eq]; exact ⟨hwc, hwd⟩)
  have hB1 : (2 + |w.im|) ^ B ≤ 2 ^ B * (1 + |w.im|) ^ B :=
    rpow_two_add_le _ _ (abs_nonneg _) hB
  have hD1 : (2 + |z.im|) ^ D ≤ 2 ^ D * (1 + |z.im|) ^ D :=
    rpow_two_add_le _ _ (abs_nonneg _) hD
  have e1 : (1 + |z.im|) ^ (-(A + D)) * (1 + |z.im|) ^ D = (1 + |z.im|) ^ (-A) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |z.im|)]
    congr 1
    ring
  have e2 : (1 + |w.im|) ^ (-(A + B)) * (1 + |w.im|) ^ B = (1 + |w.im|) ^ (-A) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |w.im|)]
    congr 1
    ring
  have e3 : (2 : ℝ) ^ B * 2 ^ D = (2 : ℝ) ^ (B + D) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have s1 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ * ‖M z‖ ≤
      (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
        (CM * (1 + |z.im|) ^ (-(A + D))) :=
    mul_le_mul hexp hMz (norm_nonneg _) (by positivity)
  have s2 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ * ‖M z‖ * ‖W w‖ ≤
      (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
        (CM * (1 + |z.im|) ^ (-(A + D))) * (CW * (1 + |w.im|) ^ (-(A + B))) :=
    mul_le_mul s1 hWw (norm_nonneg _) (by positivity)
  have s3 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ * ‖M z‖ * ‖W w‖ * (2 + |w.im|) ^ B ≤
      (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
        (CM * (1 + |z.im|) ^ (-(A + D))) * (CW * (1 + |w.im|) ^ (-(A + B))) *
        (2 ^ B * (1 + |w.im|) ^ B) :=
    mul_le_mul s2 hB1 (by positivity) (by positivity)
  have s4 : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ * ‖M z‖ * ‖W w‖ * (2 + |w.im|) ^ B *
      (2 + |z.im|) ^ D ≤
      (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
        (CM * (1 + |z.im|) ^ (-(A + D))) * (CW * (1 + |w.im|) ^ (-(A + B))) *
        (2 ^ B * (1 + |w.im|) ^ B) * (2 ^ D * (1 + |z.im|) ^ D) :=
    mul_le_mul s3 hD1 (by positivity) (by positivity)
  have eq : (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
        (CM * (1 + |z.im|) ^ (-(A + D))) * (CW * (1 + |w.im|) ^ (-(A + B))) *
        (2 ^ B * (1 + |w.im|) ^ B) * (2 ^ D * (1 + |z.im|) ^ D) =
      Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * CM * CW * 2 ^ (B + D) *
        Real.exp (-(ξ.im + z.im) ^ 2) * (1 + |z.im|) ^ (-A) * (1 + |w.im|) ^ (-A) := by
    calc (Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2)) *
          (CM * (1 + |z.im|) ^ (-(A + D))) * (CW * (1 + |w.im|) ^ (-(A + B))) *
          (2 ^ B * (1 + |w.im|) ^ B) * (2 ^ D * (1 + |z.im|) ^ D)
        = Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) * CM *
            CW * ((1 + |z.im|) ^ (-(A + D)) * (1 + |z.im|) ^ D) *
            ((1 + |w.im|) ^ (-(A + B)) * (1 + |w.im|) ^ B) * (2 ^ B * 2 ^ D) := by
          ring
      _ = Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) * CM *
            CW * (1 + |z.im|) ^ (-A) * (1 + |w.im|) ^ (-A) * (2 ^ B * 2 ^ D) := by
          rw [e1, e2]
      _ = Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * Real.exp (-(ξ.im + z.im) ^ 2) * CM *
            CW * (1 + |z.im|) ^ (-A) * (1 + |w.im|) ^ (-A) * 2 ^ (B + D) := by
          rw [e3]
      _ = Real.exp ((|a| + |e| + |b| + |f| + 1) ^ 2) * CM * CW * 2 ^ (B + D) *
            Real.exp (-(ξ.im + z.im) ^ 2) * (1 + |z.im|) ^ (-A) * (1 + |w.im|) ^ (-A) := by
          ring
  rw [comparisonGaussianMellinWeight, norm_mul, norm_mul]
  refine s4.trans (le_of_eq ?_)
  rw [comparisonHeightEnvelope]
  exact eq.trans (by ring)

private lemma weight_shift (k t ν : ℝ) (hk : 0 ≤ k) :
    (1+|ν|)^(-k) ≤ (1+|t|)^(-k) * (1+|t+ν|)^k := by
  have ht : 1+|t| ≤ (1+|t+ν|)*(1+|ν|) := by
    have hh : |t| ≤ |t+ν|+|ν| := by
      simpa using abs_sub (t+ν) ν
    nlinarith [abs_nonneg (t+ν), abs_nonneg ν]
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1+|t|) ht hk
  rw [Real.mul_rpow (by positivity) (by positivity)] at hh
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  have hd : (1+|t|)^k / (1+|ν|)^k ≤ (1+|t+ν|)^k :=
    (div_le_iff₀ (by positivity)).mpr hh
  have hi := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ ((1+|t|)^k)⁻¹)
  have ht0 : (1+|t|)^k ≠ 0 := by positivity
  simpa [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ ht0] using hi

private lemma gauss_poly (k x : ℝ) (hk : 0 ≤ k) :
    Real.exp (-x^2) * (1+|x|)^k ≤
      Real.exp (k^2/2) * Real.exp (-(1/2:ℝ)*x^2) := by
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+|x|)
  have hm := mul_le_mul_of_nonneg_right hl hk
  have hs := sq_nonneg (|x|-k)
  nlinarith [sq_abs x]

theorem comparisonHeightEnvelope_convolution (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => comparisonHeightEnvelope (A + 2) t p.1 p.2) ∧
      (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A + 2) t p.1 p.2) ≤
        C * (1 + |t|) ^ (-(A + 2)) := by
  let k := A+2
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hw : Integrable (fun x : ℝ => (1+|x|)^(-k)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := k) (by simp [k]; linarith))
  have hg : Integrable (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  let G := ∫ x : ℝ, Real.exp (-(1/2:ℝ)*x^2)
  let W := ∫ x : ℝ, (1+|x|)^(-k)
  have hG : 0 ≤ G := integral_nonneg (fun _ => Real.exp_nonneg _)
  have hW : 0 ≤ W := integral_nonneg (fun _ => by positivity)
  refine ⟨Real.exp (k^2/2) * G * W + 1, by positivity, ?_⟩
  intro t
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (Real.exp (k^2/2) * (1+|t|)^(-k)) *
        (Real.exp (-(1/2:ℝ)*(t+p.2)^2) * (1+|p.1|)^(-k))) := by
    have h := hw.mul_prod (hg.comp_add_left t)
    simpa only [Measure.volume_eq_prod, mul_comm] using h.const_mul (Real.exp (k^2/2) * (1+|t|)^(-k))
  have hbound : ∀ p : ℝ × ℝ, comparisonHeightEnvelope k t p.1 p.2 ≤
      (Real.exp (k^2/2) * (1+|t|)^(-k)) *
        (Real.exp (-(1/2:ℝ)*(t+p.2)^2) * (1+|p.1|)^(-k)) := by
    intro p
    have h := mul_le_mul_of_nonneg_left (weight_shift k t p.2 hk)
      (Real.exp_nonneg (-(t+p.2)^2))
    have h' := mul_le_mul_of_nonneg_right (gauss_poly k (t+p.2) hk)
      (by positivity : 0 ≤ (1+|t|)^(-k))
    have hh : Real.exp (-(t+p.2)^2)*(1+|p.2|)^(-k) ≤
        (Real.exp (k^2/2)*Real.exp (-(1/2:ℝ)*(t+p.2)^2)) * (1+|t|)^(-k) := by
      nlinarith [h,h']
    have hfinal := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (1+|p.1|)^(-k))
    simpa only [comparisonHeightEnvelope, mul_assoc, mul_left_comm, mul_comm] using hfinal
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => comparisonHeightEnvelope k t p.1 p.2) volume := by
    apply Measurable.aestronglyMeasurable
    unfold comparisonHeightEnvelope
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => comparisonHeightEnvelope k t p.1 p.2) :=
    hmajor.mono' hm (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (by unfold comparisonHeightEnvelope; positivity)]
      exact hbound p))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ p : ℝ × ℝ, (Real.exp (k^2/2) * (1+|t|)^(-k)) *
        (Real.exp (-(1/2:ℝ)*(t+p.2)^2) * (1+|p.1|)^(-k)) :=
      integral_mono hi hmajor hbound
    _ = Real.exp (k^2/2) * G * W * (1+|t|)^(-k) := by
      rw [integral_const_mul]
      simp_rw [mul_comm (Real.exp (-(1/2:ℝ)*(t+_ )^2)) ((1+|(_ : ℝ)|)^(-k))]
      rw [Measure.volume_eq_prod, integral_prod_mul
        (fun x : ℝ => (1+|x|)^(-k)) (fun x : ℝ => Real.exp (-(1/2:ℝ)*(t+x)^2)),
        integral_add_left_eq_self (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) t]
      dsimp [G,W]
      ring
    _ ≤ (Real.exp (k^2/2)*G*W+1)*(1+|t|)^(-(A+2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem comparisonHeightEnvelope_integrable (A : ℝ) (hA : 0 ≤ A) :
    Integrable (fun p : ℝ × ℝ × ℝ =>
      comparisonHeightEnvelope (A + 2) p.1 p.2.1 p.2.2) := by
  obtain ⟨C, hC, h⟩ := comparisonHeightEnvelope_convolution A hA
  have hi : Integrable (fun t : ℝ => (1 + |t|) ^ (-(A+2))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := A+2) (by simp; linarith))
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ =>
      comparisonHeightEnvelope (A+2) p.1 p.2.1 p.2.2) volume := by
    unfold comparisonHeightEnvelope
    apply Continuous.aestronglyMeasurable
    have hν : Continuous (fun p : ℝ × ℝ × ℝ => (1 + |p.2.2|) ^ (-(A+2))) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => 1 + |p.2.2|)).rpow_const
        (fun p => Or.inl (by positivity))
    have hτ : Continuous (fun p : ℝ × ℝ × ℝ => (1 + |p.2.1|) ^ (-(A+2))) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => 1 + |p.2.1|)).rpow_const
        (fun p => Or.inl (by positivity))
    exact ((by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => Real.exp (-(p.1 + p.2.2)^2))).mul hν).mul hτ
  have hn : ∀ p : ℝ × ℝ × ℝ, 0 ≤ comparisonHeightEnvelope (A+2) p.1 p.2.1 p.2.2 := by
    intro p; unfold comparisonHeightEnvelope; positivity
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => (h t).1)
  · apply (hi.const_mul C).mono'
    · exact hm.norm.integral_prod_right'
    · filter_upwards [] with t
      have heq : (fun p : ℝ × ℝ => ‖comparisonHeightEnvelope (A+2) t p.1 p.2‖) =
          (fun p : ℝ × ℝ => comparisonHeightEnvelope (A+2) t p.1 p.2) := by
        funext p; exact Real.norm_of_nonneg (hn (t,p))
      rw [heq, Real.norm_of_nonneg (integral_nonneg (fun p => hn (t,p)))]
      exact (h t).2

theorem comparisonHeightEnvelope_convolution_xiHeight (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => comparisonHeightEnvelope (A + E + 2) t p.1 p.2) ∧
      (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A + E + 2) t p.1 p.2) * (2 + |t|) ^ E ≤
        C * (1 + |t|) ^ (-A) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := comparisonHeightEnvelope_convolution (A + E) (by linarith)
  refine ⟨C₀ * 2 ^ E, by positivity, ?_⟩
  intro t
  obtain ⟨hint, hb⟩ := hC₀ t
  refine ⟨hint, ?_⟩
  have ht2 : 0 ≤ (2 + |t|) ^ E := Real.rpow_nonneg (by positivity) _
  have hb2 : (2 + |t|) ^ E ≤ 2 ^ E * (1 + |t|) ^ E := by
    have hbase : 2 + |t| ≤ 2 * (1 + |t|) := by
      have := abs_nonneg t; nlinarith
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 + |t|) hbase hE
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 + |t|)] at h
  calc (∫ p : ℝ × ℝ, comparisonHeightEnvelope (A + E + 2) t p.1 p.2) * (2 + |t|) ^ E
      ≤ (C₀ * (1 + |t|) ^ (-(A + E + 2))) * (2 + |t|) ^ E :=
        mul_le_mul_of_nonneg_right hb ht2
    _ ≤ (C₀ * (1 + |t|) ^ (-(A + E + 2))) * (2 ^ E * (1 + |t|) ^ E) :=
        mul_le_mul_of_nonneg_left hb2
          (mul_nonneg hC₀pos.le (Real.rpow_nonneg (by positivity) _))
    _ = C₀ * 2 ^ E * (1 + |t|) ^ (-(A + 2)) := by
        have he : -(A + E + 2) + E = -(A + 2) := by ring
        have hr : (1 + |t|) ^ (-(A + E + 2)) * (1 + |t|) ^ E = (1 + |t|) ^ (-(A + 2)) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |t|), he]
        calc C₀ * (1 + |t|) ^ (-(A + E + 2)) * (2 ^ E * (1 + |t|) ^ E)
            = (C₀ * 2 ^ E) * ((1 + |t|) ^ (-(A + E + 2)) * (1 + |t|) ^ E) := by ring
          _ = C₀ * 2 ^ E * (1 + |t|) ^ (-(A + 2)) := by rw [hr]
    _ ≤ C₀ * 2 ^ E * (1 + |t|) ^ (-A) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by have := abs_nonneg t; linarith) (by linarith))
          (by positivity)

end
end DedekindZetaZeroFree
