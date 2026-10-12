module

public import DedekindZetaZeroFree.Moments.Comparison.FarDyadSummability

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section

open Complex

lemma comparisonRealPower_norm (Z : ℝ) (hZ : 0 < Z) (s : ℂ) :
    ‖comparisonRealPower Z s‖ = Z ^ s.re := by
  rw [comparisonRealPower, Complex.norm_exp, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.ofReal_re, Real.rpow_def_of_pos hZ, mul_comm]

set_option maxHeartbeats 800000

namespace OrdinaryDyadProof
open MeasureTheory Complex Set

structure Input {ι : Type*} (principal : ι) (q : ι → ℝ) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ) where
  Ω : Set (ℂ × ℂ × ℂ)
  open_Ω : IsOpen Ω
  box : ∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
    w ∈ comparisonClosedStrip (3/1000) 4 → z ∈ comparisonClosedStrip (2/5) 2 →
    (ξ,w,z) ∈ Ω
  holE : ∀ u, u ≠ principal →
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω
  holM : DifferentiableOn ℂ M {z : ℂ | 2/5-1/100000 < z.re}
  holW : DifferentiableOn ℂ W {w : ℂ | 3/1000-1/100000 < w.re}
  decayM : comparisonRapidStripDecay M (2/5) 2
  decayW : comparisonRapidStripDecay W (3/1000) 4
  d : ℝ
  nonneg_d : 0 ≤ d
  boundE : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧ ∀ u, u ≠ principal →
    1 ≤ q u → ∀ ξ w z : ℂ,
    ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
    w ∈ comparisonClosedStrip (3/1000) 4 → z ∈ comparisonClosedStrip (2/5) 2 →
    ‖E u ξ w z‖ ≤ A * (q u)^(1/2+δ) * (2+|w.im|)^d

namespace Input

variable {ι : Type*} {principal : ι} {q : ι → ℝ} {M W : ℂ → ℂ}
  {E : ι → ℂ → ℂ → ℂ → ℂ} (h : Input principal q M W E)
include h

def domain : Set (ℂ × ℂ × ℂ) :=
  h.Ω ∩ {p | 2/5-1/100000 < p.2.2.re} ∩ {p | 3/1000-1/100000 < p.2.1.re}

lemma open_domain : IsOpen h.domain := by
  apply IsOpen.inter
  · exact h.open_Ω.inter (isOpen_lt continuous_const (by fun_prop))
  · exact isOpen_lt continuous_const (by fun_prop)

lemma box_domain (ξ w z : ℂ)
    (hξ : ξ ∈ comparisonClosedStrip comparisonSigma₁ 4)
    (hw : w ∈ comparisonClosedStrip (3/1000) 4)
    (hz : z ∈ comparisonClosedStrip (2/5) 2) : (ξ,w,z) ∈ h.domain := by
  refine ⟨⟨h.box ξ w z hξ hw hz, ?_⟩, ?_⟩
  · dsimp; have := hz.1; linarith
  · dsimp; have := hw.1; linarith

lemma hol_kernel (Z : ℝ) (u : ι) (hu : u ≠ principal) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ =>
      comparisonFrequencyKernel q M W E Z u p.1 p.2.1 p.2.2) h.domain := by
  have hM : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => M p.2.2) h.domain :=
    h.holM.comp (by fun_prop) (fun p hp => hp.1.2)
  have hW : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => W p.2.1) h.domain :=
    h.holW.comp (by fun_prop) (fun p hp => hp.2)
  have hE := (h.holE u hu).mono (show h.domain ⊆ h.Ω from fun p hp => hp.1.1)
  have hx : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => Complex.exp
      (((comparisonA : ℂ)/2+p.1-1+(comparisonH₀ : ℂ)*p.2.2+
        (comparisonB : ℂ)*(p.2.1-1))*(Real.log Z : ℂ))) :=
    Complex.differentiable_exp.comp (by fun_prop)
  have hg : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => Complex.exp ((p.1+p.2.2-1)^2)) :=
    Complex.differentiable_exp.comp (by fun_prop)
  have hq : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => Complex.exp (-p.2.2*(Real.log (q u) : ℂ))) :=
    Complex.differentiable_exp.comp (by fun_prop)
  exact ((((hx.differentiableOn.mul hg.differentiableOn).mul hM).mul hW).mul
    hq.differentiableOn).mul hE

omit h in
lemma power_re (ξ w z : ℂ) :
    ((comparisonA : ℂ)/2 + ξ - 1 + (comparisonH₀ : ℂ)*z +
      (comparisonB : ℂ)*(w-1)).re = comparisonE ξ.re w.re z.re := by
  simp [comparisonE, Complex.div_re, Complex.mul_re]

lemma box_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z u ξ w z, 1 ≤ Z → u ≠ principal → 1 ≤ q u →
    ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
    w ∈ comparisonClosedStrip (3/1000) 4 → z ∈ comparisonClosedStrip (2/5) 2 →
    ‖comparisonFrequencyKernel q M W E Z u ξ w z‖ ≤
      K * Z ^ comparisonE ξ.re w.re z.re * (q u)^(-z.re+1/2+δ) *
        comparisonHeightEnvelope 2 ξ.im w.im z.im := by
  obtain ⟨G, hG, hg⟩ := comparisonGaussianMellinWeight_polynomial_bound M W
    comparisonSigma₁ 4 (3/1000) 4 (2/5) 2 2 h.d 0
    (by norm_num [comparisonSigma₁, comparisonDelta]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h.nonneg_d (by norm_num) h.decayM h.decayW
  obtain ⟨A, hA, ha⟩ := h.boundE δ hδ
  refine ⟨G*A, by positivity, ?_⟩
  intro Z u ξ w z hZ hu hq hξ hw hz
  have hZp : 0 < Z := by linarith
  have hqp : 0 < q u := by linarith
  have hg' : ‖comparisonGaussianMellinWeight M W ξ w z‖ * (2+|w.im|)^h.d ≤
      G * comparisonHeightEnvelope 2 ξ.im w.im z.im := by
    simpa using hg ξ w z hξ hw hz
  have hb := mul_le_mul_of_nonneg_left (ha u hu hq ξ w z hξ hw hz)
    (norm_nonneg (comparisonGaussianMellinWeight M W ξ w z))
  have hb' : ‖comparisonGaussianMellinWeight M W ξ w z‖ * ‖E u ξ w z‖ ≤
      (A * (q u)^(1/2+δ)) * (G * comparisonHeightEnvelope 2 ξ.im w.im z.im) := by
    calc
      _ ≤ (A * (q u)^(1/2+δ)) *
          (‖comparisonGaussianMellinWeight M W ξ w z‖ * (2+|w.im|)^h.d) := by
        convert hb using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg' (by positivity)
  have heq : comparisonFrequencyKernel q M W E Z u ξ w z =
      comparisonRealPower Z ((comparisonA : ℂ)/2 + ξ - 1 +
        (comparisonH₀ : ℂ)*z + (comparisonB : ℂ)*(w-1)) *
      comparisonRealPower (q u) (-z) * (comparisonGaussianMellinWeight M W ξ w z * E u ξ w z) := by
    unfold comparisonFrequencyKernel comparisonGaussianMellinWeight; ring
  rw [heq, norm_mul, norm_mul, comparisonRealPower_norm Z hZp,
    comparisonRealPower_norm (q u) hqp, power_re, Complex.neg_re, norm_mul]
  calc
    _ ≤ (Z ^ comparisonE ξ.re w.re z.re * (q u)^(-z.re)) *
        ((A * (q u)^(1/2+δ)) * (G * comparisonHeightEnvelope 2 ξ.im w.im z.im)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by
      rw [show -z.re+1/2+δ = -z.re+(1/2+δ) by ring, Real.rpow_add hqp (-z.re) (1/2+δ)]
      ring

lemma uniform_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z u ξ w z, 1 ≤ Z → u ≠ principal → 1 ≤ q u →
    ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
    w ∈ comparisonClosedStrip (3/1000) 4 → z ∈ comparisonClosedStrip (2/5) 2 →
    ‖comparisonFrequencyKernel q M W E Z u ξ w z‖ ≤
      K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+δ) *
        comparisonHeightEnvelope 2 ξ.im w.im z.im := by
  obtain ⟨K,hK,hk⟩ := h.box_bound δ hδ
  refine ⟨K,hK,?_⟩
  intro Z u ξ w z hZ hu hq hξ hw hz
  apply (hk Z u ξ w z hZ hu hq hξ hw hz).trans
  have h1 : Z ^ comparisonE ξ.re w.re z.re ≤ Z ^ comparisonE 4 4 2 :=
    Real.rpow_le_rpow_of_exponent_le hZ (by
      dsimp [comparisonE, comparisonH₀, comparisonB]; linarith [hξ.2,hw.2,hz.2])
  have h2 : (q u)^(-z.re+1/2+δ) ≤ (q u)^(1/10+δ) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith [hz.1])
  unfold comparisonHeightEnvelope
  gcongr

omit h in
lemma line_mem (σ t a b : ℝ) (hσ : σ ∈ Icc a b) :
    (σ : ℂ)+(t : ℂ)*I ∈ comparisonClosedStrip a b := by
  simpa [comparisonClosedStrip] using hσ

lemma line_integrable (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal)
    (hq : 1 ≤ q u) (a b c : ℝ) (ha : a ∈ Icc comparisonSigma₁ 4)
    (hb : b ∈ Icc (3/1000) 4) (hc : c ∈ Icc (2/5) 2) :
    Integrable (fun p : ℝ × ℝ × ℝ => comparisonFrequencyKernel q M W E Z u
      ((a:ℂ)+p.1*I) ((b:ℂ)+p.2.1*I) ((c:ℂ)+p.2.2*I)) := by
  have hcont : Continuous (fun p : ℝ × ℝ × ℝ => comparisonFrequencyKernel q M W E Z u
      ((a:ℂ)+p.1*I) ((b:ℂ)+p.2.1*I) ((c:ℂ)+p.2.2*I)) :=
    (h.hol_kernel Z u hu).continuousOn.comp_continuous
      (f := fun p : ℝ × ℝ × ℝ => (((a:ℂ)+p.1*I), ((b:ℂ)+p.2.1*I), ((c:ℂ)+p.2.2*I)))
      (by fun_prop) (fun p =>
      h.box_domain _ _ _ (line_mem a p.1 _ _ ha) (line_mem b p.2.1 _ _ hb)
        (line_mem c p.2.2 _ _ hc))
  obtain ⟨K,hK,hk⟩ := h.uniform_bound 1 (by norm_num)
  have henv : Integrable (fun p : ℝ × ℝ × ℝ => comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2) :=
    by simpa using comparisonHeightEnvelope_integrable 0 (by norm_num)
  apply (henv.const_mul (K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+(1:ℝ)))).mono'
    hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa using hk Z u _ _ _ hZ hu hq (line_mem a p.1 _ _ ha)
      (line_mem b p.2.1 _ _ hb) (line_mem c p.2.2 _ _ hc))

lemma shift_slice (Z : ℝ) (u : ι) (hu : u ≠ principal)
    (g : ℂ → ℂ × ℂ × ℂ) (hg : Differentiable ℂ g)
    (a b D : ℝ) (hab : a < b) (hD : 0 ≤ D)
    (hmem : ∀ s ∈ comparisonClosedStrip a b, g s ∈ h.domain)
    (hbound : ∀ s ∈ comparisonClosedStrip a b,
      ‖comparisonFrequencyKernel q M W E Z u (g s).1 (g s).2.1 (g s).2.2‖ ≤
        D * (1+|s.im|)^(-2:ℝ)) :
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u
      (g ((a:ℂ)+t*I)).1 (g ((a:ℂ)+t*I)).2.1 (g ((a:ℂ)+t*I)).2.2) =
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u
      (g ((b:ℂ)+t*I)).1 (g ((b:ℂ)+t*I)).2.1 (g ((b:ℂ)+t*I)).2.2) := by
  apply verticalIntegral_eq_of_strip_decay a b D
    (fun s => comparisonFrequencyKernel q M W E Z u (g s).1 (g s).2.1 (g s).2.2) (g ⁻¹' h.domain) hab hD
    (h.open_domain.preimage hg.continuous) hmem
  · exact (h.hol_kernel Z u hu).comp hg.differentiableOn (fun _ hs => hs)
  · exact hbound

omit h in
lemma gauss_shift (t v : ℝ) : Real.exp (-(t+v)^2) ≤
    (Real.exp 2 * (1+|v|)^2) * (1+|t|)^(-2:ℝ) := by
  have hp : 1+|t| ≤ (1+|t+v|)*(1+|v|) := by
    have ht : |t| ≤ |t+v|+|v| := by simpa using abs_sub (t+v) v
    nlinarith [abs_nonneg (t+v), abs_nonneg v]
  have hg : Real.exp (-(t+v)^2) * (1+|t+v|)^2 ≤ Real.exp 2 := by
    rw [← Real.rpow_two (1+|t+v|), Real.rpow_def_of_pos (by positivity : 0 < 1+|t+v|), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+|t+v|)
    nlinarith [sq_abs (t+v), sq_nonneg (|t+v|-1)]
  have hh : Real.exp (-(t+v)^2) * (1+|t|)^2 ≤ Real.exp 2*(1+|v|)^2 := by
    calc
      _ ≤ Real.exp (-(t+v)^2) * ((1+|t+v|)*(1+|v|))^2 := by gcongr
      _ = (Real.exp (-(t+v)^2)*(1+|t+v|)^2)*(1+|v|)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (by positivity)
  rw [Real.rpow_neg (by positivity : 0 ≤ 1+|t|), Real.rpow_two]
  exact (le_mul_inv_iff₀ (by positivity : 0 < (1+|t|)^2)).mpr hh

omit h in
lemma envelope_xi (t w z : ℝ) : comparisonHeightEnvelope 2 t w z ≤
    (Real.exp 2 * (1+|z|)^2) * (1+|t|)^(-2:ℝ) := by
  have h1 : (1+|z|)^(-2:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z]) (by norm_num)
  have h2 : (1+|w|)^(-2:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg w]) (by norm_num)
  unfold comparisonHeightEnvelope
  calc
    _ ≤ Real.exp (-(t+z)^2)*1*1 := by gcongr
    _ ≤ _ := by simpa using gauss_shift t z

omit h in
lemma envelope_w (t w z : ℝ) : comparisonHeightEnvelope 2 t w z ≤ (1+|w|)^(-2:ℝ) := by
  have h1 : (1+|z|)^(-2:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z]) (by norm_num)
  have h2 : Real.exp (-(t+z)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t+z)])
  unfold comparisonHeightEnvelope
  calc
    _ ≤ 1*1*(1+|w|)^(-2:ℝ) := by gcongr
    _ = _ := by ring

omit h in
lemma envelope_z (t w z : ℝ) : comparisonHeightEnvelope 2 t w z ≤ (1+|z|)^(-2:ℝ) := by
  have h1 : (1+|w|)^(-2:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg w]) (by norm_num)
  have h2 : Real.exp (-(t+z)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (t+z)])
  unfold comparisonHeightEnvelope
  calc
    _ ≤ 1*(1+|z|)^(-2:ℝ)*1 := by gcongr
    _ = _ := by ring

lemma xi_shift (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u)
    (w z : ℂ) (hw : w ∈ comparisonClosedStrip (3/1000) 4)
    (hz : z ∈ comparisonClosedStrip (2/5) 2) :
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ((comparisonSigma₁:ℂ)+t*I) w z) =
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ((4:ℂ)+t*I) w z) := by
  obtain ⟨K,hK,hk⟩ := h.uniform_bound 1 (by norm_num)
  apply h.shift_slice Z u hu (fun s => (s,w,z)) (by fun_prop)
    comparisonSigma₁ 4 (K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+(1:ℝ)) *
      (Real.exp 2*(1+|z.im|)^2)) (by norm_num [comparisonSigma₁, comparisonDelta]) (by positivity)
    (fun s hs => h.box_domain s w z hs hw hz)
  intro s hs
  apply (hk Z u s w z hZ hu hq hs hw hz).trans
  have hh := mul_le_mul_of_nonneg_left (envelope_xi s.im w.im z.im)
    (show 0 ≤ K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+(1:ℝ)) by positivity)
  simpa only [mul_assoc] using hh

lemma z_shift (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u)
    (ξ w : ℂ) (hξ : ξ ∈ comparisonClosedStrip comparisonSigma₁ 4)
    (hw : w ∈ comparisonClosedStrip (3/1000) 4) :
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ξ w (((2/5:ℝ):ℂ)+t*I)) =
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ξ w ((2:ℂ)+t*I)) := by
  obtain ⟨K,hK,hk⟩ := h.uniform_bound 1 (by norm_num)
  apply h.shift_slice Z u hu (fun s => (ξ,w,s)) (by fun_prop)
    (2/5) 2 (K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+(1:ℝ))) (by norm_num) (by positivity)
    (fun s hs => h.box_domain ξ w s hξ hw hs)
  intro s hs
  exact (hk Z u ξ w s hZ hu hq hξ hw hs).trans
    (mul_le_mul_of_nonneg_left (envelope_z ξ.im w.im s.im) (by positivity))

lemma w_shift (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u)
    (ξ z : ℂ) (hξ : ξ ∈ comparisonClosedStrip comparisonSigma₁ 4)
    (hz : z ∈ comparisonClosedStrip (2/5) 2) :
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ξ (((3/1000:ℝ):ℂ)+t*I) z) =
    (∫ t : ℝ, comparisonFrequencyKernel q M W E Z u ξ ((4:ℂ)+t*I) z) := by
  obtain ⟨K,hK,hk⟩ := h.uniform_bound 1 (by norm_num)
  apply h.shift_slice Z u hu (fun s => (ξ,s,z)) (by fun_prop)
    (3/1000) 4 (K * Z ^ comparisonE 4 4 2 * (q u)^(1/10+(1:ℝ))) (by norm_num) (by positivity)
    (fun s hs => h.box_domain ξ s z hξ hs hz)
  intro s hs
  exact (hk Z u ξ s z hZ hu hq hξ hs hz).trans
    (mul_le_mul_of_nonneg_left (envelope_w ξ.im s.im z.im) (by positivity))

lemma triple_shift (Z : ℝ) (hZ : 1 ≤ Z) (u : ι) (hu : u ≠ principal) (hq : 1 ≤ q u) :
    comparisonTripleVerticalIntegral 4 4 2 (comparisonFrequencyKernel q M W E Z u) =
    comparisonTripleVerticalIntegral comparisonSigma₁ (3/1000) (2/5)
      (comparisonFrequencyKernel q M W E Z u) := by
  let f := fun (a b c : ℝ) (p : ℝ × ℝ × ℝ) => comparisonFrequencyKernel q M W E Z u
    ((a:ℂ)+p.1*I) ((b:ℂ)+p.2.1*I) ((c:ℂ)+p.2.2*I)
  have hi := h.line_integrable Z hZ u hu hq
  have h4 : (4:ℝ) ∈ Icc comparisonSigma₁ 4 := by norm_num [comparisonSigma₁,comparisonDelta]
  have hs : comparisonSigma₁ ∈ Icc comparisonSigma₁ 4 := by norm_num [comparisonSigma₁,comparisonDelta]
  have h4w : (4:ℝ) ∈ Icc (3/1000) 4 := by norm_num
  have hsw : (3/1000:ℝ) ∈ Icc (3/1000) 4 := by norm_num
  have h2 : (2:ℝ) ∈ Icc (2/5) 2 := by norm_num
  have hsz : (2/5:ℝ) ∈ Icc (2/5) 2 := by norm_num
  have hi₀ : Integrable (f 4 4 2) := hi 4 4 2 h4 h4w h2
  have hi₁ : Integrable (f comparisonSigma₁ 4 2) := hi comparisonSigma₁ 4 2 hs h4w h2
  have hi₂ : Integrable (f comparisonSigma₁ 4 (2/5)) := hi comparisonSigma₁ 4 (2/5) hs h4w hsz
  have hi₃ : Integrable (f comparisonSigma₁ (3/1000) (2/5)) := hi comparisonSigma₁ (3/1000) (2/5) hs hsw hsz
  unfold comparisonTripleVerticalIntegral
  congr 1
  change (∫ p, f 4 4 2 p) = ∫ p, f comparisonSigma₁ (3/1000) (2/5) p
  calc
    _ = ∫ p, f comparisonSigma₁ 4 2 p := by
      rw [Measure.volume_eq_prod] at hi₀ hi₁ ⊢
      rw [integral_prod_symm _ hi₀, integral_prod_symm _ hi₁]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => (h.xi_shift Z hZ u hu hq _ _
        (line_mem 4 p.1 _ _ h4w) (line_mem 2 p.2 _ _ h2)).symm)
    _ = ∫ p, f comparisonSigma₁ 4 (2/5) p := by
      rw [Measure.volume_eq_prod] at hi₁ hi₂ ⊢
      rw [integral_prod _ hi₁, integral_prod _ hi₂]
      apply integral_congr_ae
      filter_upwards [hi₁.prod_right_ae, hi₂.prod_right_ae] with t ht₁ ht₂
      rw [Measure.volume_eq_prod] at ht₁ ht₂ ⊢
      rw [integral_prod _ ht₁, integral_prod _ ht₂]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun tw => (h.z_shift Z hZ u hu hq _ _
        (line_mem comparisonSigma₁ t _ _ hs) (line_mem 4 tw _ _ h4w)).symm)
    _ = _ := by
      rw [Measure.volume_eq_prod] at hi₂ hi₃ ⊢
      rw [integral_prod _ hi₂, integral_prod _ hi₃]
      apply integral_congr_ae
      filter_upwards [hi₂.prod_right_ae, hi₃.prod_right_ae] with t ht₂ ht₃
      rw [Measure.volume_eq_prod] at ht₂ ht₃ ⊢
      rw [integral_prod_symm _ ht₂, integral_prod_symm _ ht₃]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun tz => (h.w_shift Z hZ u hu hq _ _
        (line_mem comparisonSigma₁ t _ _ hs) (line_mem (2/5) tz _ _ hsz)).symm)

lemma finite_shift (Z : ℝ) (hZ : 1 ≤ Z) (C : Finset ι)
    (hC : ∀ u ∈ C, u ≠ principal ∧ 1 ≤ q u) :
    comparisonFrequencyIntegral q M W E C Z 4 4 2 =
    comparisonFrequencyIntegral q M W E C Z comparisonSigma₁ (3/1000) (2/5) := by
  classical
  unfold comparisonFrequencyIntegral comparisonTripleVerticalIntegral
  rw [integral_finset_sum, integral_finset_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    have hh := h.triple_shift Z hZ u (hC u hu).1 (hC u hu).2
    unfold comparisonTripleVerticalIntegral at hh
    exact mul_left_cancel₀ (by simp [Real.pi_ne_zero]) hh
  · intro u hu
    exact h.line_integrable Z hZ u (hC u hu).1 (hC u hu).2 _ _ _
      (by norm_num [comparisonSigma₁,comparisonDelta]) (by norm_num) (by norm_num)
  · intro u hu
    exact h.line_integrable Z hZ u (hC u hu).1 (hC u hu).2 _ _ _
      (by norm_num [comparisonSigma₁,comparisonDelta]) (by norm_num) (by norm_num)

lemma dyad_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z U u (p : ℝ × ℝ × ℝ),
      1 ≤ Z → 1 ≤ U → u ≠ principal → U ≤ q u → q u < 2*U →
      ‖comparisonFrequencyKernel q M W E Z u
        ((comparisonSigma₁:ℂ)+p.1*I) (((3/1000:ℝ):ℂ)+p.2.1*I)
        (((2/5:ℝ):ℂ)+p.2.2*I)‖ ≤
      K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε) *
        comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 := by
  obtain ⟨K,hK,hk⟩ := h.box_bound ε hε
  refine ⟨K * (2:ℝ)^(1/10+ε), by positivity, ?_⟩
  intro Z U u p hZ hU hu hqu hqu2
  have hq := hU.trans hqu
  have hUp : 0 < U := by linarith
  have hb := hk Z u ((comparisonSigma₁:ℂ)+p.1*I) (((3/1000:ℝ):ℂ)+p.2.1*I)
    (((2/5:ℝ):ℂ)+p.2.2*I) hZ hu hq
    (line_mem comparisonSigma₁ p.1 _ _ (by norm_num [comparisonSigma₁,comparisonDelta]))
    (line_mem (3/1000) p.2.1 _ _ (by norm_num))
    (line_mem (2/5) p.2.2 _ _ (by norm_num))
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, sub_zero, zero_add, add_zero, neg_zero] at hb
  have hex : -(2/5:ℝ)+1/2+ε = 1/10+ε := by ring
  rw [hex] at hb
  have hpow : (q u)^(1/10+ε) ≤ (2:ℝ)^(1/10+ε)*U^(1/10+ε) := by
    rw [← Real.mul_rpow (by norm_num) hUp.le]
    exact Real.rpow_le_rpow (by linarith) hqu2.le (by linarith)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) *
      comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2 by unfold comparisonHeightEnvelope; positivity)
  convert hh using 1 <;> ring

lemma estimate (α B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ Z U : ℝ, 1 ≤ Z → 1 ≤ U → ∀ C : Finset ι,
      (∀ u ∈ C, u ≠ principal ∧ U ≤ q u ∧ q u < 2*U) →
      (C.card : ℝ) ≤ B * U^α →
      comparisonFrequencyIntegral q M W E C Z 4 4 2 =
        comparisonFrequencyIntegral q M W E C Z comparisonSigma₁ (3/1000) (2/5) ∧
      ‖comparisonFrequencyIntegral q M W E C Z 4 4 2‖ ≤
        A * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(α+1/2-2/5+ε) := by
  obtain ⟨K,hK,hk⟩ := h.dyad_bound ε hε
  let H := fun p : ℝ × ℝ × ℝ => comparisonHeightEnvelope 2 p.1 p.2.1 p.2.2
  have hH : Integrable H := by simpa [H] using comparisonHeightEnvelope_integrable 0 (by norm_num)
  let L : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹ ^ 3‖
  let T : ℝ := 1 + |∫ p : ℝ × ℝ × ℝ, H p|
  have hL : 0 < L := by
    dsimp [L]
    apply norm_pos_iff.mpr
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨L * K * B * T, by positivity, ?_⟩
  intro Z U hZ hU C hC hcard
  have hqu : ∀ u ∈ C, u ≠ principal ∧ 1 ≤ q u := by
    intro u hu
    exact ⟨(hC u hu).1, hU.trans (hC u hu).2.1⟩
  have heq := h.finite_shift Z hZ C hqu
  refine ⟨heq, ?_⟩
  rw [heq]
  classical
  have hsum (p : ℝ × ℝ × ℝ) :
      ‖∑ u ∈ C, comparisonFrequencyKernel q M W E Z u
        ((comparisonSigma₁:ℂ)+p.1*I) (((3/1000:ℝ):ℂ)+p.2.1*I)
        (((2/5:ℝ):ℂ)+p.2.2*I)‖ ≤
      (C.card:ℝ) * (K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε) * H p) := by
    calc
      _ ≤ ∑ u ∈ C, ‖comparisonFrequencyKernel q M W E Z u
        ((comparisonSigma₁:ℂ)+p.1*I) (((3/1000:ℝ):ℂ)+p.2.1*I)
        (((2/5:ℝ):ℂ)+p.2.2*I)‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ C, K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε) * H p :=
        Finset.sum_le_sum (fun u hu => hk Z U u p hZ hU (hC u hu).1 (hC u hu).2.1 (hC u hu).2.2)
      _ = _ := by simp
  have hmaj := norm_integral_le_of_norm_le
    (hH.const_mul ((C.card:ℝ) * (K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε))))
    (Filter.Eventually.of_forall (fun p => by simpa only [mul_assoc] using hsum p))
  rw [integral_const_mul] at hmaj
  have hi : (∫ p, H p) ≤ T := by dsimp [T]; linarith [le_abs_self (∫ p, H p)]
  unfold comparisonFrequencyIntegral comparisonTripleVerticalIntegral
  rw [norm_mul]
  change L * ‖∫ p : ℝ × ℝ × ℝ, _‖ ≤ _
  calc
    _ ≤ L * ((C.card:ℝ) * (K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε)) * ∫ p, H p) :=
      mul_le_mul_of_nonneg_left hmaj hL.le
    _ ≤ L * ((C.card:ℝ) * (K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε)) * T) := by gcongr
    _ ≤ L * ((B*U^α) * (K * Z ^ comparisonE comparisonSigma₁ (3/1000) (2/5) * U^(1/10+ε)) * T) := by
      gcongr
    _ = _ := by
      have hUp : 0 < U := by linarith
      rw [show α+1/2-2/5+ε = α+(1/10+ε) by ring, Real.rpow_add hUp α (1/10+ε)]
      ring

end Input
end OrdinaryDyadProof

theorem comparison_ordinary_dyad_analytic
    {ι : Type*} (principal : ι) (q : ι → ℝ) (M W : ℂ → ℂ)
    (E : ι → ℂ → ℂ → ℂ → ℂ)
    (Ω : Set (ℂ × ℂ × ℂ)) (hΩ : IsOpen Ω)
    (hbox : ∀ ξ w z : ℂ,
      ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
      w ∈ comparisonClosedStrip (3 / 1000) 4 →
      z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω)
    (hE : ∀ u : ι, u ≠ principal →
      DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => E u p.1 p.2.1 p.2.2) Ω)
    (hM : DifferentiableOn ℂ M {z : ℂ | 2 / 5 - 1 / 100000 < z.re})
    (hW : DifferentiableOn ℂ W {w : ℂ | 3 / 1000 - 1 / 100000 < w.re})
    (hMdecay : comparisonRapidStripDecay M (2 / 5) 2)
    (hWdecay : comparisonRapidStripDecay W (3 / 1000) 4)
    (hEBound : ∃ d : ℝ, 0 ≤ d ∧ ∀ δ : ℝ, 0 < δ →
      ∃ A : ℝ, 0 < A ∧ ∀ u : ι, u ≠ principal → 1 ≤ q u →
        ∀ ξ w z : ℂ,
          ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
          w ∈ comparisonClosedStrip (3 / 1000) 4 →
          z ∈ comparisonClosedStrip (2 / 5) 2 →
          ‖E u ξ w z‖ ≤ A * (q u) ^ (1 / 2 + δ) * (2 + |w.im|) ^ d)
    (α B ε : ℝ) (hα : 0 ≤ α) (hB : 0 < B) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ Z U : ℝ, 1 ≤ Z → 1 ≤ U →
      ∀ C : Finset ι,
        (∀ u ∈ C, u ≠ principal ∧ U ≤ q u ∧ q u < 2 * U) →
        (C.card : ℝ) ≤ B * U ^ α →
        comparisonFrequencyIntegral q M W E C Z 4 4 2 =
          comparisonFrequencyIntegral q M W E C Z comparisonSigma₁ (3 / 1000) (2 / 5) ∧
        ‖comparisonFrequencyIntegral q M W E C Z 4 4 2‖ ≤
          A * Z ^ (comparisonE comparisonSigma₁ (3 / 1000) (2 / 5)) *
            U ^ (α + 1 / 2 - 2 / 5 + ε) := by
  obtain ⟨d, hd, hb⟩ := hEBound
  let h : OrdinaryDyadProof.Input principal q M W E :=
    ⟨Ω, hΩ, hbox, hE, hM, hW, hMdecay, hWdecay, d, hd, hb⟩
  exact h.estimate α B ε hB hε

end
end DedekindZetaZeroFree
