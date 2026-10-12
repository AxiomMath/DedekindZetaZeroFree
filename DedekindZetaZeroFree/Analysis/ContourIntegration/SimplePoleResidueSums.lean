module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.ExponentialStripGrowth
public import DedekindZetaZeroFree.Analysis.VerticalStripBounds

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/PrincipalMellinResidues.lean.
-/

open scoped NumberField Classical Real
open MeasureTheory Filter

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem integral_div_sq_add_sq (α : ℝ) (hα : α ≠ 0) :
    ∫ t : ℝ, α / (α^2 + t^2) = π * α / |α| := by
  have hpt : (fun t : ℝ => α / (α^2 + t^2))
      = fun t => (1/α) * (1 + ((1/α) * t)^2)⁻¹ := by
    funext t
    field_simp
  rw [hpt, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq]
  simp only [one_div, abs_inv]
  field_simp
  rw [sq_abs]

theorem re_simplePoleKernel (α β t : ℝ) :
    (((1:ℂ)/((α:ℂ) + t*Complex.I) - (1:ℂ)/((β:ℂ) + t*Complex.I))).re
      = α/(α^2+t^2) - β/(β^2+t^2) := by
  simp [one_div, Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re] <;> ring_nf

theorem im_simplePoleKernel (α β t : ℝ) :
    (((1:ℂ)/((α:ℂ) + t*Complex.I) - (1:ℂ)/((β:ℂ) + t*Complex.I))).im
      = t/(β^2+t^2) - t/(α^2+t^2) := by
  simp [one_div, Complex.inv_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im] <;> ring_nf

private lemma min_sq_one_mul_le (δ t : ℝ) : min (δ^2) 1 * (1 + t^2) ≤ δ^2 + t^2 := by
  rcases le_or_gt (δ^2) 1 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h.le]; nlinarith

private lemma integrable_div_sq_add_sq (α : ℝ) (hα : α ≠ 0) :
    Integrable (fun t : ℝ => α / (α^2 + t^2)) := by
  have hb : (1/α) ≠ 0 := by simp [hα]
  refine ((integrable_inv_one_add_mul_sq hb).const_mul (1/α)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.mul_apply, smul_eq_mul]
  field_simp

private lemma poleKernel_eq (c α t : ℝ) :
    (((c:ℂ) + t*Complex.I) - (α:ℂ))⁻¹ = (1:ℂ)/(((c - α : ℝ) : ℂ) + t*Complex.I) := by
  simp only [one_div]
  congr 1
  push_cast
  ring

private lemma integrable_im_poleKernel (δ1 δ2 : ℝ) (h1 : δ1 ≠ 0) (h2 : δ2 ≠ 0) :
    Integrable (fun t : ℝ => t/(δ2^2+t^2) - t/(δ1^2+t^2)) := by
  have hcont : Continuous fun t : ℝ => t/(δ2^2+t^2) - t/(δ1^2+t^2) := by
    refine Continuous.sub ?_ ?_
    · exact continuous_id.div (by fun_prop) fun t => ne_of_gt (by positivity)
    · exact continuous_id.div (by fun_prop) fun t => ne_of_gt (by positivity)
  refine Integrable.mono'
    (g := fun t : ℝ => (|δ1^2 - δ2^2| / (min (δ1^2) 1 * min (δ2^2) 1)) * (1 + t^2)⁻¹)
    (integrable_inv_one_add_sq.const_mul _) hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun t => ?_
  have ht1 : (0:ℝ) < δ1^2 + t^2 := by positivity
  have ht2 : (0:ℝ) < δ2^2 + t^2 := by positivity
  have hD : (0:ℝ) < (δ1^2+t^2)*(δ2^2+t^2) := mul_pos ht1 ht2
  have hid : t/(δ2^2+t^2) - t/(δ1^2+t^2)
      = t*(δ1^2-δ2^2)/((δ1^2+t^2)*(δ2^2+t^2)) := by
    field_simp
    ring
  have hden : min (δ1^2) 1 * min (δ2^2) 1 * (1+t^2)^2 ≤ (δ1^2+t^2)*(δ2^2+t^2) := by
    have := mul_le_mul (min_sq_one_mul_le δ1 t) (min_sq_one_mul_le δ2 t)
      (by positivity) (by positivity)
    nlinarith [this]
  have hstep1 : |t*(δ1^2-δ2^2)| / ((δ1^2+t^2)*(δ2^2+t^2))
      ≤ |t*(δ1^2-δ2^2)| / (min (δ1^2) 1 * min (δ2^2) 1 * (1+t^2)^2) :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden
  have hstep2 : |t*(δ1^2-δ2^2)| / (min (δ1^2) 1 * min (δ2^2) 1 * (1+t^2)^2)
      = (|δ1^2 - δ2^2| / (min (δ1^2) 1 * min (δ2^2) 1)) * (|t|/(1+t^2)) * (1 + t^2)⁻¹ := by
    rw [abs_mul]
    field_simp
  have hratio : |t|/(1+t^2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg t, abs_nonneg t, sq_abs t]
  rw [hid, Real.norm_eq_abs, abs_div, abs_of_pos hD]
  calc |t*(δ1^2-δ2^2)| / ((δ1^2+t^2)*(δ2^2+t^2))
      ≤ |t*(δ1^2-δ2^2)| / (min (δ1^2) 1 * min (δ2^2) 1 * (1+t^2)^2) := hstep1
    _ = (|δ1^2 - δ2^2| / (min (δ1^2) 1 * min (δ2^2) 1)) * (|t|/(1+t^2)) * (1 + t^2)⁻¹ :=
        hstep2
    _ ≤ (|δ1^2 - δ2^2| / (min (δ1^2) 1 * min (δ2^2) 1)) * 1 * (1 + t^2)⁻¹ := by gcongr
    _ = (|δ1^2 - δ2^2| / (min (δ1^2) 1 * min (δ2^2) 1)) * (1 + t^2)⁻¹ := by ring

private lemma integrable_poleKernel (δ1 δ2 : ℝ) (h1 : δ1 ≠ 0) (h2 : δ2 ≠ 0) :
    Integrable (fun t : ℝ =>
        (1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I)) := by
  have hre : (fun t : ℝ => RCLike.re ((1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I)))
      = fun t : ℝ => δ1/(δ1^2+t^2) - δ2/(δ2^2+t^2) :=
    funext fun t => re_simplePoleKernel δ1 δ2 t
  have him : (fun t : ℝ => RCLike.im ((1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I)))
      = fun t : ℝ => t/(δ2^2+t^2) - t/(δ1^2+t^2) :=
    funext fun t => im_simplePoleKernel δ1 δ2 t
  have hreint : Integrable (fun t : ℝ =>
      RCLike.re ((1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I))) := by
    rw [hre]
    exact (integrable_div_sq_add_sq δ1 h1).sub (integrable_div_sq_add_sq δ2 h2)
  have himint : Integrable (fun t : ℝ =>
      RCLike.im ((1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I))) := by
    rw [him]; exact integrable_im_poleKernel δ1 δ2 h1 h2
  rw [← Integrable.re_im_iff]
  exact ⟨hreint, himint⟩

private lemma integral_poleKernel (δ1 δ2 : ℝ) (h1 : δ1 ≠ 0) (h2 : δ2 ≠ 0) :
    ∫ t : ℝ, ((1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I))
      = ((π * (δ1/|δ1| - δ2/|δ2|) : ℝ) : ℂ) := by
  set K : ℝ → ℂ := fun t =>
    (1:ℂ)/((δ1:ℂ) + t*Complex.I) - (1:ℂ)/((δ2:ℂ) + t*Complex.I) with hKdef
  have hK : Integrable K := integrable_poleKernel δ1 δ2 h1 h2
  have hre : (fun t : ℝ => RCLike.re (K t)) = fun t : ℝ => δ1/(δ1^2+t^2) - δ2/(δ2^2+t^2) :=
    funext fun t => re_simplePoleKernel δ1 δ2 t
  have him : (fun t : ℝ => RCLike.im (K t)) = fun t : ℝ => t/(δ2^2+t^2) - t/(δ1^2+t^2) :=
    funext fun t => im_simplePoleKernel δ1 δ2 t
  have hIre : ∫ t : ℝ, RCLike.re (K t) = π * δ1/|δ1| - π * δ2/|δ2| := by
    rw [hre, integral_sub (integrable_div_sq_add_sq δ1 h1) (integrable_div_sq_add_sq δ2 h2),
      integral_div_sq_add_sq δ1 h1, integral_div_sq_add_sq δ2 h2]
  have hIim : ∫ t : ℝ, RCLike.im (K t) = 0 := by
    rw [him]
    set g : ℝ → ℝ := fun t => t/(δ2^2+t^2) - t/(δ1^2+t^2) with hgdef
    have hodd : ∀ t : ℝ, g (-t) = -g t := by intro t; simp only [hgdef]; ring
    have h1 : ∫ t : ℝ, g (-t) = ∫ t : ℝ, g t := integral_neg_eq_self g volume
    rw [funext hodd] at h1
    have h2 : ∫ t : ℝ, -g t = -∫ t : ℝ, g t := integral_neg g
    rw [h2] at h1
    linarith
  rw [← integral_re_add_im hK, hIre, hIim]
  simp
  ring

private lemma verticalIntegral_poleKernel (c α β : ℝ) (hα : c ≠ α) (hβ : c ≠ β) :
    verticalIntegral c (fun s : ℂ => (s - (α:ℂ))⁻¹ - (s - (β:ℂ))⁻¹)
      = ((((c-α)/|c-α| - (c-β)/|c-β|)/2 : ℝ) : ℂ) := by
  rw [verticalIntegral]
  have h1 : (fun t : ℝ => (((c:ℂ) + t*Complex.I) - (α:ℂ))⁻¹ - (((c:ℂ) + t*Complex.I) - (β:ℂ))⁻¹)
      = fun t : ℝ =>
        (1:ℂ)/(((c - α : ℝ) : ℂ) + t*Complex.I) - (1:ℂ)/(((c - β : ℝ) : ℂ) + t*Complex.I) := by
    funext t
    rw [poleKernel_eq c α t, poleKernel_eq c β t]
  rw [h1, integral_poleKernel (c-α) (c-β) (sub_ne_zero.mpr hα) (sub_ne_zero.mpr hβ)]
  push_cast
  field_simp

private theorem verticalIntegral_sum {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℂ → ℂ)
    (hf : ∀ i, Complex.VerticalIntegrable (f i) c) :
    verticalIntegral c (fun s => ∑ i, f i s) = ∑ i, verticalIntegral c (f i) := by
  simp only [verticalIntegral]
  rw [integral_finset_sum Finset.univ (fun i _ => hf i), Finset.mul_sum]

theorem verticalIntegral_sub_eq_sum_residues
    {a b : ℝ} (hab : a < b) (n : ℕ) (p : Fin n → ℝ) (R : Fin n → ℂ)
    (hp_distinct : Function.Injective p) (hp_strip : ∀ j, p j ∈ Set.Ioo a b)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hstrip : {s : ℂ | s.re ∈ Set.Icc a b} ⊆ U)
    (hf_holo : DifferentiableOn ℂ f (U \ Set.range (fun j => (p j : ℂ))))
    (hregular : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, (∀ j, s ≠ (p j : ℂ)) →
        g s = f s - ∑ j : Fin n, R j / (s - (p j : ℂ)))
    (ha : Complex.VerticalIntegrable f a) (hb : Complex.VerticalIntegrable f b)
    (hgrowth : ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + |t|) ^ k) :
    verticalIntegral b f - verticalIntegral a f = ∑ j : Fin n, R j := by
  obtain ⟨g, hg, hreg⟩ := hregular
  obtain ⟨C, k, hC, hbound⟩ := hgrowth
  let Q : ℝ := b + 1
  let φ : ℂ → ℂ := fun s => ∑ j, R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)
  let H : ℂ → ℂ := fun s => g s + ∑ j, R j / (s - (Q : ℂ))
  have hQ : b < Q := by dsimp [Q]; linarith
  have hQne (s : ℂ) (hs : s.re ∈ Set.Icc a b) : s - (Q : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re (sub_eq_zero.mp he)
    simp only [Complex.ofReal_re] at hh
    linarith [hs.2]
  have hHdiff (s : ℂ) (hs : s.re ∈ Set.Icc a b) : DifferentiableAt ℂ H s := by
    apply DifferentiableAt.add (hg.differentiableAt (hU.mem_nhds (hstrip hs)))
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (differentiableAt_const (R j)).div (differentiableAt_id.sub_const _) (hQne s hs)
  have hHeq (s : ℂ) (hs : s.re ∈ Set.Icc a b) (hp : ∀ j, s ≠ (p j : ℂ)) :
      H s = f s - φ s := by
    dsimp [H, φ]
    rw [hreg s (hstrip hs) hp]
    simp_rw [mul_sub, ← div_eq_mul_inv]
    rw [Finset.sum_sub_distrib]
    ring
  have hφint (c : ℝ) (hc : c = a ∨ c = b) : Complex.VerticalIntegrable φ c := by
    have hcp (j : Fin n) : c ≠ p j := by
      rcases hc with rfl | rfl
      · exact ne_of_lt (hp_strip j).1
      · exact ne_of_gt (hp_strip j).2
    have hcQ : c ≠ Q := by rcases hc with rfl | rfl <;> linarith
    apply integrable_finset_sum
    intro j hj
    have hi := (integrable_poleKernel (c-p j) (c-Q)
      (sub_ne_zero.mpr (hcp j)) (sub_ne_zero.mpr hcQ)).const_mul (R j)
    convert hi using 1
    funext t
    simp only [φ, poleKernel_eq]
  have hHline (c : ℝ) (hc : c = a ∨ c = b) :
      (fun t : ℝ => H ((c : ℂ) + t * Complex.I)) =
        fun t : ℝ => f ((c : ℂ) + t * Complex.I) - φ ((c : ℂ) + t * Complex.I) := by
    funext t
    apply hHeq
    · rcases hc with rfl | rfl <;> simp [hab.le]
    · intro j he
      have hh := congrArg Complex.re he
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero] at hh
      rcases hc with rfl | rfl <;> linarith [(hp_strip j).1, (hp_strip j).2]
  have hHa : Complex.VerticalIntegrable H a := by
    change Integrable (fun t : ℝ => H ((a : ℂ) + t * Complex.I))
    rw [hHline a (Or.inl rfl)]
    exact ha.sub (hφint a (Or.inl rfl))
  have hHb : Complex.VerticalIntegrable H b := by
    change Integrable (fun t : ℝ => H ((b : ℂ) + t * Complex.I))
    rw [hHline b (Or.inr rfl)]
    exact hb.sub (hφint b (Or.inr rfl))
  have hHtail : ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
      ‖H ((σ : ℂ) + t * Complex.I)‖ ≤ (C + 2 * ∑ j, ‖R j‖) * (1 + |t|)^k := by
    intro σ t hσ ht
    let s : ℂ := (σ : ℂ) + t * Complex.I
    have hs : s.re ∈ Set.Icc a b := by simpa [s] using hσ
    have htn : t ≠ 0 := by intro he; simp [he] at ht; linarith
    have hpn (j : Fin n) : s ≠ (p j : ℂ) := by
      intro he
      have := congrArg Complex.im he
      simp [s] at this
      exact htn this
    have hinv (r : ℝ) : ‖(s - (r : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      have hh := Complex.abs_im_le_norm (s - (r : ℂ))
      simp only [s, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
        mul_one, mul_zero, add_zero, zero_add, sub_zero] at hh
      exact ht.trans hh
    have hφ : ‖φ s‖ ≤ 2 * ∑ j, ‖R j‖ := by
      dsimp [φ]
      calc ‖∑ j, R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)‖
          ≤ ∑ j, ‖R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖R j‖ * 2 := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact (norm_sub_le _ _).trans (by linarith [hinv (p j), hinv Q])
        _ = 2 * ∑ j, ‖R j‖ := by rw [← Finset.sum_mul]; ring
    have hpw : 1 ≤ (1 + |t|)^k := one_le_pow₀ (by linarith [abs_nonneg t])
    rw [hHeq s hs hpn]
    calc ‖f s - φ s‖ ≤ ‖f s‖ + ‖φ s‖ := norm_sub_le _ _
      _ ≤ C * (1 + |t|)^k + 2 * ∑ j, ‖R j‖ := add_le_add (hbound σ t hσ ht) hφ
      _ ≤ (C + 2 * ∑ j, ‖R j‖) * (1 + |t|)^k := by
        have hsum : 0 ≤ 2 * ∑ j, ‖R j‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpw hsum]
  have hHgrow : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖H ((σ : ℂ) + t * Complex.I)‖ ≤ B * Real.exp (A * |t|) := by
    let J : ℂ → ℂ := fun s => (Real.exp (-|s.im|) : ℂ) * H s
    have hJcont : ContinuousOn J {s : ℂ | s.re ∈ Set.Icc a b} := by
      apply ContinuousOn.mul
      · fun_prop
      · exact fun s hs => (hHdiff s hs).continuousAt.continuousWithinAt
    have hD : 0 ≤ C + 2 * ∑ j, ‖R j‖ := by positivity
    have htail : ∃ B : ℝ, 0 ≤ B ∧ ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖J ((σ : ℂ) + t * Complex.I)‖ ≤ B := by
      refine ⟨(C + 2 * ∑ j, ‖R j‖) * (k.factorial : ℝ) * Real.exp 1, by positivity, ?_⟩
      intro σ t hσ ht
      have hk : (1 + |t|)^k ≤ (k.factorial : ℝ) * Real.exp (1 + |t|) := by
        have hh := Real.pow_div_factorial_le_exp (1 + |t|) (show 0 ≤ 1 + |t| by positivity) k
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k.factorial : ℝ))).mp hh |>.trans_eq (mul_comm _ _)
      have hn : ‖J ((σ : ℂ) + t * Complex.I)‖ =
          Real.exp (-|t|) * ‖H ((σ : ℂ) + t * Complex.I)‖ := by
        simp [J, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      rw [hn]
      calc Real.exp (-|t|) * ‖H ((σ : ℂ) + t * Complex.I)‖
          ≤ Real.exp (-|t|) * ((C + 2 * ∑ j, ‖R j‖) * (1 + |t|)^k) :=
            mul_le_mul_of_nonneg_left (hHtail σ t hσ ht) (Real.exp_pos _).le
        _ ≤ Real.exp (-|t|) * ((C + 2 * ∑ j, ‖R j‖) * ((k.factorial : ℝ) * Real.exp (1 + |t|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hD) (Real.exp_pos _).le
        _ = _ := by
          rw [Real.exp_add, Real.exp_neg]
          field_simp
    obtain ⟨B, hB, hJB⟩ := Subquadratic.strip_bound_of_tail_bound J hJcont htail
    refine ⟨1, B, by norm_num, hB, fun σ hσ t => ?_⟩
    have hh := hJB σ t hσ
    have hn : ‖J ((σ : ℂ) + t * Complex.I)‖ =
        Real.exp (-|t|) * ‖H ((σ : ℂ) + t * Complex.I)‖ := by
      simp [J, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    rw [hn, Real.exp_neg] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos |t|).le
    have he : (Real.exp |t|)⁻¹ * ‖H ((σ : ℂ) + t * Complex.I)‖ * Real.exp |t| =
        ‖H ((σ : ℂ) + t * Complex.I)‖ := by field_simp
    simpa only [one_mul, he] using hh'
  have hshift := integral_eq_of_exponential_strip_growth hab.le H
    (fun s hsa hsb => hHdiff s ⟨hsa, hsb⟩) hHa hHb hHgrow
  have hφval (c : ℝ) (hc : c = a ∨ c = b) :
      verticalIntegral c φ = if c = a then 0 else ∑ j, R j := by
    have hcp (j : Fin n) : c ≠ p j := by
      rcases hc with rfl | rfl
      · exact ne_of_lt (hp_strip j).1
      · exact ne_of_gt (hp_strip j).2
    have hcQ : c ≠ Q := by rcases hc with rfl | rfl <;> linarith
    have hint (j : Fin n) : Complex.VerticalIntegrable
        (fun s => R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)) c := by
      have hi := (integrable_poleKernel (c-p j) (c-Q)
        (sub_ne_zero.mpr (hcp j)) (sub_ne_zero.mpr hcQ)).const_mul (R j)
      change Integrable (fun t : ℝ => R j * ((((c : ℂ) + t * Complex.I) - (p j : ℂ))⁻¹ - (((c : ℂ) + t * Complex.I) - (Q : ℂ))⁻¹))
      convert hi using 1
      funext t
      simp only [poleKernel_eq]
    change verticalIntegral c (fun s => ∑ j, R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)) = _
    rw [verticalIntegral_sum c _ hint]
    have hmul (j : Fin n) : verticalIntegral c
        (fun s => R j * ((s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹)) =
        R j * verticalIntegral c (fun s => (s - (p j : ℂ))⁻¹ - (s - (Q : ℂ))⁻¹) := by
      simp only [verticalIntegral, integral_const_mul]
      ring
    simp_rw [hmul, verticalIntegral_poleKernel c _ Q (hcp _) hcQ]
    rcases hc with hca | hcb
    · subst c
      have haQ : a - Q < 0 := by linarith
      have hs (j : Fin n) : a - p j < 0 := by linarith [(hp_strip j).1]
      simp only [if_pos rfl]
      apply Finset.sum_eq_zero
      intro j hj
      rw [abs_of_neg (hs j), abs_of_neg haQ]
      have hpne : a - p j ≠ 0 := ne_of_lt (hs j)
      have hQne : a - Q ≠ 0 := ne_of_lt haQ
      field_simp
      norm_num
    · subst c
      have hbQ : b - Q < 0 := by linarith
      have hs (j : Fin n) : 0 < b - p j := by linarith [(hp_strip j).2]
      simp only [if_neg (ne_of_gt hab)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_of_pos (hs j), abs_of_neg hbQ]
      have hpne : b - p j ≠ 0 := ne_of_gt (hs j)
      have hQne : b - Q ≠ 0 := ne_of_lt hbQ
      field_simp
      norm_num
  have hVI (c : ℝ) (hc : c = a ∨ c = b) (hi : Complex.VerticalIntegrable f c) :
      verticalIntegral c H = verticalIntegral c f - verticalIntegral c φ := by
    unfold verticalIntegral
    rw [hHline c hc, integral_sub hi (hφint c hc), mul_sub]
  rw [hVI a (Or.inl rfl) ha, hVI b (Or.inr rfl) hb,
    hφval a (Or.inl rfl), hφval b (Or.inr rfl)] at hshift
  simp only [if_pos, if_neg (ne_of_gt hab), sub_zero] at hshift
  linear_combination -hshift

end DedekindZetaZeroFree.LargeSieve.Vendor
