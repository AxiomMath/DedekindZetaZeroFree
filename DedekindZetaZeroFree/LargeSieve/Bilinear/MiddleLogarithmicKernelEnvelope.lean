module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.LogarithmicKernelSeparation

@[expose] public section

noncomputable section

open scoped Classical ContDiff
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve

namespace MiddleLogKernel

def normalizedKernel (K : ℝ → ℂ) (χ : ℝ → ℝ) (h b x y : ℝ) : ℂ :=
  ((χ x * χ y * h * Real.exp ((x + y) / 2) : ℝ) : ℂ) *
    K (b * h * Real.exp ((x + y) / 2))

def fourierCoefficient (K : ℝ → ℂ) (χ : ℝ → ℝ) (h b t s : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ,
    normalizedKernel K χ h b p.1 p.2 *
      Complex.exp (-((2 * Real.pi * (t * p.1 + s * p.2) : ℝ) : ℂ) * Complex.I)

end MiddleLogKernel

namespace MiddleLogKernel

open Vendor.KernelSeparation

 def weightedCutoff (χ : ℝ → ℝ) (x : ℝ) : ℂ :=
  (χ x : ℂ) * (Real.exp (x / 2) : ℂ)
private lemma weightedCutoff_smooth (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (weightedCutoff χ) := by
  unfold weightedCutoff
  have he : ContDiff ℝ ∞ (fun x : ℝ => Real.exp (x / 2)) :=
    Real.contDiff_exp.comp (contDiff_id.div_const 2)
  exact (Complex.ofRealCLM.contDiff.comp hχ).mul (Complex.ofRealCLM.contDiff.comp he)
private lemma weightedCutoff_support (χ : ℝ → ℝ) (R : ℝ)
    (hs : Function.support χ ⊆ Set.Icc (-R) R) :
    Function.support (weightedCutoff χ) ⊆ Set.Icc (-R) R := by
  intro x hx
  apply hs
  contrapose! hx
  have hx0 : χ x = 0 := by simpa only [Function.mem_support, not_not] using hx
  simp [weightedCutoff, Function.mem_support, hx0]
private lemma normalized_eq (K : ℝ → ℂ) (χ : ℝ → ℝ) (h b x y : ℝ) :
    MiddleLogKernel.normalizedKernel K χ h b x y =
      (h : ℂ) * logLocalized (weightedCutoff χ) (weightedCutoff χ) K (b*h) (x,y) := by
  simp only [MiddleLogKernel.normalizedKernel, logLocalized, weightedCutoff]
  rw [show (x+y)/2 = x/2 + y/2 by ring, Real.exp_add]
  push_cast
  ring
private lemma phase_pair (t s x y : ℝ) :
    phase (-t) x * phase (-s) y =
      Complex.exp (-((2 * Real.pi * (t*x+s*y) : ℝ) : ℂ) * Complex.I) := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
private lemma normalized_coefficient (K : ℝ → ℂ) (χ : ℝ → ℝ) (h b t s : ℝ)
    (hInt : Integrable (logLocalized (weightedCutoff χ) (weightedCutoff χ) K (b*h))) :
    MiddleLogKernel.fourierCoefficient K χ h b t s =
      (h : ℂ) * coefficient (logLocalized (weightedCutoff χ) (weightedCutoff χ) K (b*h)) t s := by
  let H := logLocalized (weightedCutoff χ) (weightedCutoff χ) K (b*h)
  have hp : Continuous (fun p : ℝ × ℝ => phase (-t) p.1 * phase (-s) p.2) := by
    dsimp [phase]
    fun_prop
  have hInt' : Integrable (fun p : ℝ × ℝ => H p * phase (-t) p.1 * phase (-s) p.2) := by
    refine Integrable.mono' hInt.norm ?_ ?_
    · exact (hInt.aestronglyMeasurable.mul hp.aestronglyMeasurable).congr
        (Filter.Eventually.of_forall (fun p => by dsimp [H]; ring))
    · filter_upwards with p
      simp [norm_mul, phase, Complex.norm_exp, H]
  simp only [MiddleLogKernel.fourierCoefficient, normalized_eq, ← phase_pair]
  rw [show (fun p : ℝ × ℝ => (h : ℂ) * H p * (phase (-t) p.1 * phase (-s) p.2)) =
      (fun p : ℝ × ℝ => (h : ℂ) * (H p * phase (-t) p.1 * phase (-s) p.2)) by ext; ring,
    integral_const_mul]
  congr 1
  rw [Measure.volume_eq_prod]
  exact integral_prod _ (by simpa only [Measure.volume_eq_prod] using hInt')

private lemma phase_positive_pair (t s x y : ℝ) :
    phase t x * phase s y =
      Complex.exp (((2 * Real.pi * (t*x+s*y) : ℝ) : ℂ) * Complex.I) := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end MiddleLogKernel

open MiddleLogKernel Vendor.KernelSeparation

private lemma fixed_box_fourier :
    ∀ R : ℝ, 0 < R → ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ H → Function.support H ⊆ Set.Icc (-R) R ×ˢ Set.Icc (-R) R →
      (∀ t s : ℝ, ‖coefficient H t s‖ ≤ A * boxJet R H / ((1+t^2)*(1+s^2))) ∧
      fourierL1 H ≤ A * Real.pi ^ 2 * boxJet R H := by
  intro R hR
  obtain ⟨A₁, hA₁, hpraw⟩ := Vendor.BoxFourier.coefficient_box_bound R hR
  have hp : ∀ H : ℝ × ℝ → ℂ, ContDiff ℝ ∞ H →
      Function.support H ⊆ Set.Icc (-R) R ×ˢ Set.Icc (-R) R →
      ∀ t s : ℝ, ‖coefficient H t s‖ ≤ A₁ * boxJet R H / ((1+t^2)*(1+s^2)) := by
    intro H hH hs t s
    apply (le_div_iff₀ (by positivity : 0 < (1+t^2)*(1+s^2))).2
    have ht := hpraw H hH hs t s
    change (1+t^2)*(1+s^2)*‖coefficient H t s‖ ≤ A₁*boxJet R H at ht
    nlinarith
  obtain ⟨A₂, hA₂, hL⟩ := fourierL1_le_boxJet R hR
  refine ⟨max A₁ A₂, lt_of_lt_of_le hA₁ (le_max_left _ _), ?_⟩
  intro H hH hs
  have hc : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hs
  have h0 : 0 ≤ boxJet R H := by
    have hL0 := (compact_smooth_fourier H hH hc).2.2.1
    have hLH := hL H hH hs
    nlinarith
  constructor
  · intro t s
    exact (hp H hH hs t s).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) h0) (by positivity))
  · have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hm : A₂ ≤ max A₁ A₂ * Real.pi ^ 2 := by
      have hmax : 0 ≤ max A₁ A₂ := (lt_of_lt_of_le hA₁ (le_max_left _ _)).le
      nlinarith [le_max_right A₁ A₂]
    exact (hL H hH hs).trans (mul_le_mul_of_nonneg_right hm h0)

theorem bilinear_middle_log_kernel_envelope
    (D : ℝ) (r : ℕ) (W : ℝ → ℂ) (α β : ℝ)
    (hD : 0 < D) (hr : 1 ≤ r) (hW : ContDiff ℝ ∞ W)
    (hsupp : Function.support W ⊆ Set.Icc α β) (hα : 0 < α) (hαβ : α < β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχ_one : ∀ x ∈ Set.Icc 0 (Real.log 2), χ x = 1)
    (hχ_supp : Function.support χ ⊆ Set.Icc (-1) (1 + Real.log 2)) :
    let K := SquareSecondPass.reflectedTransform D r W
    ∃ C : ℝ, 0 < C ∧ ∀ θ b h : ℝ,
      1 ≤ θ → 1 ≤ b →
      1 / (Real.sqrt 2 * θ) ≤ h → h ≤ Real.sqrt 2 * θ →
      (∀ t s : ℝ,
        ‖MiddleLogKernel.fourierCoefficient K χ h b t s‖ ≤
          C * θ * b⁻¹ ^ 2 / ((1 + t ^ 2) * (1 + s ^ 2))) ∧
      Integrable (fun p : ℝ × ℝ =>
        MiddleLogKernel.normalizedKernel K χ h b p.1 p.2) ∧
      Integrable (fun p : ℝ × ℝ =>
        MiddleLogKernel.fourierCoefficient K χ h b p.1 p.2) ∧
      (∀ x y : ℝ,
        MiddleLogKernel.normalizedKernel K χ h b x y =
          ∫ p : ℝ × ℝ,
            MiddleLogKernel.fourierCoefficient K χ h b p.1 p.2 *
              Complex.exp
                (((2 * Real.pi * (p.1 * x + p.2 * y) : ℝ) : ℂ) * Complex.I)) ∧
      (∫ p : ℝ × ℝ,
        ‖MiddleLogKernel.fourierCoefficient K χ h b p.1 p.2‖) ≤
          C * Real.pi ^ 2 * θ * b⁻¹ ^ 2 := by
  dsimp only
  let K := SquareSecondPass.reflectedTransform D r W
  have hbounds := bilinear_middle_double_reflection_bounds D r W α β hD hr hW hsupp hα hαβ
  choose E hEpos hE using fun j : ℕ => hbounds.2.2.2.1 j 2 (by norm_num)
  let B := ∑ j ∈ Finset.range 5, E j
  have hBle : ∀ j ≤ 4, E j ≤ B := by
    intro j hj
    apply Finset.single_le_sum (fun i hi => (hEpos i).le)
    simp only [Finset.mem_range]
    omega
  have hBpos : 0 < B := lt_of_lt_of_le (hEpos 0) (hBle 0 (by omega))
  have hEB : ∀ j ≤ 4, ∀ x : ℝ, 0 < x → ‖Vendor.EulerIter j K x‖ ≤ B * Real.rpow x (-2) := by
    intro j hj x hx
    exact (hE j x hx).trans (mul_le_mul_of_nonneg_right (hBle j hj) (Real.rpow_nonneg hx.le _))
  have hχs : Function.support χ ⊆ Set.Icc (-2) 2 := by
    intro x hx
    have hmem := hχ_supp hx
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    constructor <;> linarith [hmem.1, hmem.2]
  have hwc := weightedCutoff_smooth χ hχ
  have hwcs := weightedCutoff_support χ 2 hχs
  obtain ⟨L, hL, hloc⟩ := logLocalized_uniform_fourier_bound 2 2 (by norm_num) (by norm_num)
    (weightedCutoff χ) (weightedCutoff χ) hwc hwc hwcs hwcs
  obtain ⟨A, hA, hfour⟩ := fixed_box_fourier 2 (by norm_num)
  refine ⟨A*L*B*Real.sqrt 2, by positivity, ?_⟩
  intro θ b h hθ hb hl hu
  have hθ0 : 0 < θ := by linarith
  have hb0 : 0 < b := by linarith
  have hh : 0 < h := lt_of_lt_of_le (by positivity) hl
  have hi : h⁻¹ ≤ Real.sqrt 2 * θ := by
    simpa only [one_div] using (one_div_le hh (by positivity)).2 hl
  let H := logLocalized (weightedCutoff χ) (weightedCutoff χ) K (b*h)
  obtain ⟨hH, hsH, hjet, hL1⟩ := hloc K B hbounds.2.2.1 hBpos.le hEB (b*h) (mul_pos hb0 hh)
  have hc : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsH
  have hint : Integrable H := hH.continuous.integrable_of_hasCompactSupport hc
  have hft := compact_smooth_fourier H hH hc
  have hcoef : ∀ t s, MiddleLogKernel.fourierCoefficient K χ h b t s = (h:ℂ)*coefficient H t s :=
    fun t s => normalized_coefficient K χ h b t s hint
  have hnorm : ∀ t s, ‖MiddleLogKernel.fourierCoefficient K χ h b t s‖ = h * ‖coefficient H t s‖ := by
    intro t s
    rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hjet_scaled : h * (A * boxJet 2 H) ≤ (A*L*B*Real.sqrt 2)*θ*b⁻¹ ^ 2 := by
    calc
      h * (A * boxJet 2 H) ≤ h * (A * (L*B*Real.rpow (b*h) (-2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjet hA.le) hh.le
      _ = (A*L*B*b⁻¹ ^ 2)*h⁻¹ := by
        have hrpow : Real.rpow (b*h) (-2) = (b*h)⁻¹ ^ 2 :=
          (Real.rpow_neg_eq_inv_rpow (b*h) 2).trans (Real.rpow_two _)
        rw [hrpow, mul_inv_rev]
        field_simp
        <;> ring
      _ ≤ (A*L*B*Real.sqrt 2)*θ*b⁻¹ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hi (show 0 ≤ A*L*B*b⁻¹ ^ 2 by positivity)
        nlinarith
  have hfourH := hfour H hH hsH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t s
    change ‖MiddleLogKernel.fourierCoefficient K χ h b t s‖ ≤ _
    rw [hnorm]
    have hden : 0 ≤ (1+t^2)*(1+s^2) := by positivity
    calc h * ‖coefficient H t s‖
        ≤ h * (A * boxJet 2 H / ((1+t^2)*(1+s^2))) :=
          mul_le_mul_of_nonneg_left (hfourH.1 t s) hh.le
      _ = h * (A * boxJet 2 H) / ((1+t^2)*(1+s^2)) := by ring
      _ ≤ (A*L*B*Real.sqrt 2)*θ*b⁻¹ ^ 2 / ((1+t^2)*(1+s^2)) :=
        div_le_div_of_nonneg_right hjet_scaled hden
  · have := hint.const_mul (h:ℂ)
    exact this.congr (Filter.Eventually.of_forall (fun p => (normalized_eq K χ h b p.1 p.2).symm))
  · have hfint : Integrable (fun p : ℝ × ℝ => coefficient H p.1 p.2) := by
      simpa only [Measure.volume_eq_prod] using hft.1
    exact (hfint.const_mul (h:ℂ)).congr (Filter.Eventually.of_forall (fun p => (hcoef p.1 p.2).symm))
  · intro x y
    change MiddleLogKernel.normalizedKernel K χ h b x y = _
    rw [normalized_eq]
    change (h:ℂ) * H (x,y) =
      ∫ p : ℝ × ℝ, MiddleLogKernel.fourierCoefficient K χ h b p.1 p.2 *
        Complex.exp (((2*Real.pi*(p.1*x+p.2*y) : ℝ) : ℂ) * Complex.I)
    rw [(hft.2.2.2 x y).2, ← integral_prod _ (hft.2.2.2 x y).1]
    rw [← integral_const_mul, Measure.volume_eq_prod]
    simp_rw [hcoef]
    apply integral_congr_ae
    filter_upwards with p
    rw [← phase_positive_pair]
    ring
  · change (∫ p : ℝ × ℝ, ‖MiddleLogKernel.fourierCoefficient K χ h b p.1 p.2‖) ≤ _
    simp_rw [hnorm]
    rw [integral_const_mul, Measure.volume_eq_prod, integral_prod _ hft.1.norm]
    change h * fourierL1 H ≤ _
    have hs := mul_le_mul_of_nonneg_left hfourH.2 hh.le
    have hs' := mul_le_mul_of_nonneg_right hjet_scaled (sq_nonneg Real.pi)
    nlinarith

end DedekindZetaZeroFree.LargeSieve

end
