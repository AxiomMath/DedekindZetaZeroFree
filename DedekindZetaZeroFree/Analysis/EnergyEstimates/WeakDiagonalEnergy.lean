module

public import DedekindZetaZeroFree.Analysis.EnergyEstimates.InvariantFlowCaccioppoli
public import DedekindZetaZeroFree.Adeles.Quotients.CuspCutoffs.WeakIntegrationByParts

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeWeakEnergy
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming compact_flow_weak_ibp → compact_flow_weak_ibp
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming flow_ae_differentiable → flow_ae_differentiable
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.Caccioppoli renaming cutoff_young → cutoff_young
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.Caccioppoli renaming finite_energy_of_cutoff_bound → finite_energy_of_cutoff_bound
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private theorem weak_cutoff_derivative
    (q : ℝ → X → X) (hq : Continuous (Function.uncurry q))
    (hμ : ∀ t, MeasurePreserving (q t) μ μ)
    (hz : ∀ x, q 0 x = x) (ha : ∀ s t x, q (s+t) x = q t (q s x))
    (χ : X → ℝ) (hχ : Continuous χ) (L : ℝ≥0)
    (hLip : ∀ x, LipschitzWith L (fun t => (χ (q t x) : ℂ))) :
    (∀ᵐ x ∂μ, HasDerivAt (fun t => χ (q t x))
      (deriv (fun t => (χ (q t x) : ℂ)) 0).re 0) ∧
    ∀ x, |(deriv (fun t => (χ (q t x) : ℂ)) 0).re| ≤ L := by
  constructor
  · have hd := flow_ae_differentiable μ q hq hμ hz ha
      (fun x => (χ x : ℂ)) (Complex.continuous_ofReal.comp hχ) L
      (fun x => (hLip x).lipschitzOnWith)
    filter_upwards [hd] with x hx
    convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hx.hasDerivAt using 1
    · funext t; rfl
    · rfl
  · intro x
    exact (Complex.abs_re_le_norm _).trans (norm_deriv_le_of_lipschitz (hLip x))

private theorem squared_cutoff_lipschitz
    (q : ℝ → X → X) (χ : X → ℝ) (L : ℝ≥0)
    (hχb : ∀ x, |χ x| ≤ 1)
    (hLip : ∀ x, LipschitzWith L (fun t => (χ (q t x) : ℂ))) (x : X) :
    LipschitzWith (2 * L) (fun t => ((χ (q t x) ^ 2 : ℝ) : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hl := (hLip x).dist_le_mul s t
  have hs := hχb (q s x)
  have ht := hχb (q t x)
  simp only [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
    ← Complex.ofReal_sub] at hl ⊢
  rw [show χ (q s x) ^ 2 - χ (q t x) ^ 2 =
    (χ (q s x) - χ (q t x)) * (χ (q s x) + χ (q t x)) by ring, abs_mul]
  have hb : |χ (q s x) + χ (q t x)| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  norm_num only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith [abs_nonneg (χ (q s x) - χ (q t x))]

private theorem weak_real_cutoff_identity
    (q : ℝ → X → X) (hq : Continuous (Function.uncurry q))
    (hμ : ∀ t, MeasurePreserving (q t) μ μ)
    (hz : ∀ x, q 0 x = x) (ha : ∀ s t x, q (s+t) x = q t (q s x))
    (χ dχ : X → ℝ) (u du ddu : X → ℂ)
    (hχ : Continuous χ) (hu : Continuous u)
    (hdu : Continuous du) (hddu : Continuous ddu) (hs : HasCompactSupport χ)
    (hχd : ∀ᵐ x ∂μ, HasDerivAt (fun t => χ (q t x)) (dχ x) 0)
    (hud : ∀ x t, HasDerivAt (fun s => u (q s x)) (du (q t x)) t)
    (hdud : ∀ x t, HasDerivAt (fun s => du (q s x)) (ddu (q t x)) t)
    (L : ℝ≥0) (hχb : ∀ x, |χ x| ≤ 1)
    (hLip : ∀ x, LipschitzWith L (fun t => (χ (q t x) : ℂ))) :
    Integrable (fun x => 2 * χ x * dχ x * (star (u x) * du x).re) μ ∧
    (∫ x, χ x ^ 2 * ‖du x‖ ^ 2 ∂μ) =
      -(∫ x, χ x ^ 2 * (star (u x) * ddu x).re ∂μ) -
        ∫ x, 2 * χ x * dχ x * (star (u x) * du x).re ∂μ := by
  let C : X → ℂ := fun x => ((χ x ^ 2 : ℝ) : ℂ)
  let J : X → ℂ := fun x => star (u x) * du x
  let dC : X → ℂ := fun x => ((2 * χ x * dχ x : ℝ) : ℂ)
  let dJ : X → ℂ := fun x => ((‖du x‖ ^ 2 : ℝ) : ℂ) + star (u x) * ddu x
  have hCs : HasCompactSupport C := by
    exact (show HasCompactSupport (fun x => χ x ^ 2) by
        have hm : HasCompactSupport (fun x => χ x * χ x) := hs.mul_right
        simpa only [pow_two] using hm).comp_left (show Complex.ofReal 0 = 0 by rfl)
  have hCd : ∀ᵐ x ∂μ, HasDerivAt (fun t => C (q t x)) (dC x) 0 := by
    filter_upwards [hχd] with x hx
    convert (hx.pow 2).ofReal_comp using 1 <;> simp [dC, hz]
  have hJd : ∀ x t, HasDerivAt (fun s => J (q s x)) (dJ (q t x)) t := by
    intro x t
    have hh := ((hud x t).star).mul (hdud x t)
    convert hh using 1
    dsimp [dJ]
    congr 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
  obtain ⟨hiC, he⟩ := compact_flow_weak_ibp μ q hq hμ hz ha C J dC dJ
    (Complex.continuous_ofReal.comp (hχ.pow 2)) (hu.star.mul hdu)
    ((Complex.continuous_ofReal.comp (hdu.norm.pow 2)).add (hu.star.mul hddu)) hCs hCd hJd (2*L)
    (fun x => (squared_cutoff_lipschitz q χ L hχb hLip x).lipschitzOnWith)
  have hiE : Integrable (fun x => χ x ^ 2 * ‖du x‖ ^ 2) μ :=
    ((hχ.pow 2).mul (hdu.norm.pow 2)).integrable_of_hasCompactSupport
      ((show HasCompactSupport (fun x => χ x ^ 2) by
        have hm : HasCompactSupport (fun x => χ x * χ x) := hs.mul_right
        simpa only [pow_two] using hm).mul_right)
  have hiS : Integrable (fun x => χ x ^ 2 * (star (u x) * ddu x).re) μ :=
    ((hχ.pow 2).mul (Complex.continuous_re.comp (hu.star.mul hddu))).integrable_of_hasCompactSupport
      ((show HasCompactSupport (fun x => χ x ^ 2) by
        have hm : HasCompactSupport (fun x => χ x * χ x) := hs.mul_right
        simpa only [pow_two] using hm).mul_right)
  have hiCross : Integrable (fun x => 2 * χ x * dχ x * (star (u x) * du x).re) μ := by
    simpa [dC, J, Complex.mul_re] using hiC.re
  refine ⟨hiCross, ?_⟩
  have hiCDJ : Integrable (fun x => C x * dJ x) μ :=
    ((Complex.continuous_ofReal.comp (hχ.pow 2)).mul
      ((Complex.continuous_ofReal.comp (hdu.norm.pow 2)).add (hu.star.mul hddu))).integrable_of_hasCompactSupport hCs.mul_right
  apply_fun Complex.re at he
  have hRe1 := integral_re hiCDJ
  have hRe2 := integral_re hiC
  change (∫ x, (C x * dJ x).re ∂μ) = (∫ x, C x * dJ x ∂μ).re at hRe1
  change (∫ x, (dC x * J x).re ∂μ) = (∫ x, dC x * J x ∂μ).re at hRe2
  rw [← hRe1, Complex.neg_re, ← hRe2] at he
  have hre : (fun x => (C x * dJ x).re) = fun x =>
      χ x ^ 2 * ‖du x‖ ^ 2 + χ x ^ 2 * (star (u x) * ddu x).re := by
    funext x
    simp only [C, dJ, Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_add]
  rw [hre, integral_add hiE hiS] at he
  have hrCross : (fun x => (dC x * J x).re) = fun x =>
      2 * χ x * dχ x * (star (u x) * du x).re := by
    funext x
    simp [dC, J, Complex.mul_re]
  rw [hrCross] at he
  linarith

private theorem weak_diagonal_cutoff_estimate
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ → X → X)
    (hq : ∀ i, Continuous (Function.uncurry (q i)))
    (hμ : ∀ i t, MeasurePreserving (q i t) μ μ)
    (hz : ∀ i x, q i 0 x = x)
    (ha : ∀ i s t x, q i (s+t) x = q i t (q i s x))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (χ : X → ℝ) (dχ : ι → X → ℝ)
    (u : X → ℂ) (du ddu : ι → X → ℂ)
    (hχ : Continuous χ) (hu : Continuous u)
    (hdu : ∀ i, Continuous (du i)) (hddu : ∀ i, Continuous (ddu i))
    (hχc : HasCompactSupport χ)
    (hχd : ∀ i, ∀ᵐ x ∂μ, HasDerivAt (fun t => χ (q i t x)) (dχ i x) 0)
    (hud : ∀ i x t, HasDerivAt (fun s => u (q i s x)) (du i (q i t x)) t)
    (hdud : ∀ i x t, HasDerivAt (fun s => du i (q i s x)) (ddu i (q i t x)) t)
    (L : ℝ≥0) (hχb : ∀ x, |χ x| ≤ 1)
    (hLip : ∀ i x, LipschitzWith L (fun t => (χ (q i t x) : ℂ)))
    (hu2 : MemLp u 2 μ)
    (A : ℝ) (hA : ∀ x, (∑ i, c i * dχ i x ^ 2) ≤ A) :
    (∫ x, χ x ^ 2 * (∑ i, c i * ‖du i x‖ ^ 2) ∂μ) ≤
      2 * (∫ x, χ x ^ 2 * ‖u x‖ * ‖∑ i, (c i : ℂ) * ddu i x‖ ∂μ) +
      4 * A * (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  have hχsq : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [pow_two] using (show HasCompactSupport (fun x => χ x * χ x) from hχc.mul_right)
  have hiE (i : ι) : Integrable (fun x => χ x ^ 2 * ‖du i x‖ ^ 2) μ :=
    ((hχ.pow 2).mul ((hdu i).norm.pow 2)).integrable_of_hasCompactSupport hχsq.mul_right
  have hiS (i : ι) : Integrable (fun x => χ x ^ 2 * (star (u x) * ddu i x).re) μ :=
    ((hχ.pow 2).mul (Complex.continuous_re.comp (hu.star.mul (hddu i)))).integrable_of_hasCompactSupport hχsq.mul_right
  have hiC (i : ι) : Integrable (fun x => 2 * χ x * dχ i x * (star (u x) * du i x).re) μ :=
    (weak_real_cutoff_identity (q i) (hq i) (hμ i) (hz i) (ha i)
      χ (dχ i) u (du i) (ddu i) hχ hu (hdu i) (hddu i) hχc
      (hχd i) (hud i) (hdud i) L hχb (hLip i)).1
  let E := ∫ x, χ x ^ 2 * (∑ i, c i * ‖du i x‖ ^ 2) ∂μ
  let S := ∫ x, χ x ^ 2 * (star (u x) * (∑ i, (c i : ℂ) * ddu i x)).re ∂μ
  let C := ∫ x, ∑ i, c i * (2 * χ x * dχ i x * (star (u x) * du i x).re) ∂μ
  let D := A * ∫ x, ‖u x‖ ^ 2 ∂μ
  let V := ∫ x, χ x ^ 2 * ‖u x‖ * ‖∑ i, (c i : ℂ) * ddu i x‖ ∂μ
  have he : E = -S - C := by
    have hid (i : ι) := (weak_real_cutoff_identity (q i) (hq i) (hμ i) (hz i) (ha i)
      χ (dχ i) u (du i) (ddu i) hχ hu (hdu i) (hddu i) hχc
      (hχd i) (hud i) (hdud i) L hχb (hLip i)).2
    have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => congrArg (fun r : ℝ => c i * r) (hid i))
    dsimp only [E, S, C]
    have heq : (fun x => χ x ^ 2 * (∑ i, c i * ‖du i x‖ ^ 2)) =
        fun x => ∑ i, c i * (χ x ^ 2 * ‖du i x‖ ^ 2) := by
      funext x
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hseq : (fun x => χ x ^ 2 * (star (u x) * (∑ i, (c i : ℂ) * ddu i x)).re) =
        fun x => ∑ i, c i * (χ x ^ 2 * (star (u x) * ddu i x).re) := by
      funext x
      simp only [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_left_comm (star (u x)), Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    rw [heq, hseq]
    rw [integral_finsetSum _ (fun i _ => (hiE i).const_mul (c i)),
      integral_finsetSum _ (fun i _ => (hiS i).const_mul (c i)),
      integral_finsetSum _ (fun i _ => (hiC i).const_mul (c i))]
    simp_rw [integral_const_mul]
    simpa only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib] using hh
  have hiCsum : Integrable (fun x => ∑ i, c i * (2 * χ x * dχ i x * (star (u x) * du i x).re)) μ :=
    integrable_finsetSum _ (fun i _ => (hiC i).const_mul (c i))
  have hiEsum : Integrable (fun x => χ x ^ 2 * ∑ i, c i * ‖du i x‖ ^ 2) μ := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun i _ => by
      convert (hiE i).const_mul (c i) using 1 <;> funext x <;> ring)
  have hb : |C| ≤ E / 2 + 2 * D := by
    calc
      |C| ≤ ∫ x, |∑ i, c i * (2 * χ x * dχ i x * (star (u x) * du i x).re)| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x, χ x ^ 2 * (∑ i, c i * ‖du i x‖ ^ 2) / 2 +
          2 * (A * ‖u x‖ ^ 2) ∂μ := by
        apply integral_mono hiCsum.abs ((hiEsum.div_const 2).add ((hu2.norm.integrable_sq.const_mul A).const_mul 2))
        intro x
        calc
          _ ≤ ∑ i, |c i * (2 * χ x * dχ i x * (star (u x) * du i x).re)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, c i * (χ x ^ 2 * ‖du i x‖ ^ 2 / 2 + 2 * dχ i x ^ 2 * ‖u x‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul, abs_of_nonneg (hc i)]
            exact mul_le_mul_of_nonneg_left (cutoff_young _ _ _ _) (hc i)
          _ = χ x ^ 2 * (∑ i, c i * ‖du i x‖ ^ 2) / 2 +
              2 * ((∑ i, c i * dχ i x ^ 2) * ‖u x‖ ^ 2) := by
            simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
              Finset.sum_div]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
          _ ≤ _ := by
            have hh := mul_le_mul_of_nonneg_right (hA x) (sq_nonneg ‖u x‖)
            simp only [Pi.add_apply]
            linarith
      _ = E / 2 + 2 * D := by rw [integral_add (hiEsum.div_const 2) ((hu2.norm.integrable_sq.const_mul A).const_mul 2),
        integral_div, integral_const_mul, integral_const_mul]
  have hs : -S ≤ V := by
    have hiV : Integrable (fun x => χ x ^ 2 * ‖u x‖ * ‖∑ i, (c i : ℂ) * ddu i x‖) μ :=
      (((hχ.pow 2).mul hu.norm).mul (continuous_finsetSum _ (fun i _ =>
        continuous_const.mul (hddu i))).norm).integrable_of_hasCompactSupport hχsq.mul_right.mul_right
    have hiSS : Integrable (fun x => χ x ^ 2 * (star (u x) * (∑ i, (c i : ℂ) * ddu i x)).re) μ :=
      ((hχ.pow 2).mul (Complex.continuous_re.comp (hu.star.mul (continuous_finsetSum _ (fun i _ =>
        continuous_const.mul (hddu i)))))).integrable_of_hasCompactSupport hχsq.mul_right
    rw [show -S = ∫ x, -(χ x ^ 2 * (star (u x) * (∑ i, (c i : ℂ) * ddu i x)).re) ∂μ by
      rw [integral_neg]]
    apply integral_mono hiSS.neg hiV
    intro x
    have hh := (neg_le_abs ((star (u x) * (∑ i, (c i : ℂ) * ddu i x)).re)).trans
      (Complex.abs_re_le_norm _)
    rw [norm_mul, norm_star] at hh
    change -(χ x ^ 2 * _) ≤ χ x ^ 2 * ‖u x‖ * _
    have hx := mul_le_mul_of_nonneg_left hh (sq_nonneg (χ x))
    nlinarith only [hx]
  dsimp only [E, V, D] at *
  linarith [neg_le_abs C]

 theorem weak_diagonal_energy_finite
    {ι : Type*} [Fintype ι]
    (q : ι → ℝ → X → X)
    (hq : ∀ i, Continuous (Function.uncurry (q i)))
    (hμ : ∀ i t, MeasurePreserving (q i t) μ μ)
    (hz : ∀ i x, q i 0 x = x)
    (ha : ∀ i s t x, q i (s+t) x = q i t (q i s x))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (u v : X → ℂ) (du ddu : ι → X → ℂ)
    (hu : Continuous u) (hdu : ∀ i, Continuous (du i))
    (hddu : ∀ i, Continuous (ddu i))
    (hud : ∀ i x t, HasDerivAt (fun s => u (q i s x)) (du i (q i t x)) t)
    (hdud : ∀ i x t, HasDerivAt (fun s => du i (q i s x)) (ddu i (q i t x)) t)
    (hEq : ∀ x, (∑ i, (c i : ℂ) * ddu i x) = v x)
    (hu2 : MemLp u 2 μ) (hv2 : MemLp v 2 μ)
    (χ : ℕ → X → ℝ) (hχ : ∀ n, Continuous (χ n))
    (hχc : ∀ n, HasCompactSupport (χ n))
    (hχb : ∀ n x, |χ n x| ≤ 1)
    (hχlim : ∀ x, Filter.Tendsto (fun n => χ n x) Filter.atTop (𝓝 1))
    (L : ℝ≥0) (hLip : ∀ n i x, LipschitzWith L (fun t => (χ n (q i t x) : ℂ))) :
    (∫⁻ x, ENNReal.ofReal (∑ i, c i * ‖du i x‖ ^ 2) ∂μ) < ⊤ := by
  let dχ : ℕ → ι → X → ℝ := fun n i x =>
    (deriv (fun t => (χ n (q i t x) : ℂ)) 0).re
  let A : ℝ := ∑ i, c i * (L : ℝ) ^ 2
  have hD (n : ℕ) (i : ι) := weak_cutoff_derivative (q i) (hq i) (hμ i)
    (hz i) (ha i) (χ n) (hχ n) L (hLip n i)
  have hA (n : ℕ) (x : X) : (∑ i, c i * dχ n i x ^ 2) ≤ A := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hc i)
    have hh := (hD n i).2 x
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) L.coe_nonneg).mpr hh
  have hE : Continuous (fun x => ∑ i, c i * ‖du i x‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul ((hdu i).norm.pow 2))
  have hp : Integrable (fun x => ‖u x‖ * ‖v x‖) μ := hu2.norm.integrable_mul hv2.norm
  have hpχ (n : ℕ) : Integrable (fun x => χ n x ^ 2 * ‖u x‖ * ‖v x‖) μ := by
    apply hp.mono' (((hχ n).pow 2).aestronglyMeasurable.mul hu2.norm.aestronglyMeasurable
      |>.mul hv2.norm.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro x
    have hb : χ n x ^ 2 ≤ 1 := by nlinarith [sq_abs (χ n x), hχb n x, abs_nonneg (χ n x)]
    change ‖χ n x ^ 2 * ‖u x‖ * ‖v x‖‖ ≤ ‖u x‖ * ‖v x‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x)))]
  apply finite_energy_of_cutoff_bound _ hE.measurable
    (fun x => Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (sq_nonneg _)))
    χ (fun n => (hχ n).measurable) hχlim
    (fun n => ((hχ n).pow 2 |>.mul hE).integrable_of_hasCompactSupport (by
      have hs : HasCompactSupport (fun x => χ n x ^ 2) := by
        simpa only [pow_two] using
          (show HasCompactSupport (fun x => χ n x * χ n x) from (hχc n).mul_right)
      exact hs.mul_right))
    (2 * (∫ x, ‖u x‖ * ‖v x‖ ∂μ) + 4 * A * (∫ x, ‖u x‖ ^ 2 ∂μ))
  intro n
  have hh := weak_diagonal_cutoff_estimate q hq hμ hz ha c hc (χ n) (dχ n) u du ddu
    (hχ n) hu hdu hddu (hχc n) (fun i => (hD n i).1) hud hdud L (hχb n) (hLip n) hu2 A (hA n)
  simp_rw [hEq] at hh
  have hb : (∫ x, χ n x ^ 2 * ‖u x‖ * ‖v x‖ ∂μ) ≤ (∫ x, ‖u x‖ * ‖v x‖ ∂μ) := by
    apply integral_mono (hpχ n) hp
    intro x
    have hb : χ n x ^ 2 ≤ 1 := by nlinarith [sq_abs (χ n x), hχb n x, abs_nonneg (χ n x)]
    nlinarith [mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x)))]
  linarith

end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeWeakEnergy

end
