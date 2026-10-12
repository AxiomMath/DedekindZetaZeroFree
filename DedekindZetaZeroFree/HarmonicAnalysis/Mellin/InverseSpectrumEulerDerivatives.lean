module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.PositiveSideJetSeminorms

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor.InverseSpectrumEuler

def line (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
def integrand (b : ℂ → ℂ) (j : ℕ) (c x t : ℝ) : ℂ :=
  (x : ℂ) ^ (-line c t) * (-line c t) ^ j * b (line c t)

private lemma integrand_norm (b : ℂ → ℂ)
    (j : ℕ) (c x t : ℝ) (hx : 0 < x) :
    ‖integrand b j c x t‖ =
      x ^ (-c) * ‖(-line c t) ^ j * b (line c t)‖ := by
  unfold integrand
  rw [mul_assoc, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [line, Complex.mul_re]

private lemma integrand_integrable (c : ℝ) (b : ℂ → ℂ)
    (hb : ∀ j : ℕ, Integrable (fun t : ℝ => (-line c t) ^ j * b (line c t)))
    (j : ℕ) (x : ℝ) (hx : 0 < x) : Integrable (integrand b j c x) := by
  refine (Integrable.const_mul (hb j).norm (x ^ (-c))).mono' ?_ ?_
  · have hcont : Continuous (fun t : ℝ => (x : ℂ) ^ (-line c t)) :=
      (show Continuous (fun t : ℝ => -line c t) by unfold line; fun_prop).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    convert (hcont.aestronglyMeasurable.mul (hb j).aestronglyMeasurable) using 1
    funext t
    simp [integrand, mul_assoc]
  · exact Eventually.of_forall fun t => (integrand_norm b j c x t hx).le

private lemma integrand_deriv (b : ℂ → ℂ)
    (j : ℕ) (c x t : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => integrand b j c y t)
      ((x : ℂ)⁻¹ * integrand b (j + 1) c x t) x := by
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := -line c t)
    (Complex.ofReal_mem_slitPlane.mpr hx)).hasDerivAt.comp_ofReal
  convert (hd.mul_const ((-line c t) ^ j)).mul_const (b (line c t)) using 1
  · rfl
  · rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
    simp only [integrand, pow_succ, div_eq_mul_inv]
    ring

theorem hasDerivAt_weighted (c : ℝ) (b : ℂ → ℂ)
    (hb : ∀ j : ℕ, Integrable (fun t : ℝ =>
      (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j * b ((c : ℂ) + (t : ℂ) * Complex.I)))
    (j : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (mellinInv c (fun s => (-s) ^ j * b s))
      ((x : ℂ)⁻¹ * mellinInv c (fun s => (-s) ^ (j + 1) * b s) x) x := by
  have hweight := hb (j + 1)
  let K : ℝ := max ((x / 2) ^ (-c - 1)) ((x + 1) ^ (-c - 1))
  have hbound : Integrable (fun t => K *
      ‖(-line c t) ^ (j + 1) * b (line c t)‖) := hweight.norm.const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y => integrand b j c y)
    (F' := fun y t => (y : ℂ)⁻¹ * integrand b (j + 1) c y t)
    (s := Set.Ioo (x / 2) (x + 1)) (bound := fun t => K *
      ‖(-line c t) ^ (j + 1) * b (line c t)‖)
    (Ioo_mem_nhds (by linarith : x / 2 < x) (by linarith : x < x + 1))
    (eventually_of_mem (Ioi_mem_nhds hx) (fun y hy =>
      (integrand_integrable c b hb j y hy).aestronglyMeasurable))
    (integrand_integrable c b hb j x hx)
    ((integrand_integrable c b hb (j + 1) x hx).const_mul _).aestronglyMeasurable
    (Eventually.of_forall (fun t y hy => by
      have hypos : 0 < y := lt_trans (by positivity : 0 < x / 2) hy.1
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos,
        integrand_norm b (j + 1) c y t hypos]
      have heq : y⁻¹ * y ^ (-c) = y ^ (-c - 1) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hypos]
        congr 1
        ring
      rw [← mul_assoc, heq]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rcases le_total (-c - 1) 0 with he | he
      · exact (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x / 2) hy.1.le he).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow hypos.le hy.2.le he).trans (le_max_right _ _))) hbound
    (Eventually.of_forall (fun t y hy => integrand_deriv b j c y t
      (lt_trans (by positivity : 0 < x / 2) hy.1)))
  have hkey := key.2.const_mul (((1 / (2 * Real.pi)) : ℝ) : ℂ)
  simp only [integral_const_mul] at hkey
  change HasDerivAt (fun y => mellinInv c (fun s => (-s) ^ j * b s) y) _ x
  convert hkey using 1
  · funext y
    simp [mellinInv, integrand, line, RCLike.real_smul_eq_coe_mul, mul_assoc]
  · simp [mellinInv, integrand, line, RCLike.real_smul_eq_coe_mul, mul_assoc, mul_left_comm]

private lemma inverse_smooth (c : ℝ) (b : ℂ → ℂ)
    (hb : ∀ j : ℕ, Integrable (fun t : ℝ => (-line c t) ^ j * b (line c t))) :
    ∀ (k j : ℕ), ContDiffOn ℝ (k : ℕ∞ω)
      (mellinInv c (fun s => (-s) ^ j * b s)) (Set.Ioi 0) := by
  have hd : ∀ j : ℕ, DifferentiableOn ℝ
      (mellinInv c (fun s => (-s) ^ j * b s)) (Set.Ioi 0) :=
    fun j x hx => (hasDerivAt_weighted c b hb j x hx).differentiableAt.differentiableWithinAt
  intro k
  induction k with
  | zero => intro j; exact contDiffOn_zero.mpr (hd j).continuousOn
  | succ k ih =>
    intro j
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨hd j, by simp, ?_⟩
    have hinv : ContDiffOn ℝ (k : ℕ∞ω) (fun x : ℝ => (x : ℂ)⁻¹) (Set.Ioi 0) := by
      apply ContDiffOn.inv Complex.ofRealCLM.contDiff.contDiffOn
      intro x hx
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
    exact (hinv.mul (ih (j + 1))).congr fun x hx =>
      (hasDerivAt_weighted c b hb j x hx).deriv

theorem contDiffOn_weighted (c : ℝ) (b : ℂ → ℂ)
    (hb : ∀ j : ℕ, Integrable (fun t : ℝ =>
      (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j * b ((c : ℂ) + (t : ℂ) * Complex.I)))
    (j : ℕ) : ContDiffOn ℝ ∞ (mellinInv c (fun s => (-s) ^ j * b s)) (Set.Ioi 0) := by
  exact contDiffOn_infty.mpr fun k => inverse_smooth c b hb k j

theorem EulerIter_eq_mellinInv (c : ℝ) (b : ℂ → ℂ)
    (hb : ∀ j : ℕ, Integrable (fun t : ℝ =>
      (-((c : ℂ) + (t : ℂ) * Complex.I)) ^ j * b ((c : ℂ) + (t : ℂ) * Complex.I)))
    (j : ℕ) (x : ℝ) (hx : 0 < x) :
    DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter j (mellinInv c b) x =
      mellinInv c (fun s => (-s) ^ j * b s) x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter_succ_of_pos j _ x hx]
    have heq : DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter j (mellinInv c b) =ᶠ[nhds x]
        mellinInv c (fun s => (-s) ^ j * b s) :=
      eventually_of_mem (Ioi_mem_nhds hx) (fun y hy => ih y hy)
    rw [heq.deriv_eq, (hasDerivAt_weighted c b hb j x hx).deriv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.ne'), one_mul]

end DedekindZetaZeroFree.LargeSieve.Vendor.InverseSpectrumEuler

end
