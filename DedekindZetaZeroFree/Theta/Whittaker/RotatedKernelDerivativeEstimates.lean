module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxQuadraticKernelDerivatives

noncomputable def radialOp (F : ℝ → ℂ → ℂ) : ℝ → ℂ → ℂ :=
  fun ρ x => ((ρ / 2 : ℝ) : ℂ) * deriv (fun r : ℝ => F r x) ρ

end DedekindZetaZeroFree.KPCplxQuadraticKernelDerivatives

end

section

namespace DedekindZetaZeroFree.KPCplxRotatedKernelEstimates

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable def radialUnit (ρ : ℝ) (u : ℂˣ) : ℂˣ :=
  if hρ : 0 < ρ then
    Units.mk0 ((ρ : ℂ) * (u : ℂ)) (by
      have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
      exact mul_ne_zero hρ0 u.ne_zero)
  else 1

theorem exists_norm_eq_one_radialUnit_eq (y : ℂˣ) :
    ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ radialUnit ‖(y : ℂ)‖ u = y := by
  have hr : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  let a : ℂˣ := Units.mk0 (‖(y : ℂ)‖ : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  refine ⟨a⁻¹ * y, ?_, ?_⟩
  · change ‖((a⁻¹ * y : ℂˣ) : ℂ)‖ = 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    change (‖(‖(y : ℂ)‖ : ℂ)‖)⁻¹ * ‖(y : ℂ)‖ = 1
    simp [Complex.norm_real, abs_of_pos hr, hr.ne']
  · apply Units.ext
    simp only [radialUnit, dif_pos hr, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
    change (‖(y : ℂ)‖ : ℂ) * ((‖(y : ℂ)‖ : ℂ)⁻¹ * (y : ℂ)) = (y : ℂ)
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]

noncomputable def horizontalRealDerivative (F : ℝ → ℂ → ℂ) : ℝ → ℂ → ℂ :=
  fun ρ x => deriv (fun t : ℝ => F ρ ⟨t, x.im⟩) x.re

instance areaHaar : euclideanArea.IsAddHaarMeasure := by
  unfold euclideanArea
  infer_instance

noncomputable def rationalEnvelope (h : ℕ) (ρ : ℝ) (x : ℂ) : ℝ :=
  ρ ^ (4 / 3 : ℝ) * (ρ ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2)

lemma rationalEnvelope_scaled (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    rationalEnvelope h ρ (ρ • x) =
      ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)) *
        (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  unfold rationalEnvelope
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]
  have he : ρ ^ 2 + ρ ^ 2 * ‖x‖ ^ 2 = ρ ^ 2 * (1 + ‖x‖ ^ 2) := by ring
  rw [he, Real.mul_rpow (sq_nonneg ρ) (by positivity), ← Real.rpow_natCast_mul hρ.le]
  rw [← mul_assoc, ← Real.rpow_add hρ]
  congr 2
  ring

lemma rationalEnvelope_normalized (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) :
    rationalEnvelope h ρ x =
      ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)) *
        (1 + ‖ρ⁻¹ • x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) := by
  simpa only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] using
    rationalEnvelope_scaled h ρ hρ (ρ⁻¹ • x)

lemma rationalEnvelope_one_integrable (h : ℕ) :
    Integrable (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2))
      euclideanArea := by
  have hh : (Module.finrank ℝ ℂ : ℝ) < (8 / 3 : ℝ) + (h : ℝ) := by
    simp only [Complex.finrank_real_complex, Nat.cast_ofNat]
    have hn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
    linarith
  letI : euclideanArea.IsAddHaarMeasure := by
    unfold euclideanArea
    infer_instance
  have he : -((8 / 3 : ℝ) + (h : ℝ)) / 2 = -(4 / 3 : ℝ) - (h : ℝ) / 2 := by ring
  simpa only [he] using (integrable_rpow_neg_one_add_norm_sq (μ := euclideanArea) hh)

lemma rationalEnvelope_integrable (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (rationalEnvelope h ρ) euclideanArea := by
  have hi := (rationalEnvelope_one_integrable h).comp_smul (inv_ne_zero hρ.ne')
  have hj := hi.const_mul (ρ ^ (-(4 / 3 : ℝ) - (h : ℝ)))
  exact hj.congr (Filter.Eventually.of_forall fun x => (rationalEnvelope_normalized h ρ hρ x).symm)

lemma rationalEnvelope_integral (h : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ x : ℂ, rationalEnvelope h ρ x ∂euclideanArea) =
      (∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) ∂euclideanArea) *
        ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  simp_rw [rationalEnvelope_normalized h ρ hρ]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg euclideanArea
    (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2)) hρ.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hρ]
  ring_nf

lemma integral_bound_of_rationalEnvelope (h : ℕ) (ρ C : ℝ) (hρ : 0 < ρ)
    (F : ℂ → ℂ) (hm : AEStronglyMeasurable F euclideanArea)
    (hb : ∀ x, ‖F x‖ ≤ C * rationalEnvelope h ρ x) :
    Integrable (fun x => ‖F x‖) euclideanArea ∧
      (∫ x, ‖F x‖ ∂euclideanArea) ≤
        C * (∫ x : ℂ, (1 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ) - (h : ℝ) / 2) ∂euclideanArea) *
          ρ ^ ((2 / 3 : ℝ) - (h : ℝ)) := by
  have hi := (rationalEnvelope_integrable h ρ hρ).const_mul C
  have hf : Integrable F euclideanArea := hi.mono' hm (Filter.Eventually.of_forall hb)
  refine ⟨hf.norm, ?_⟩
  calc
    (∫ x, ‖F x‖ ∂euclideanArea) ≤ ∫ x, C * rationalEnvelope h ρ x ∂euclideanArea :=
      integral_mono hf.norm hi hb
    _ = _ := by rw [integral_const_mul, rationalEnvelope_integral h ρ hρ]; ring

lemma bottomRowNormSq_pos (g : ComplexGL2) : 0 < bottomRowNormSq g := by
  have hn : 0 ≤ bottomRowNormSq g := by unfold bottomRowNormSq; positivity
  by_contra hp
  have hz : bottomRowNormSq g = 0 := le_antisymm (le_of_not_gt hp) hn
  have h0 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    have : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = 0 := by
      unfold bottomRowNormSq at hz; nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖]
    exact norm_eq_zero.mp ((sq_eq_zero_iff.mp this))
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
    have : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 0 := by
      unfold bottomRowNormSq at hz; nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖]
    exact norm_eq_zero.mp ((sq_eq_zero_iff.mp this))
  have hd := Matrix.GeneralLinearGroup.det_ne_zero g
  apply hd
  simp [Matrix.det_fin_two, h0, h1]

end DedekindZetaZeroFree.KPCplxRotatedKernelEstimates

end
