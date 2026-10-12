module

public import DedekindZetaZeroFree.Theta.Profiles.BesselSheets

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.GaussianSmoothing
open MomentSources ThetaProfileHaarSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

 instance instContinuousMulGaussianSmoothingPositiveAxis : ContinuousMul PositiveAxis :=
  ⟨(continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _⟩
 instance instMeasurableMulGaussianSmoothingPositiveAxis : MeasurableMul PositiveAxis :=
  ⟨fun _ => (continuous_const.mul continuous_id).measurable,
    fun _ => (continuous_id.mul continuous_const).measurable⟩
 instance instLocallyCompactSpaceGaussianSmoothingPositiveAxis : LocallyCompactSpace PositiveAxis := isOpen_Ioi.locallyCompactSpace

private lemma reciprocal_cancel (C A : ℝ) (r : ℕ) (hC : 0 < C) (hA : 0 < A)
    (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    thetaProfileReciprocalMellinFactor C A r s *
      ((C : ℂ) * (A : ℂ)^s * (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))^r) = 1 := by
  have h1 : Complex.Gamma (s+5/6) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : Complex.Gamma (s+7/6) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hc : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have ha : (A : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  simp only [thetaProfileReciprocalMellinFactor, reciprocalGamma,
    Complex.cpow_neg, ← mul_inv, inv_pow]
  have hg := pow_ne_zero r (mul_ne_zero h1 h2)
  calc
    _ = ((C : ℂ)⁻¹ * C) * (((A : ℂ)^s)⁻¹ * (A : ℂ)^s) *
      (((Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))^r)⁻¹ *
        (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))^r) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hc, inv_mul_cancel₀ ha, inv_mul_cancel₀ hg]; ring

private lemma axis_cpow (x : PositiveAxis) (s : ℂ) :
    (x.val : ℂ)^s = Complex.exp ((Real.log x.val : ℂ)*s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr x.property.ne'),
    ← Complex.ofReal_log x.property.le]

private lemma gaussian_contour (u : ℝ) :
    (1/(2*Real.pi) : ℝ) •
      (∫ t : ℝ, Complex.exp (-(t : ℂ)^2) * Complex.exp (-(t : ℂ)*Complex.I*u)) =
        (Real.exp (-u^2/4)/(2*Real.sqrt Real.pi) : ℝ) := by
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num) (-Complex.I*u) 0
  have he : (fun t : ℝ => Complex.exp (-(t : ℂ)^2) * Complex.exp (-(t : ℂ)*Complex.I*u)) =
      fun t : ℝ => Complex.exp ((-1 : ℂ)*t^2 + (-Complex.I*u)*t + 0) := by
    funext t
    rw [← Complex.exp_add]; congr 1; ring
  rw [he, h]
  have hs : ((Real.pi : ℂ)/ -(-1 : ℂ))^(1/2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    simp only [neg_neg, div_one]
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le (1/2 : ℝ), Real.sqrt_eq_rpow]
  have hx : (0 : ℂ) - (-Complex.I*u)^2/(4*(-1)) = (-u^2/4 : ℝ) := by
    push_cast; simp only [mul_pow, neg_pow_two, Complex.I_sq]; ring
  rw [hs, hx, ← Complex.ofReal_exp, Complex.real_smul]
  push_cast
  have hn : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hp : (Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt Real.pi_pos.le).symm
  rw [hp]; field_simp

theorem C0_pos (N : TraceHaarTransport R) (P : Packet R Q) : 0 < P.C₀ := by
  rw [C0_exact N P]
  exact polarC0_pos N P

theorem positiveSheet_pos (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    0 < P.positiveSheet x := by
  rw [positiveSheet_eq N P]
  exact sheet_pos N P x

theorem positiveSheet_nonneg (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    0 ≤ P.positiveSheet x := by
  rw [positiveSheet_eq N P]
  exact integral_nonneg (fun z => radial_nonneg P _)

theorem positiveSheet_continuous (N : TraceHaarTransport R) (P : Packet R Q) :
    Continuous P.positiveSheet := by
  rw [positiveSheet_eq N P]
  exact continuous_sheet N P

theorem positiveSheet_integrable (N : TraceHaarTransport R) (P : Packet R Q) :
    Integrable P.positiveSheet positiveHaar := by
  have hi := Complex.reCLM.integrable_comp ((sheet_mellin N P 0 (by norm_num)).1)
  simpa using hi

theorem gaussian_smoothing (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    Integrable (fun t : PositiveAxis => P.kernel t.val *
      (P.positiveSheet ⟨x.val*t.val, mul_pos x.property t.property⟩ : ℂ)) positiveHaar ∧
    (∫ t : PositiveAxis, P.kernel t.val *
      (P.positiveSheet ⟨x.val*t.val, mul_pos x.property t.property⟩ : ℂ) ∂positiveHaar) =
      (thetaReflectionGaussian x.val : ℂ) := by
  have hC := C0_pos N P
  have hA := P.A₀_pos
  have hr : 1 ≤ Fintype.card (InfinitePlace F) := Fintype.card_pos_iff.mpr ⟨P.v₀⟩
  have hVcont := positiveSheet_continuous N P
  have hVpos := positiveSheet_nonneg N P
  have hVint := positiveSheet_integrable N P
  have hVmellin (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
      (∫ t : PositiveAxis, (P.positiveSheet t : ℂ)*(t.val : ℂ)^s ∂positiveHaar) =
        (P.C₀ : ℂ)*(P.A₀ : ℂ)^s *
          (Complex.Gamma (s+5/6)*Complex.Gamma (s+7/6))^Fintype.card (InfinitePlace F) := by
    rw [C0_exact N P]
    exact (sheet_mellin N P s hs).2
  have hkernel : Continuous (fun t : PositiveAxis => P.kernel t.val) :=
    (thetaProfileGaussianKernel_continuousOn _ _ _ hC hA hr).comp_continuous
      continuous_subtype_val (fun t => t.property)
  have habs : Integrable (fun t : PositiveAxis => ‖P.kernel t.val‖ * P.positiveSheet (x*t)) positiveHaar := by
    obtain ⟨B, hB, hb⟩ := thetaProfileGaussianKernel_rpow_bound P.C₀ P.A₀
      (Fintype.card (InfinitePlace F)) hC hA hr 0
    have hc : Continuous (fun t : PositiveAxis => ‖P.kernel t.val‖ * P.positiveSheet (x*t)) :=
      hkernel.norm.mul (hVcont.comp (continuous_const.mul continuous_id))
    exact ((hVint.comp_mul_left x).const_mul B).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hVpos _))]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Packet.kernel] using hb t.val t.property) (hVpos _)))
  refine ⟨?_, ?_⟩
  · apply (integrable_norm_iff ?_).mp
    · convert habs using 1
      funext t
      change ‖P.kernel t.val * (P.positiveSheet (x*t) : ℂ)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hVpos _)]
    · exact (hkernel.mul (Complex.continuous_ofReal.comp
        (hVcont.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · let V := P.positiveSheet
    let C := P.C₀
    let A := P.A₀
    let r := Fintype.card (InfinitePlace F)
    let g := fun t : ℝ => Complex.exp (((t : ℂ)*Complex.I)^2) *
      thetaProfileReciprocalMellinFactor C A r ((t : ℂ)*Complex.I)
    have hg : Integrable g := by
      have hi := thetaProfileGaussianContour_integrable C A r hC hA hr 0 1 zero_lt_one
      change Integrable (fun t : ℝ => Complex.exp (((0 : ℂ)+t*Complex.I)^2) *
        thetaProfileReciprocalMellinFactor C A r ((0 : ℂ)+t*Complex.I) *
          (1 : ℂ)^((0 : ℂ)+t*Complex.I)) at hi
      simpa [g] using hi
    have hgc : Continuous g := by
      exact (Complex.continuous_exp.comp (by fun_prop)).mul
        ((thetaProfileReciprocalMellinFactor_differentiable C A r hC hA hr).continuous.comp (by fun_prop))
    let f : PositiveAxis → ℝ → ℂ := fun t u => g u * (t.val : ℂ)^((u : ℂ)*Complex.I) * (V (x*t) : ℂ)
    have hfcont : Continuous (Function.uncurry f) := by
      dsimp [f]
      apply Continuous.mul
      · apply Continuous.mul
        · exact hgc.comp continuous_snd
        · apply Continuous.cpow
          · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
          · fun_prop
          · intro p; exact Or.inl p.1.property
      · exact Complex.continuous_ofReal.comp (hVcont.comp (continuous_const.mul continuous_fst))
    have hprod : Integrable (Function.uncurry f) (positiveHaar.prod volume) := by
      apply ((hVint.comp_mul_left x).mul_prod hg.norm).mono' hfcont.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro p
      dsimp [Function.uncurry, f]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos p.1.property]
      simp [Complex.mul_re, Real.norm_eq_abs, abs_of_nonneg (hVpos _), V, mul_comm]
    have hinner (t : PositiveAxis) : P.kernel t.val * (V (x*t) : ℂ) =
        (1/(2*Real.pi) : ℝ) • ∫ u : ℝ, f t u := by
      unfold Packet.kernel thetaProfileGaussianKernel thetaProfileGaussianContour
      simp only [thetaProfileGaussianContourIntegrand, Complex.ofReal_zero, zero_add]
      rw [smul_mul_assoc, ← integral_mul_const]
    have hshift (u : ℝ) : (∫ t : PositiveAxis, f t u ∂positiveHaar) =
        Complex.exp (-(u : ℂ)^2) * Complex.exp (-(u : ℂ)*Complex.I*Real.log x.val) := by
      let s : ℂ := (u : ℂ)*Complex.I
      have hs : s.re = 0 := by simp [s, Complex.mul_re]
      have hxn : (x.val : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr x.property.ne'))
      have hchange : (∫ t : PositiveAxis, (t.val : ℂ)^s * (V (x*t) : ℂ) ∂positiveHaar) =
          (x.val : ℂ)^(-s) * ∫ t : PositiveAxis, (V t : ℂ)*(t.val : ℂ)^s ∂positiveHaar := by
        rw [← integral_mul_left_eq_self (fun t : PositiveAxis => (V t : ℂ)*(t.val : ℂ)^s) x,
          ← integral_const_mul]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        change _ = (x.val : ℂ)^(-s) * ((V (x*t) : ℂ)*((x.val*t.val : ℝ) : ℂ)^s)
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg x.property.le t.property.le,
          Complex.cpow_neg]
        calc
          _ = (((x.val : ℂ)^s)⁻¹ * (x.val : ℂ)^s) * ((t.val : ℂ)^s * (V (x*t) : ℂ)) := by
            rw [inv_mul_cancel₀ hxn, one_mul]
          _ = _ := by ring
      change (∫ t : PositiveAxis, g u * (t.val : ℂ)^s * (V (x*t) : ℂ) ∂positiveHaar) = _
      simp_rw [mul_assoc]
      rw [integral_const_mul, hchange, hVmellin s (by rw [hs]; norm_num)]
      have hcanc := reciprocal_cancel C A r hC hA s (by rw [hs]; norm_num)
      change (Complex.exp (s^2)*thetaProfileReciprocalMellinFactor C A r s) *
        ((x.val : ℂ)^(-s)*((C : ℂ)*(A : ℂ)^s *
          (Complex.Gamma (s+5/6)*Complex.Gamma (s+7/6))^r)) = _
      rw [show (Complex.exp (s^2)*thetaProfileReciprocalMellinFactor C A r s) *
          ((x.val : ℂ)^(-s)*((C : ℂ)*(A : ℂ)^s *
            (Complex.Gamma (s+5/6)*Complex.Gamma (s+7/6))^r)) =
          Complex.exp (s^2)*(x.val : ℂ)^(-s) *
            (thetaProfileReciprocalMellinFactor C A r s * ((C : ℂ)*(A : ℂ)^s *
              (Complex.Gamma (s+5/6)*Complex.Gamma (s+7/6))^r)) by ring,
        hcanc, mul_one, axis_cpow]
      congr 1
      · congr 1; simp [s, mul_pow, Complex.I_sq]
      · congr 1; dsimp [s]; ring
    change (∫ t : PositiveAxis, P.kernel t.val * (V (x*t) : ℂ) ∂positiveHaar) = _
    simp_rw [hinner]
    rw [integral_smul, integral_integral_swap hprod]
    simp_rw [hshift]
    rw [gaussian_contour, thetaReflectionGaussian_of_pos _ x.property]

theorem mellinGaussian (N : TraceHaarTransport R) (P : Packet R Q) : MellinGaussian R N Q P := by
  refine ⟨C0_exact N P, positive_sheet_integrable N P, C0_pos N P,
    fun s hs => (sheet_mellin N P s hs).1, ?_,
    fun x => (gaussian_smoothing N P x).1, fun x => (gaussian_smoothing N P x).2⟩
  intro s hs
  rw [C0_exact N P]
  exact (sheet_mellin N P s hs).2
end DedekindZetaZeroFree.GaussianSmoothing

end
