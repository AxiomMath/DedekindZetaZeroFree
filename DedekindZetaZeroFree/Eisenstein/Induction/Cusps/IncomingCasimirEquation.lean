module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.HolomorphicZeroModeTransitions

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPContFlatCuspCasimirSpecialization

def coordinateDirection (d : ℕ) (i : Fin d) (j : Fin 3) : KPArch.Space d :=
  Pi.single i (if j = 0 then (1, 0) else if j = 1 then (Complex.I, 0) else (0, 1))

def inverseMetricWeight (d : ℕ) (z : KPArch.Space d) (i : Fin d) (j : Fin 3) : ℝ :=
  if j = 2 then 1 else KPArch.height (z i) ^ 2

def Δloc {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (f : KPArch.Space d → V) (z : KPArch.Space d) : V :=
  -((KPArch.volumeDensity d z : ℂ)⁻¹ •
    ∑ i : Fin d, ∑ j : Fin 3,
      fderiv ℝ (fun y =>
        ((KPArch.volumeDensity d y * inverseMetricWeight d y i j : ℝ) : ℂ) •
          fderiv ℝ f y (coordinateDirection d i j)) z (coordinateDirection d i j))

private theorem volumeDensity_eq (d : ℕ) (y : KPArch.Space d) :
    KPArch.volumeDensity d y = Real.exp (-2 * ∑ k, (y k).2) := by
  unfold KPArch.volumeDensity KPArch.height
  have hfac : ∀ k : Fin d, (Real.exp (y k).2)⁻¹ ^ 2 = Real.exp (-2 * (y k).2) := by
    intro k
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hfac]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]

private theorem differentiableAt_volumeDensity (d : ℕ) (z : KPArch.Space d) :
    DifferentiableAt ℝ (KPArch.volumeDensity d) z := by
  rw [funext (volumeDensity_eq d)]
  fun_prop

private theorem differentiableAt_height_sq (d : ℕ) (i : Fin d) (z : KPArch.Space d) :
    DifferentiableAt ℝ (fun y : KPArch.Space d => KPArch.height (y i) ^ 2) z := by
  rw [show (fun y : KPArch.Space d => KPArch.height (y i) ^ 2) =
      fun y : KPArch.Space d => Real.exp (2 * (y i).2) from by
    funext y; simp only [KPArch.height]; rw [← Real.exp_nat_mul]; norm_num]
  fun_prop

private theorem fderiv_ofReal_apply {d : ℕ} {f : KPArch.Space d → ℝ} {z : KPArch.Space d}
    (hf : DifferentiableAt ℝ f z) (v : KPArch.Space d) :
    fderiv ℝ (fun y : KPArch.Space d => ((f y : ℝ) : ℂ)) z v = ((fderiv ℝ f z v : ℝ) : ℂ) := by
  rw [show (fun y : KPArch.Space d => ((f y : ℝ) : ℂ)) =
      (Complex.ofRealCLM : ℝ → ℂ) ∘ f from rfl]
  rw [fderiv_comp (f := f) (g := (Complex.ofRealCLM : ℝ → ℂ)) (x := z)
      (Complex.ofRealCLM.differentiableAt) hf]
  rw [ContinuousLinearMap.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private theorem fderiv_volumeDensity_real (d : ℕ) (z v : KPArch.Space d) :
    fderiv ℝ (KPArch.volumeDensity d) z v = -2 * KPArch.volumeDensity d z * (∑ k, (v k).2) := by
  have hV : KPArch.volumeDensity d = fun y : KPArch.Space d => Real.exp (-2 * ∑ k, (y k).2) :=
    funext (volumeDensity_eq d)
  rw [hV]
  have hB : HasFDerivAt (fun y : KPArch.Space d => -2 * ∑ k : Fin d, (y k).2)
      ((-2 : ℝ) • (∑ k : Fin d, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp
        (ContinuousLinearMap.proj k))) z := by
    fun_prop
  rw [hB.exp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, sum_apply]
  simp
  ring

private theorem fderiv_volumeDensity_apply (d : ℕ) (z v : KPArch.Space d) :
    fderiv ℝ (fun y : KPArch.Space d => ((KPArch.volumeDensity d y : ℝ) : ℂ)) z v =
      -2 * (KPArch.volumeDensity d z : ℂ) * (((∑ k, (v k).2) : ℝ) : ℂ) := by
  rw [fderiv_ofReal_apply (differentiableAt_volumeDensity d z) v, fderiv_volumeDensity_real]
  push_cast
  ring

private theorem fderiv_height_sq_real (d : ℕ) (i : Fin d) (z v : KPArch.Space d) :
    fderiv ℝ (fun y : KPArch.Space d => KPArch.height (y i) ^ 2) z v
      = Real.exp (2 * (z i).2) * (2 * (v i).2) := by
  have hK : (fun y : KPArch.Space d => KPArch.height (y i) ^ 2) =
      fun y : KPArch.Space d => Real.exp (2 * (y i).2) := by
    funext y; simp only [KPArch.height]; rw [← Real.exp_nat_mul]; norm_num
  rw [hK]
  have hB : HasFDerivAt (fun y : KPArch.Space d => 2 * (y i).2)
      ((2 : ℝ) • ((ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj i))) z := by
    fun_prop
  rw [hB.exp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  simp

private theorem sum_coordinateDirection (d : ℕ) (i : Fin d) (j : Fin 3) :
    (∑ k : Fin d, (coordinateDirection d i j k).2) = if j = 2 then 1 else 0 := by
  rw [Finset.sum_eq_single i]
  · rw [coordinateDirection, Pi.single_eq_same]
    fin_cases j <;> norm_num
  · intro k _ hk
    rw [coordinateDirection, Pi.single_eq_of_ne hk]
    rfl
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem coordinateDirection_apply_self (d : ℕ) (i : Fin d) (j : Fin 3) :
    (coordinateDirection d i j i).2 = if j = 2 then 1 else 0 := by
  rw [coordinateDirection, Pi.single_eq_same]
  fin_cases j <;> norm_num

private theorem differentiableAt_VK_real (d : ℕ) (i : Fin d) (z : KPArch.Space d) :
    DifferentiableAt ℝ (fun y : KPArch.Space d =>
      KPArch.volumeDensity d y * KPArch.height (y i) ^ 2) z :=
  (differentiableAt_volumeDensity d z).mul (differentiableAt_height_sq d i z)

private theorem differentiableAt_VK (d : ℕ) (i : Fin d) (z : KPArch.Space d) :
    DifferentiableAt ℝ (fun y : KPArch.Space d =>
      ((KPArch.volumeDensity d y * KPArch.height (y i) ^ 2 : ℝ) : ℂ)) z :=
  Complex.ofRealCLM.differentiableAt.comp z
    ((differentiableAt_volumeDensity d z).mul (differentiableAt_height_sq d i z))

private theorem differentiableAt_V_one (d : ℕ) (z : KPArch.Space d) :
    DifferentiableAt ℝ (fun y : KPArch.Space d => ((KPArch.volumeDensity d y * 1 : ℝ) : ℂ)) z := by
  have h : (fun y : KPArch.Space d => ((KPArch.volumeDensity d y * 1 : ℝ) : ℂ)) =
      fun y : KPArch.Space d => ((KPArch.volumeDensity d y : ℝ) : ℂ) := by
    funext y; simp
  rw [h]
  exact Complex.ofRealCLM.differentiableAt.comp z (differentiableAt_volumeDensity d z)

private theorem fderiv_VK_coordinateDirection (d : ℕ) (i : Fin d) (j : Fin 3)
    (z : KPArch.Space d) :
    fderiv ℝ (fun y : KPArch.Space d =>
      ((KPArch.volumeDensity d y * KPArch.height (y i) ^ 2 : ℝ) : ℂ)) z
      (coordinateDirection d i j) = 0 := by
  rw [fderiv_ofReal_apply (differentiableAt_VK_real d i z) (coordinateDirection d i j)]
  rw [show (fun y : KPArch.Space d => KPArch.volumeDensity d y * KPArch.height (y i) ^ 2)
      = KPArch.volumeDensity d * fun y : KPArch.Space d => KPArch.height (y i) ^ 2 from rfl]
  rw [fderiv_mul (differentiableAt_volumeDensity d z) (differentiableAt_height_sq d i z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [fderiv_volumeDensity_real, fderiv_height_sq_real, sum_coordinateDirection,
    coordinateDirection_apply_self]
  rw [show Real.exp (2 * (z i).2) = KPArch.height (z i) ^ 2 from by
    rw [KPArch.height, ← Real.exp_nat_mul]; norm_num]
  rw [Complex.ofReal_eq_zero]
  ring

private theorem fderiv_V_one_coordinateDirection (d : ℕ) (i : Fin d) (z : KPArch.Space d) :
    fderiv ℝ (fun y : KPArch.Space d => ((KPArch.volumeDensity d y * 1 : ℝ) : ℂ)) z
      (coordinateDirection d i 2) = -2 * (KPArch.volumeDensity d z : ℂ) := by
  have h : (fun y : KPArch.Space d => ((KPArch.volumeDensity d y * 1 : ℝ) : ℂ)) =
      fun y : KPArch.Space d => ((KPArch.volumeDensity d y : ℝ) : ℂ) := by
    funext y; simp
  rw [h, fderiv_volumeDensity_apply, sum_coordinateDirection]
  norm_num

private theorem fderiv_smul_apply' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {d : ℕ} {c : KPArch.Space d → ℂ} {g : KPArch.Space d → V} {z : KPArch.Space d}
    (hc : DifferentiableAt ℝ c z) (hg : DifferentiableAt ℝ g z) (v : KPArch.Space d) :
    fderiv ℝ (fun y => c y • g y) z v = c z • (fderiv ℝ g z v) + (fderiv ℝ c z v) • g z := by
  rw [fderiv_fun_smul hc hg]
  simp

private theorem differentiableAt_fderiv_apply {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {d : ℕ} {f : KPArch.Space d → V} (hf : ContDiff ℝ 2 f)
    (z v : KPArch.Space d) : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) z := by
  fun_prop

theorem Δloc_coordinate_expression {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (d : ℕ) (f : KPArch.Space d → V)
    (hf : ContDiff ℝ 2 f) (z : KPArch.Space d) :
    Δloc d f z = ∑ i : Fin d,
      (-(fderiv ℝ (fun y => fderiv ℝ f y (coordinateDirection d i 2)) z
          (coordinateDirection d i 2)) +
        (2 : ℂ) • fderiv ℝ f z (coordinateDirection d i 2) -
        ((KPArch.height (z i) ^ 2 : ℝ) : ℂ) •
          (fderiv ℝ (fun y => fderiv ℝ f y (coordinateDirection d i 0)) z
            (coordinateDirection d i 0) +
           fderiv ℝ (fun y => fderiv ℝ f y (coordinateDirection d i 1)) z
            (coordinateDirection d i 1))) := by
  rw [Δloc]
  simp only [inverseMetricWeight]
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_three]
  simp only [if_neg (show ¬((0 : Fin 3) = 2) from by decide),
    if_neg (show ¬((1 : Fin 3) = 2) from by decide), if_true]
  have hG0 : fderiv ℝ (fun y : KPArch.Space d =>
      ((KPArch.volumeDensity d y * KPArch.height (y i) ^ 2 : ℝ) : ℂ) •
        (fderiv ℝ f y) (coordinateDirection d i 0)) z (coordinateDirection d i 0)
      = ((KPArch.volumeDensity d z * KPArch.height (z i) ^ 2 : ℝ) : ℂ) •
        fderiv ℝ (fun y => (fderiv ℝ f y) (coordinateDirection d i 0)) z
          (coordinateDirection d i 0) := by
    rw [fderiv_smul_apply' (differentiableAt_VK d i z)
      (differentiableAt_fderiv_apply hf z (coordinateDirection d i 0))
      (coordinateDirection d i 0)]
    rw [fderiv_VK_coordinateDirection]
    simp
  have hG1 : fderiv ℝ (fun y : KPArch.Space d =>
      ((KPArch.volumeDensity d y * KPArch.height (y i) ^ 2 : ℝ) : ℂ) •
        (fderiv ℝ f y) (coordinateDirection d i 1)) z (coordinateDirection d i 1)
      = ((KPArch.volumeDensity d z * KPArch.height (z i) ^ 2 : ℝ) : ℂ) •
        fderiv ℝ (fun y => (fderiv ℝ f y) (coordinateDirection d i 1)) z
          (coordinateDirection d i 1) := by
    rw [fderiv_smul_apply' (differentiableAt_VK d i z)
      (differentiableAt_fderiv_apply hf z (coordinateDirection d i 1))
      (coordinateDirection d i 1)]
    rw [fderiv_VK_coordinateDirection]
    simp
  have hG2 : fderiv ℝ (fun y : KPArch.Space d =>
      ((KPArch.volumeDensity d y * 1 : ℝ) : ℂ) •
        (fderiv ℝ f y) (coordinateDirection d i 2)) z (coordinateDirection d i 2)
      = (KPArch.volumeDensity d z : ℂ) •
          fderiv ℝ (fun y => (fderiv ℝ f y) (coordinateDirection d i 2)) z
            (coordinateDirection d i 2) +
        (-2 * (KPArch.volumeDensity d z : ℂ)) • (fderiv ℝ f z) (coordinateDirection d i 2) := by
    rw [fderiv_smul_apply' (differentiableAt_V_one d z)
      (differentiableAt_fderiv_apply hf z (coordinateDirection d i 2))
      (coordinateDirection d i 2)]
    rw [fderiv_V_one_coordinateDirection]
    simp
  rw [hG0, hG1, hG2]
  have hVz : (KPArch.volumeDensity d z : ℂ) ≠ 0 := by
    rw [volumeDensity_eq]
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hc1 : (KPArch.volumeDensity d z : ℂ)⁻¹ *
      ((KPArch.volumeDensity d z * KPArch.height (z i) ^ 2 : ℝ) : ℂ)
      = ((KPArch.height (z i) ^ 2 : ℝ) : ℂ) := by
    rw [show ((KPArch.volumeDensity d z * KPArch.height (z i) ^ 2 : ℝ) : ℂ)
        = (KPArch.volumeDensity d z : ℂ) * ((KPArch.height (z i) ^ 2 : ℝ) : ℂ) from by
      push_cast; ring]
    rw [← mul_assoc, inv_mul_cancel₀ hVz, one_mul]
  have hc3 : (KPArch.volumeDensity d z : ℂ)⁻¹ * (-2 * (KPArch.volumeDensity d z : ℂ)) = -2 := by
    rw [show (KPArch.volumeDensity d z : ℂ)⁻¹ * (-2 * (KPArch.volumeDensity d z : ℂ))
        = -2 * ((KPArch.volumeDensity d z : ℂ)⁻¹ * (KPArch.volumeDensity d z : ℂ)) from by ring]
    rw [inv_mul_cancel₀ hVz, mul_one]
  simp only [smul_add, smul_smul]
  rw [hc1, hc3, inv_mul_cancel₀ hVz, one_smul, neg_smul]
  abel

 def meanCLM (d : ℕ) : KPArch.Space d →L[ℝ] ℝ :=
  (d : ℝ)⁻¹ • ∑ k : Fin d, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj k)
private theorem meanCLM_apply (d : ℕ) (z : KPArch.Space d) :
    meanCLM d z = KPCuspLogShape.meanHeight d z := by
  simp [meanCLM, KPCuspLogShape.meanHeight, div_eq_inv_mul]
private theorem meanCLM_dir (d : ℕ) (i : Fin d) (j : Fin 3) :
    meanCLM d (coordinateDirection d i j) = if j = 2 then (d : ℝ)⁻¹ else 0 := by
  simp only [meanCLM, ContinuousLinearMap.smul_apply, sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · simp [coordinateDirection, Pi.single_eq_same]
    fin_cases j <;> norm_num
  · intro k _ hk
    simp [coordinateDirection, Pi.single_eq_of_ne hk]
  · simp
private theorem exp_mean_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (c : ℂ) (b : V) (z w : KPArch.Space d) :
    fderiv ℝ (fun y => Complex.exp (c * (meanCLM d y : ℂ)) • b) z w =
      (c * (meanCLM d w : ℂ) * Complex.exp (c * (meanCLM d z : ℂ))) • b := by
  have hm := (Complex.ofRealCLM.comp (meanCLM d)).hasFDerivAt (x := z)
  have he := (hm.const_smul c).cexp.smul_const b
  have he' : HasFDerivAt (fun y => Complex.exp (c * (meanCLM d y : ℂ)) • b)
      ((Complex.exp (c * (meanCLM d z : ℂ)) • c • (Complex.ofRealCLM.comp (meanCLM d))).smulRight b) z := by
    simpa [ContinuousLinearMap.comp_apply, smul_eq_mul] using he
  rw [he'.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 1
  ring
private theorem exp_mean_second {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (c : ℂ) (b : V) (z w : KPArch.Space d) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => Complex.exp (c * (meanCLM d x : ℂ)) • b) y w) z w =
      ((c * (meanCLM d w : ℂ)) ^ 2 * Complex.exp (c * (meanCLM d z : ℂ))) • b := by
  have hfun : (fun y => fderiv ℝ (fun x => Complex.exp (c * (meanCLM d x : ℂ)) • b) y w) =
      fun y => Complex.exp (c * (meanCLM d y : ℂ)) • ((c * (meanCLM d w : ℂ)) • b) := by
    funext y
    rw [exp_mean_fderiv]
    simp only [smul_smul]
    congr 1
    ring
  rw [hfun, exp_mean_fderiv, smul_smul]
  congr 1
  ring
private theorem exp_mean_laplacian {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (d : ℕ) (hd : 0 < d) (s : ℂ) (b : V) (z : KPArch.Space d) :
    Δloc d (fun y => KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d y) • b) z =
      KPContinuation.spectralCoordinate (d : ℤ) s •
        (KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d z) • b) := by
  have hf : ContDiff ℝ 2 (fun y : KPArch.Space d =>
      KPIncomingCasimir.heightFactor d s (KPCuspLogShape.meanHeight d y) • b) := by
    simp only [KPIncomingCasimir.heightFactor, ← meanCLM_apply]
    apply ContDiff.smul_const
    have hm : ContDiff ℝ 2 (fun y => (meanCLM d y : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (meanCLM d).contDiff
    exact ((contDiff_const.mul hm).cexp)
  rw [Δloc_coordinate_expression d _ hf]
  simp only [KPIncomingCasimir.heightFactor, ← meanCLM_apply]
  simp only [exp_mean_second]
  simp only [exp_mean_fderiv, meanCLM_dir]
  simp only [ite_true, show ¬ ((0 : Fin 3) = 2) from by decide,
    show ¬ ((1 : Fin 3) = 2) from by decide, ite_false,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_smul,
    add_zero, sub_zero]
  simp only [smul_zero, sub_zero, ← neg_smul, smul_smul, ← add_smul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  congr 1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [KPContinuation.spectralCoordinate, Int.cast_natCast]
  field_simp
  ring

open KPContFlatCuspIncomingEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U)
variable (a : Cusps F ζ hζ C R P H U)

theorem dimension (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) :
    KPCuspLogShape.dimension F = Module.finrank ℚ F / 2 ∧
    0 < Module.finrank ℚ F / 2 := by
  have h := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
  exact ⟨h.2.1, by rw [← h.2.1]; exact h.2.2⟩

def wave (s : ℂ) (v : S) (p : KPCuspCharts.Coordinates F) :
    ZeroFiber F ζ hζ C R P H U a :=
  W F ζ hζ C R P H U a ι s v p.2 p.1.2

def incomingOnArch (s : ℂ) (v : S)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) : ZeroFiber F ζ hζ C R P H U a :=
  wave F ζ hζ C R P H U ι a s v
    ((KPCuspCharts.toArchHomeomorph F
      (KPCuspLogShape.dimension_pos F H.totallyComplex)).symm z)

private theorem incoming_height_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S) :
    incomingOnArch F ζ hζ C R P H U ι a s v =
      fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
        KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s
          (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) •
          (b F ζ hζ C R P H U a ι s hs v).val 0 := by
  funext z
  simp only [incomingOnArch, wave]
  rw [incoming_formula F ζ hζ C R P H U a ι s hs v]
  have h2 : ((KPCuspCharts.toArchHomeomorph F
      (KPCuspLogShape.dimension_pos F H.totallyComplex)).symm z).2 =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z := rfl
  rw [h2]
  rw [b_formula F ζ hζ C R P H U a ι s hs v, b_formula F ζ hζ C R P H U a ι s hs v]

private theorem incoming_scalar_eigen (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (q : KernelTorus F ζ hζ C R P H U a)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    Δloc (KPCuspLogShape.dimension F)
      (fun y => (incomingOnArch F ζ hζ C R P H U ι a s v y).val q) z =
        KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
          (incomingOnArch F ζ hζ C R P H U ι a s v z).val q := by
  rw [incoming_height_formula F ζ hζ C R P H U ι a s hs v]
  change Δloc (KPCuspLogShape.dimension F)
      (fun y => KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s
        (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) y) •
        ((b F ζ hζ C R P H U a ι s hs v).val 0).val q) z = _
  rw [← (dimension F ζ hζ).1]
  exact exp_mean_laplacian _ (KPCuspLogShape.dimension_pos F H.totallyComplex) _ _ _

private theorem wave_scalar_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (shape : KPCuspCharts.Shape F) (q : KernelTorus F ζ hζ C R P H U a) :
    (fun t => (W F ζ hζ C R P H U a ι s v t shape).val q) =
      fun t => KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t *
        ((b F ζ hζ C R P H U a ι s hs v).val 0).val q := by
  funext t
  rw [incoming_formula F ζ hζ C R P H U a ι s hs v]
  rw [b_formula F ζ hζ C R P H U a ι s hs v, b_formula F ζ hζ C R P H U a ι s hs v]
  rfl

theorem metric_radial_scalar (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (p : KPCuspCharts.Coordinates F) (q : KernelTorus F ζ hζ C R P H U a) :
    Δloc (KPCuspLogShape.dimension F)
      (fun z => (incomingOnArch F ζ hζ C R P H U ι a s v z).val q)
      (KPCuspCharts.toArch F p) =
        KPIncomingCasimir.radialLaplacian (Module.finrank ℚ F / 2)
          (fun t => (W F ζ hζ C R P H U a ι s v t p.1.2).val q) p.2 := by
  rw [incoming_scalar_eigen F ζ hζ C R P H U ι a s hs v]
  rw [wave_scalar_formula F ζ hζ C R P H U ι a s hs v]
  rw [KPIncomingCasimir.heightFactor_eigenfunction _ (dimension F ζ hζ).2]
  rw [incoming_height_formula F ζ hζ C R P H U ι a s hs v]
  dsimp only
  rw [KPCuspCharts.toArch_meanHeight F (KPCuspLogShape.dimension_pos F H.totallyComplex)]
  rfl

theorem incoming_casimir_scalar (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (q : KernelTorus F ζ hζ C R P H U a)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    Δloc (KPCuspLogShape.dimension F)
      (fun y => (incomingOnArch F ζ hζ C R P H U ι a s v y).val q) z =
        KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
          (incomingOnArch F ζ hζ C R P H U ι a s v z).val q := by
  exact incoming_scalar_eigen F ζ hζ C R P H U ι a s hs v q z

end DedekindZetaZeroFree.KPContFlatCuspCasimirSpecialization

namespace DedekindZetaZeroFree

open KPContFlatCuspIncomingEvaluation KPContFlatCuspCasimirSpecialization

end DedekindZetaZeroFree

end
