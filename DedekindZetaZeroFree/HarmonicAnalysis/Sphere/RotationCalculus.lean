module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalFractionalIntegrals.RotationDerivatives

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open MeasureTheory
open scoped BigOperators

noncomputable def radialExtension (F : Sphere → ℂ) (x : Ambient) : ℂ :=
  if hx : x ≠ 0 then
    F ⟨‖x‖⁻¹ • x, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  else 0

def IsSphereSmooth (F : Sphere → ℂ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (radialExtension F) {x : Ambient | x ≠ 0}

noncomputable def rotationVector (i : Fin 3) (x : Ambient) : Ambient :=
  WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i + 1 then -x (i + 2) else if j = i + 2 then x (i + 1) else 0)

noncomputable def rotationDeriv (i : Fin 3) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  fderiv ℝ (radialExtension F) (x : Ambient) (rotationVector i x)

noncomputable def rotationWord : List (Fin 3) → (Sphere → ℂ) → (Sphere → ℂ)
  | [], F => F
  | i :: w, F => rotationDeriv i (rotationWord w F)

noncomputable def rotationSup (n : ℕ) (F : Sphere → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ w : List (Fin 3), w.length ≤ n ∧
    ∃ x : Sphere, r = ‖rotationWord w F x‖}

noncomputable def positiveLaplacian (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  -∑ i : Fin 3, rotationDeriv i (rotationDeriv i F) x

private theorem sphere_norm (x : Sphere) : ‖(x : Ambient)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property
private theorem sphere_ne_zero (x : Sphere) : (x : Ambient) ≠ 0 := by
  intro h
  have := sphere_norm x
  simp [h] at this
theorem radialExtension_sphere (F : Sphere → ℂ) (x : Sphere) : radialExtension F x = F x := by
  simp only [radialExtension, dif_pos (sphere_ne_zero x), sphere_norm, inv_one, one_smul]
private theorem puncture_open : IsOpen {x : Ambient | x ≠ 0} := isOpen_ne
private theorem normalize_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ambient => ‖x‖⁻¹ • x) {x | x ≠ 0} := by
  intro x hx
  exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).contDiffWithinAt
private theorem restrict_smooth (G : Ambient → ℂ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G {x | x ≠ 0}) :
    IsSphereSmooth (fun x : Sphere => G x) := by
  have h := hG.comp normalize_smooth (fun x hx => by
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx)
  apply h.congr
  intro x hx
  simp only [radialExtension, dif_pos (show x ≠ 0 from hx), Function.comp_apply]
theorem rotationVector_smooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (rotationVector i) := by
  unfold rotationVector
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  simp only [rotationVector]
  split_ifs
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 2)).contDiff.neg
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 1)).contDiff
  · exact contDiff_const
theorem rotationDeriv_smooth (i : Fin 3) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    IsSphereSmooth (rotationDeriv i F) := by
  unfold rotationDeriv
  apply restrict_smooth (fun x : Ambient => fderiv ℝ (radialExtension F) x (rotationVector i x))
  exact (hF.fderiv_of_isOpen puncture_open (by simp)).clm_apply (rotationVector_smooth i).contDiffOn
theorem rotationWord_smooth (w : List (Fin 3)) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    IsSphereSmooth (rotationWord w F) := by
  induction w with
  | nil => exact hF
  | cons i w ih => exact rotationDeriv_smooth i ih
theorem IsSphereSmooth.continuous {F : Sphere → ℂ} (hF : IsSphereSmooth F) : Continuous F := by
  have h : Continuous (fun x : Sphere => radialExtension F x) :=
    hF.continuousOn.comp_continuous continuous_subtype_val (fun x => sphere_ne_zero x)
  simpa only [radialExtension_sphere] using h
theorem IsSphereSmooth.add {F G : Sphere → ℂ} (hF : IsSphereSmooth F) (hG : IsSphereSmooth G) :
    IsSphereSmooth (fun x => F x + G x) := by
  apply (ContDiffOn.add hF hG).congr
  intro x hx
  simp only [radialExtension, dif_pos (show x ≠ 0 from hx), Function.comp_apply]
theorem IsSphereSmooth.neg {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    IsSphereSmooth (fun x => -F x) := by
  apply (ContDiffOn.neg hF).congr
  intro x hx
  simp only [radialExtension, dif_pos (show x ≠ 0 from hx), Function.comp_apply]
theorem IsSphereSmooth.const_mul (c : ℂ) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    IsSphereSmooth (fun x => c * F x) := by
  apply ((contDiffOn_const (c := c)).mul hF).congr
  intro x hx
  simp only [radialExtension, dif_pos (show x ≠ 0 from hx), Function.comp_apply]
theorem IsSphereSmooth.sum {ι : Type*} (s : Finset ι) (F : ι → Sphere → ℂ)
    (hF : ∀ i ∈ s, IsSphereSmooth (F i)) : IsSphereSmooth (fun x => ∑ i ∈ s, F i x) := by
  classical
  apply (ContDiffOn.sum (fun i hi => hF i hi)).congr
  intro x hx
  simp only [radialExtension, dif_pos (show x ≠ 0 from hx)]
theorem positiveLaplacian_smooth {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    IsSphereSmooth (positiveLaplacian F) := by
  apply IsSphereSmooth.neg
  exact IsSphereSmooth.sum Finset.univ _ (fun i _ => rotationDeriv_smooth i (rotationDeriv_smooth i hF))
theorem rotationSup_nonneg (n : ℕ) (F : Sphere → ℂ) : 0 ≤ rotationSup n F := by
  apply Real.sSup_nonneg
  rintro r ⟨w, hw, x, rfl⟩
  exact norm_nonneg _
theorem rotationSup_bddAbove (n : ℕ) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    BddAbove {r : ℝ | ∃ w : List (Fin 3), w.length ≤ n ∧ ∃ x : Sphere, r = ‖rotationWord w F x‖} := by
  have hc : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
  have hb : BddAbove (⋃ w ∈ {w : List (Fin 3) | w.length ≤ n}, Set.range (fun x : Sphere => ‖rotationWord w F x‖)) := by
    apply (List.finite_length_le (Fin 3) n).bddAbove_biUnion.mpr
    intro w hw
    simpa only [Set.image_univ] using isCompact_univ.bddAbove_image (IsSphereSmooth.continuous (rotationWord_smooth w hF)).norm.continuousOn
  apply hb.mono
  rintro r ⟨w, hw, x, rfl⟩
  exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, Set.mem_range_self x⟩⟩
theorem rotationWord_norm_le_rotationSup {F : Sphere → ℂ} (hF : IsSphereSmooth F) (w : List (Fin 3))
    {n : ℕ} (hw : w.length ≤ n) (x : Sphere) : ‖rotationWord w F x‖ ≤ rotationSup n F := by
  exact le_csSup (rotationSup_bddAbove n hF) ⟨w, hw, x, rfl⟩
theorem radialExtension_add (F G : Sphere → ℂ) :
    radialExtension (fun x => F x + G x) = fun x => radialExtension F x + radialExtension G x := by
  funext x
  unfold radialExtension
  split_ifs <;> simp
theorem radialExtension_const_mul (c : ℂ) (F : Sphere → ℂ) :
    radialExtension (fun x => c * F x) = fun x => c * radialExtension F x := by
  funext x
  unfold radialExtension
  split_ifs <;> simp
theorem radialExtension_neg (F : Sphere → ℂ) :
    radialExtension (fun x => -F x) = fun x => -radialExtension F x := by
  funext x
  unfold radialExtension
  split_ifs <;> simp
private theorem radial_diff_at {F : Sphere → ℂ} (hF : IsSphereSmooth F) (x : Sphere) :
    DifferentiableAt ℝ (radialExtension F) (x : Ambient) :=
  ((hF x (sphere_ne_zero x)).contDiffAt (puncture_open.mem_nhds (sphere_ne_zero x))).differentiableAt (by simp)
theorem rotationDeriv_add (i : Fin 3) {F G : Sphere → ℂ}
    (hF : IsSphereSmooth F) (hG : IsSphereSmooth G) :
    rotationDeriv i (fun x => F x + G x) = fun x => rotationDeriv i F x + rotationDeriv i G x := by
  funext x
  simp only [rotationDeriv, radialExtension_add, fderiv_fun_add (radial_diff_at hF x) (radial_diff_at hG x), ContinuousLinearMap.add_apply]
theorem rotationDeriv_const_mul (i : Fin 3) (c : ℂ) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    rotationDeriv i (fun x => c * F x) = fun x => c * rotationDeriv i F x := by
  funext x
  simp only [rotationDeriv, radialExtension_const_mul, fderiv_const_mul (radial_diff_at hF x), ContinuousLinearMap.smul_apply, smul_eq_mul]
theorem rotationDeriv_neg (i : Fin 3) (F : Sphere → ℂ) :
    rotationDeriv i (fun x => -F x) = fun x => -rotationDeriv i F x := by
  funext x
  simp only [rotationDeriv, radialExtension_neg, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
theorem rotationWord_add (w : List (Fin 3)) {F G : Sphere → ℂ}
    (hF : IsSphereSmooth F) (hG : IsSphereSmooth G) :
    rotationWord w (fun x => F x + G x) = fun x => rotationWord w F x + rotationWord w G x := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [rotationWord, ih, rotationDeriv_add i (rotationWord_smooth w hF) (rotationWord_smooth w hG)]
theorem rotationWord_const_mul (w : List (Fin 3)) (c : ℂ) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    rotationWord w (fun x => c * F x) = fun x => c * rotationWord w F x := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [rotationWord, ih, rotationDeriv_const_mul i c (rotationWord_smooth w hF)]
theorem rotationWord_neg (w : List (Fin 3)) (F : Sphere → ℂ) :
    rotationWord w (fun x => -F x) = fun x => -rotationWord w F x := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [rotationWord, ih, rotationDeriv_neg]
theorem rotationWord_sum {ι : Type*} (s : Finset ι) (w : List (Fin 3)) (F : ι → Sphere → ℂ)
    (hF : ∀ i ∈ s, IsSphereSmooth (F i)) :
    rotationWord w (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, rotationWord w (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    induction w with
    | nil => simp [rotationWord]
    | cons i w ih =>
      simp only [Finset.sum_empty] at ih ⊢
      simp only [rotationWord, ih, rotationDeriv]
      have hz : radialExtension (fun _ : Sphere => (0 : ℂ)) = fun _ => 0 := by
        funext x; simp [radialExtension]
      funext x
      unfold rotationDeriv
      rw [hz]
      simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rotationWord_add w (hF a (Finset.mem_insert_self a s)) (IsSphereSmooth.sum s F (fun i hi => hF i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]
theorem rotationWord_append (w v : List (Fin 3)) (F : Sphere → ℂ) :
    rotationWord (w ++ v) F = rotationWord w (rotationWord v F) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, rotationWord, ih]
theorem rotationWord_positiveLaplacian (w : List (Fin 3)) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    rotationWord w (positiveLaplacian F) = fun x => -∑ i : Fin 3, rotationWord (w ++ [i,i]) F x := by
  unfold positiveLaplacian
  rw [rotationWord_neg, rotationWord_sum Finset.univ w _ (fun i _ => rotationDeriv_smooth i (rotationDeriv_smooth i hF))]
  simp only [rotationWord_append, rotationWord]

 theorem fractionalIntegral_integrable (α : ℝ) (hα : 0 < α)
    {F : Sphere → ℂ} (hF : IsSphereSmooth F) (x : Sphere) :
    Integrable (fun y => (fractionalKernel α x y : ℂ) * F y) sphereArea := by
  have hK := (fractionalKernel_mass α hα).2 x
  apply hK.1.ofReal.mul_bdd hF.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => rotationWord_norm_le_rotationSup hF [] (n := 0) (by simp) y)

 theorem rotationSup_const_mul_le (n : ℕ) (c : ℂ) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    rotationSup n (fun x => c * F x) ≤ ‖c‖ * rotationSup n F := by
  apply Real.sSup_le _ (mul_nonneg (norm_nonneg c) (rotationSup_nonneg n F))
  rintro r ⟨w, hw, x, rfl⟩
  rw [rotationWord_const_mul w c hF, norm_mul]
  exact mul_le_mul_of_nonneg_left (rotationWord_norm_le_rotationSup hF w hw x) (norm_nonneg c)
 theorem rotationSup_mono {n m : ℕ} (hnm : n ≤ m) {F : Sphere → ℂ} (hF : IsSphereSmooth F) :
    rotationSup n F ≤ rotationSup m F := by
  apply Real.sSup_le _ (rotationSup_nonneg m F)
  rintro r ⟨w, hw, x, rfl⟩
  exact rotationWord_norm_le_rotationSup hF w (hw.trans hnm) x

 theorem fractionalIntegral_add (α : ℝ) (hα : 0 < α)
    {F G : Sphere → ℂ} (hF : IsSphereSmooth F) (hG : IsSphereSmooth G) :
    fractionalIntegral α (fun x => F x + G x) =
      fun x => fractionalIntegral α F x + fractionalIntegral α G x := by
  funext x
  unfold fractionalIntegral
  simp only [mul_add]
  exact integral_add (fractionalIntegral_integrable α hα hF x) (fractionalIntegral_integrable α hα hG x)
 theorem fractionalIntegral_const_mul (α : ℝ) (c : ℂ) (F : Sphere → ℂ) :
    fractionalIntegral α (fun x => c * F x) = fun x => c * fractionalIntegral α F x := by
  funext x
  unfold fractionalIntegral
  simp only [← mul_assoc]
  conv_lhs => arg 2; ext y; rw [mul_comm _ c, mul_assoc]
  exact integral_const_mul c _
 theorem fractionalIntegral_neg (α : ℝ) (F : Sphere → ℂ) :
    fractionalIntegral α (fun x => -F x) = fun x => -fractionalIntegral α F x := by
  funext x
  simp only [fractionalIntegral, mul_neg, integral_neg]
 theorem fractionalIntegral_norm_le_of_bound (α : ℝ) (hα : 0 < α)
    (F : Sphere → ℂ) (C : ℝ) (hC : ∀ y, ‖F y‖ ≤ C) (x : Sphere) :
    ‖fractionalIntegral α F x‖ ≤ C := by
  have hK := (fractionalKernel_mass α hα).2 x
  calc
    _ ≤ ∫ y, fractionalKernel α x y * C ∂sphereArea := by
      apply norm_integral_le_of_norm_le (hK.1.mul_const _) (Filter.Eventually.of_forall _)
      intro y
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK.2.1 y)]
      exact mul_le_mul_of_nonneg_left (hC y) (hK.2.1 y)
    _ = _ := by rw [integral_mul_const, hK.2.2, one_mul]
 theorem fractionalIntegral_rotationSup_of_commutes (α : ℝ) (hα : 0 < α)
    {F : Sphere → ℂ} (hF : IsSphereSmooth F)
    (hcomm : ∀ w : List (Fin 3), rotationWord w (fractionalIntegral α F) =
      fractionalIntegral α (rotationWord w F)) (n : ℕ) :
    rotationSup n (fractionalIntegral α F) ≤ rotationSup n F := by
  apply Real.sSup_le _ (rotationSup_nonneg n F)
  rintro r ⟨w, hw, x, rfl⟩
  rw [hcomm]
  exact fractionalIntegral_norm_le_of_bound α hα _ _
    (fun y => rotationWord_norm_le_rotationSup hF w hw y) x

 theorem fractionalIntegral_rotationWord_of_deriv (α : ℝ)
    (hcomm : ∀ (i : Fin 3) (F : Sphere → ℂ), IsSphereSmooth F →
      rotationDeriv i (fractionalIntegral α F) = fractionalIntegral α (rotationDeriv i F))
    {F : Sphere → ℂ} (hF : IsSphereSmooth F) (w : List (Fin 3)) :
    rotationWord w (fractionalIntegral α F) = fractionalIntegral α (rotationWord w F) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [rotationWord, ih]
    exact hcomm i _ (rotationWord_smooth w hF)

theorem fractionalIntegral_rotation (α : ℝ) (hα : 0 < α)
    (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    (∀ x : Sphere, Integrable
      (fun y => (fractionalKernel α x y : ℂ) * F y) sphereArea) ∧
    IsSphereSmooth (fractionalIntegral α F) ∧
    (∀ w : List (Fin 3), rotationWord w (fractionalIntegral α F) =
      fractionalIntegral α (rotationWord w F)) ∧
    (∀ n : ℕ, rotationSup n (fractionalIntegral α F) ≤ rotationSup n F) := by
  have hsmooth : IsSphereSmooth (fractionalIntegral α F) :=
    RotationCalculus.fractionalIntegral_raw_smooth α hα F hF
  have hderiv : ∀ (i : Fin 3) (G : Sphere → ℂ), IsSphereSmooth G →
      rotationDeriv i (fractionalIntegral α G) = fractionalIntegral α (rotationDeriv i G) := by
    intro i G hG
    exact RotationCalculus.fractionalIntegral_raw_rotationDeriv α hα i G hG
  have hword : ∀ w : List (Fin 3), rotationWord w (fractionalIntegral α F) =
      fractionalIntegral α (rotationWord w F) :=
    fractionalIntegral_rotationWord_of_deriv α hderiv hF
  exact ⟨fractionalIntegral_integrable α hα hF, hsmooth, hword,
    fractionalIntegral_rotationSup_of_commutes α hα hF hword⟩

theorem positiveLaplacian_rotation_bound (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    IsSphereSmooth (positiveLaplacian F) ∧
    (∀ n : ℕ, 0 ≤ rotationSup n F) ∧
    (∀ n : ℕ, rotationSup n (fun x => F x + (9 / 2 : ℂ) * positiveLaplacian F x) ≤
      (29 / 2 : ℝ) * rotationSup (n + 2) F) := by
  refine ⟨positiveLaplacian_smooth hF, fun n => rotationSup_nonneg n F, fun n => ?_⟩
  apply Real.sSup_le _ (mul_nonneg (by norm_num) (rotationSup_nonneg (n + 2) F))
  rintro r ⟨w, hw, x, rfl⟩
  rw [rotationWord_add w hF (IsSphereSmooth.const_mul _ (positiveLaplacian_smooth hF)), rotationWord_const_mul w _ (positiveLaplacian_smooth hF)]
  simp only [rotationWord_positiveLaplacian w hF, norm_mul, norm_neg]
  have h1 : ‖rotationWord w F x‖ ≤ rotationSup (n + 2) F :=
    rotationWord_norm_le_rotationSup hF w (by omega) x
  have h2 : ‖∑ i : Fin 3, rotationWord (w ++ [i, i]) F x‖ ≤ 3 * rotationSup (n + 2) F := by
    calc
      _ ≤ ∑ i : Fin 3, ‖rotationWord (w ++ [i,i]) F x‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, rotationSup (n + 2) F := Finset.sum_le_sum (fun i _ =>
        rotationWord_norm_le_rotationSup hF _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) x)
      _ = _ := by simp
  have hnorm : ‖(9 / 2 : ℂ)‖ = (9 / 2 : ℝ) := by norm_num
  calc
    _ ≤ ‖rotationWord w F x‖ + (9 / 2 : ℝ) * ‖∑ i : Fin 3, rotationWord (w ++ [i,i]) F x‖ := by
      simpa only [norm_mul, norm_neg, hnorm] using
        norm_add_le (rotationWord w F x) ((9 / 2 : ℂ) * -∑ i : Fin 3, rotationWord (w ++ [i,i]) F x)
    _ ≤ rotationSup (n + 2) F + (9 / 2 : ℝ) * (3 * rotationSup (n + 2) F) :=
      add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

open Set
open scoped Pointwise

noncomputable def sphereOrthogonal (e : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  e.toHomeomorph.subtype (fun x => by
    change ‖x - 0‖ = 1 ↔ ‖e x - 0‖ = 1
    simp only [sub_zero, e.norm_map])
@[simp] theorem sphereOrthogonal_coe (e : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (sphereOrthogonal e x : Ambient) = e x := rfl

theorem sphereOrthogonal_measurePreserving (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereOrthogonal e) sphereArea sphereArea := by
  have hraw : MeasurePreserving (sphereOrthogonal e) volume.toSphere volume.toSphere := by
    refine ⟨(sphereOrthogonal e).measurable, Measure.ext fun s hs => ?_⟩
    rw [(sphereOrthogonal e).measurableEmbedding.map_apply,
      Measure.toSphere_apply' _ ((sphereOrthogonal e).measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereOrthogonal e) ⁻¹' s)) =
        e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
      ext z
      constructor
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨t, ht, e y, ⟨sphereOrthogonal e y, hy, rfl⟩, by simp⟩
      · rintro ⟨t, ht, _, ⟨y, hy, rfl⟩, heq⟩
        refine ⟨t, ht, e.symm y, ⟨(sphereOrthogonal e).symm y, ?_, rfl⟩, ?_⟩
        · simpa using hy
        · have := congrArg e.symm heq
          simpa using this
    rw [hset]
    exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _
  exact hraw.smul_measure _

noncomputable def rotationFlowMap (i : Fin 3) (t : ℝ) : Ambient →ₗ[ℝ] Ambient where
  toFun x := WithLp.toLp 2 (fun j : Fin 3 =>
    if j = i then x i else if j = i + 1 then
      Real.cos t * x (i+1) - Real.sin t * x (i+2)
    else Real.sin t * x (i+1) + Real.cos t * x (i+2))
  map_add' x y := by ext j; simp only [PiLp.toLp_apply, PiLp.add_apply]; split_ifs <;> ring
  map_smul' c x := by ext j; simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem rotationFlowMap_inverse (i : Fin 3) (t : ℝ) (x : Ambient) :
    rotationFlowMap i (-t) (rotationFlowMap i t x) = x := by
  have ht := Real.cos_sq_add_sin_sq t
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [rotationFlowMap, Fin.reduceAdd, Real.sin_neg, Real.cos_neg] <;>
    nlinarith [congrArg (fun a : ℝ => a * x 0) ht,
      congrArg (fun a : ℝ => a * x 1) ht,
      congrArg (fun a : ℝ => a * x 2) ht]

theorem rotationFlowMap_norm (i : Fin 3) (t : ℝ) (x : Ambient) :
    ‖rotationFlowMap i t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have ht := Real.cos_sq_add_sin_sq t
  fin_cases i <;> simp only [Fin.sum_univ_three, rotationFlowMap, LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.toLp_apply, Fin.reduceAdd, Real.norm_eq_abs, sq_abs] <;>
    simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

noncomputable def rotationFlow (i : Fin 3) (t : ℝ) : Ambient ≃ₗᵢ[ℝ] Ambient where
  toLinearEquiv :=
    { rotationFlowMap i t with
      invFun := rotationFlowMap i (-t)
      left_inv := rotationFlowMap_inverse i t
      right_inv := fun x => by
        change rotationFlowMap i t (rotationFlowMap i (-t) x) = x
        simpa only [neg_neg] using rotationFlowMap_inverse i (-t) x }
  norm_map' := rotationFlowMap_norm i t

@[simp] theorem rotationFlow_apply (i : Fin 3) (t : ℝ) (x : Ambient) :
    rotationFlow i t x = rotationFlowMap i t x := rfl
@[simp] theorem rotationFlow_zero (i : Fin 3) (x : Ambient) : rotationFlow i 0 x = x := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [rotationFlowMap, rotationFlow, Fin.reduceAdd]
theorem rotationFlow_hasDerivAt (i : Fin 3) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => rotationFlow i t x) (rotationVector i (rotationFlow i t x)) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : HasDerivAt (fun t => (rotationFlow i t x).ofLp)
      ((rotationVector i (rotationFlow i t x)).ofLp) t := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [rotationFlow_apply, rotationFlowMap, rotationVector, Fin.reduceAdd]
    all_goals
      first
      | exact hasDerivAt_const t _
      | convert ((Real.hasDerivAt_cos t).mul_const _).sub ((Real.hasDerivAt_sin t).mul_const _) using 1 <;> ring
      | convert ((Real.hasDerivAt_sin t).mul_const _).add ((Real.hasDerivAt_cos t).mul_const _) using 1 <;> ring
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem sphereOrthogonal_rotationFlow_hasDerivAt (i : Fin 3) {F : Sphere → ℂ}
    (hF : IsSphereSmooth F) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun t => F (sphereOrthogonal (rotationFlow i t) x))
      (rotationDeriv i F (sphereOrthogonal (rotationFlow i t) x)) t := by
  have hn : (sphereOrthogonal (rotationFlow i t) x : Ambient) ≠ 0 := by
    intro hz
    have hs := (sphereOrthogonal (rotationFlow i t) x).property
    simp [Metric.mem_sphere, hz] at hs
  have hd := ((hF _ hn).contDiffAt (isOpen_ne.mem_nhds hn)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t (rotationFlow_hasDerivAt i (x : Ambient) t)
  simpa only [Function.comp_def, ← sphereOrthogonal_coe, radialExtension_sphere, rotationDeriv] using hc

end DedekindZetaZeroFree.ComplexFractionalInverse
