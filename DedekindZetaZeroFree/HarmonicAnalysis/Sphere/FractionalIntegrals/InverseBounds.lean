module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexCompactSphericalCharts
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.HarmonicIdentity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped NNReal

noncomputable def fractionalInverse (β : ℂˣ) (F : Sphere → ℂ) (x : Sphere) : ℂ :=
  let G := fractionalIntegral (2 / 3) F
  (sphericalScalar β : ℂ)⁻¹ * (G x + (9 / 2 : ℂ) * positiveLaplacian G x)

private theorem laplacian_add {F G : Sphere → ℂ}
    (hF : IsSphereSmooth F) (hG : IsSphereSmooth G) :
    positiveLaplacian (fun x => F x + G x) =
      fun x => positiveLaplacian F x + positiveLaplacian G x := by
  funext x
  simp only [positiveLaplacian, rotationDeriv_add _ hF hG,
    rotationDeriv_add _ (rotationDeriv_smooth _ hF) (rotationDeriv_smooth _ hG),
    Finset.sum_add_distrib, neg_add]

private theorem laplacian_mul (c : ℂ) {F : Sphere → ℂ}
    (hF : IsSphereSmooth F) :
    positiveLaplacian (fun x => c * F x) =
      fun x => c * positiveLaplacian F x := by
  funext x
  simp only [positiveLaplacian, rotationDeriv_const_mul _ c hF,
    rotationDeriv_const_mul _ c (rotationDeriv_smooth _ hF),
    ← Finset.mul_sum, mul_neg]

noncomputable def inverseCore (F : Sphere → ℂ) : Sphere → ℂ :=
  let G := fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) F)
  fun x => G x + (9 / 2 : ℂ) * positiveLaplacian G x

private theorem inverseCore_sub {F P : Sphere → ℂ}
    (hF : IsSphereSmooth F) (hP : IsSphereSmooth P) :
    inverseCore (fun x => F x - P x) =
      fun x => inverseCore F x - inverseCore P x := by
  have hs (H : Sphere → ℂ) (hH : IsSphereSmooth H) :=
    (fractionalIntegral_rotation (1 / 3) (by norm_num) H hH).2.1
  have hs' (H : Sphere → ℂ) (hH : IsSphereSmooth H) :=
    (fractionalIntegral_rotation (2 / 3) (by norm_num)
      (fractionalIntegral (1 / 3) H) (hs H hH)).2.1
  unfold inverseCore
  simp only [sub_eq_add_neg, fractionalIntegral_add _ (by norm_num : (0 : ℝ) < 1 / 3)
    hF hP.neg, fractionalIntegral_neg]
  rw [fractionalIntegral_add _ (by norm_num : (0 : ℝ) < 2 / 3)
    (hs F hF) (hs P hP).neg, fractionalIntegral_neg]
  rw [laplacian_add (hs' F hF) (hs' P hP).neg]
  have hn : positiveLaplacian (fun x => -(fractionalIntegral (2 / 3)
      (fractionalIntegral (1 / 3) P) x)) =
      fun x => -(positiveLaplacian (fractionalIntegral (2 / 3)
        (fractionalIntegral (1 / 3) P)) x) := by
    simpa only [neg_one_mul] using laplacian_mul (-1) (hs' P hP)
  rw [hn]
  funext x
  ring

private theorem inverseCore_bound {F : Sphere → ℂ} (hF : IsSphereSmooth F)
    (x : Sphere) : ‖inverseCore F x‖ ≤ (29 / 2 : ℝ) * rotationSup 2 F := by
  have hT := fractionalIntegral_rotation (1 / 3) (by norm_num) F hF
  have hG := fractionalIntegral_rotation (2 / 3) (by norm_num)
    (fractionalIntegral (1 / 3) F) hT.2.1
  have hsum := hG.2.1.add ((positiveLaplacian_smooth hG.2.1).const_mul (9 / 2 : ℂ))
  calc
    _ ≤ rotationSup 0 (inverseCore F) :=
      rotationWord_norm_le_rotationSup hsum [] (by simp) x
    _ ≤ (29 / 2 : ℝ) * rotationSup 2
        (fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) F)) :=
      (positiveLaplacian_rotation_bound _ hG.2.1).2.2 0
    _ ≤ (29 / 2 : ℝ) * rotationSup 2 (fractionalIntegral (1 / 3) F) :=
      mul_le_mul_of_nonneg_left (hG.2.2.2 2) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hT.2.2.2 2) (by norm_num)

private theorem inverseCore_identity (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    inverseCore F = F := by
  obtain ⟨p, hp⟩ := finite_polynomial_smooth_density F hF
  funext x
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb (N : ℕ) : ‖inverseCore F x - F x‖ ≤
      (29 / 2 : ℝ) * rotationSup 2 (fun y => F y - polynomialSphere (p N) y) +
        rotationSup 0 (fun y => F y - polynomialSphere (p N) y) := by
    have hP := polynomialSphere_smooth (p N)
    have hd := hF.add hP.neg
    have hpoly : inverseCore (polynomialSphere (p N)) = polynomialSphere (p N) :=
      fractional_polynomial_identity (p N)
    have he : inverseCore F x - F x =
        inverseCore (fun y => F y - polynomialSphere (p N) y) x -
          (F x - polynomialSphere (p N) x) := by
      rw [inverseCore_sub hF hP, hpoly]
      ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add
      (inverseCore_bound hd x)
      (rotationWord_norm_le_rotationSup hd [] (n := 0) (by simp) x))
  have ht := ((hp 2).const_mul (29 / 2 : ℝ)).add (hp 0)
  simpa only [mul_zero, add_zero] using ge_of_tendsto' ht hb

theorem fractionalInverse_leftIdentity (β : ℂˣ) (F : Sphere → ℂ)
    (hF : IsSphereSmooth F) :
    fractionalInverse β (fun x => (sphericalScalar β : ℂ) *
      fractionalIntegral (1 / 3) F x) = F := by
  have hG := (fractionalIntegral_rotation (1 / 3) (by norm_num) F hF).2.1
  have hH := (fractionalIntegral_rotation (2 / 3) (by norm_num)
    (fractionalIntegral (1 / 3) F) hG).2.1
  have ha : (sphericalScalar β : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sphericalScalar_pos β))
  unfold fractionalInverse
  rw [fractionalIntegral_const_mul]
  dsimp only
  rw [laplacian_mul _ hH]
  funext x
  change (sphericalScalar β : ℂ)⁻¹ *
    ((sphericalScalar β : ℂ) * _ + (9 / 2 : ℂ) *
      ((sphericalScalar β : ℂ) * _)) = _
  rw [show (sphericalScalar β : ℂ) *
      fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) F) x +
      (9 / 2 : ℂ) * ((sphericalScalar β : ℂ) *
        positiveLaplacian (fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) F)) x) =
      (sphericalScalar β : ℂ) * inverseCore F x by
    unfold inverseCore
    ring]
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul, inverseCore_identity F hF]

theorem fractionalInverse_rotation_bound (β : ℂˣ) (F : Sphere → ℂ)
    (hF : IsSphereSmooth F) (n : ℕ) :
    rotationSup n (fractionalInverse β F) ≤
      ((29 / 2 : ℝ) / sphericalScalar β) * rotationSup (n + 2) F := by
  let G := fractionalIntegral (2 / 3) F
  have hG := (fractionalIntegral_rotation (2 / 3) (by norm_num) F hF).2
  have hL := positiveLaplacian_smooth hG.1
  have hsum := hG.1.add (hL.const_mul (9 / 2 : ℂ))
  have ha : ‖(sphericalScalar β : ℂ)⁻¹‖ = (sphericalScalar β)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sphericalScalar_pos β)]
  change rotationSup n (fun x => (sphericalScalar β : ℂ)⁻¹ *
    (G x + (9 / 2 : ℂ) * positiveLaplacian G x)) ≤ _
  calc
    _ ≤ ‖(sphericalScalar β : ℂ)⁻¹‖ *
        rotationSup n (fun x => G x + (9 / 2 : ℂ) * positiveLaplacian G x) :=
      rotationSup_const_mul_le n _ hsum
    _ ≤ (sphericalScalar β)⁻¹ * ((29 / 2 : ℝ) * rotationSup (n + 2) G) := by
      rw [ha]
      exact mul_le_mul_of_nonneg_left
        ((positiveLaplacian_rotation_bound G hG.1).2.2 n) (inv_nonneg.mpr (sphericalScalar_pos β).le)
    _ ≤ (sphericalScalar β)⁻¹ * ((29 / 2 : ℝ) * rotationSup (n + 2) F) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hG.2.2 (n + 2)) (by norm_num)) (inv_nonneg.mpr (sphericalScalar_pos β).le)
    _ = _ := by ring

theorem standardIntertwiner_fractional_leftInverse (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    fractionalInverse β (sphereProfile negativeParameter (standardIntertwiner β f)) =
      sphereProfile positiveParameter f := by
  rw [standardIntertwiner_sphereProfile]
  exact fractionalInverse_leftIdentity β _ (sphereProfile_spec _ f).1

theorem actual_chart_inverse_bound (β : ℂˣ) (n : ℕ) :
    ∃ (orders : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ f : PrincipalSeries positiveParameter,
        chartSeminorm positiveParameter n f ≤
          (C • orders.sup (chartSeminorm negativeParameter)) (standardIntertwiner β f) := by
  obtain ⟨C, _, hC, _, hc, _⟩ := chart_rotation_comparison positiveParameter n
  obtain ⟨_, D, _, hD, _, hd⟩ := chart_rotation_comparison negativeParameter (n + 2)
  let K : ℝ≥0 := ⟨(29 / 2 : ℝ) / sphericalScalar β,
    (div_pos (by norm_num) (sphericalScalar_pos β)).le⟩
  have hK : K ≠ 0 := by
    apply ne_of_gt
    change 0 < (29 / 2 : ℝ) / sphericalScalar β
    exact div_pos (by norm_num) (sphericalScalar_pos β)
  refine ⟨Finset.range ((n + 2) + 1), C * K * D,
    mul_ne_zero (mul_ne_zero hC hK) hD, ?_⟩
  intro f
  have hB := fractionalInverse_rotation_bound β
    (sphereProfile negativeParameter (standardIntertwiner β f))
    (sphereProfile_spec _ _).1 n
  rw [standardIntertwiner_fractional_leftInverse] at hB
  calc
    chartSeminorm positiveParameter n f ≤
        (C : ℝ) * rotationSup n (sphereProfile positiveParameter f) := hc f
    _ ≤ (C : ℝ) * ((K : ℝ) *
        rotationSup (n + 2) (sphereProfile negativeParameter (standardIntertwiner β f))) :=
      mul_le_mul_of_nonneg_left hB C.coe_nonneg
    _ ≤ (C : ℝ) * ((K : ℝ) *
        (D • (Finset.range ((n + 2) + 1)).sup (chartSeminorm negativeParameter))
          (standardIntertwiner β f)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hd _) K.coe_nonneg) C.coe_nonneg
    _ = ((C * K * D) •
        (Finset.range ((n + 2) + 1)).sup (chartSeminorm negativeParameter))
          (standardIntertwiner β f) := by
      simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul]
      ring

end DedekindZetaZeroFree.ComplexFractionalInverse
