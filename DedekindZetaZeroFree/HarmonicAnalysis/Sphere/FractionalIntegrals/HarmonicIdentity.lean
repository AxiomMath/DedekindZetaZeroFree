module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalHarmonics.PolynomialFunkHecke
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalHarmonics.RotationLaplacian

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse
open KPCplxIntertwinerEigenvalues
open scoped BigOperators

noncomputable def fractionalEigenvalue (α : ℝ) (ℓ : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 ℓ, (((j : ℝ) - α) / ((j : ℝ) + α))

theorem fractionalIntegral_harmonic (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    (∀ α : ℝ, 0 < α → α < 1 →
      fractionalIntegral α (polynomialSphere p) =
        fun x => (fractionalEigenvalue α ℓ : ℂ) * polynomialSphere p x) ∧
    (positiveLaplacian (polynomialSphere p) =
      fun x => ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * polynomialSphere p x) := by
  constructor
  · intro α hα hα1
    funext x
    have h := (HarmonicIdentity.polynomial_funkHecke ℓ p hp
      (fun u => α * u ^ (α - 1))
      (HarmonicIdentity.powerWeight_integrable α hα) x).2
    change fractionalIntegral α (polynomialSphere p) x = _
    simpa only [fractionalIntegral, fractionalKernel,
      HarmonicIdentity.shiftedLegendre_beta ℓ α hα hα1,
      fractionalEigenvalue, Real.rpow_eq_pow] using h
  · have hp' : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ ∧
        polynomialLaplacian p = 0 := hp
    rw [HarmonicIdentity.homogeneous_positiveLaplacian ℓ p hp'.1]
    funext x
    simp [hp'.2, polynomialSphere]

theorem fractionalEigenvalue_product (ℓ : ℕ) :
    fractionalEigenvalue (1 / 3) ℓ * fractionalEigenvalue (2 / 3) ℓ =
      2 / (((3 : ℝ) * ℓ + 1) * (3 * ℓ + 2)) := by
  induction ℓ with
  | zero => norm_num [fractionalEigenvalue]
  | succ n ih =>
    simp only [fractionalEigenvalue] at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [show (∏ j ∈ Finset.Icc 1 n, ((j : ℝ) - 1 / 3) / ((j : ℝ) + 1 / 3)) *
        ((((n + 1 : ℕ) : ℝ) - 1 / 3) / (((n + 1 : ℕ) : ℝ) + 1 / 3)) *
        ((∏ j ∈ Finset.Icc 1 n, ((j : ℝ) - 2 / 3) / ((j : ℝ) + 2 / 3)) *
          ((((n + 1 : ℕ) : ℝ) - 2 / 3) / (((n + 1 : ℕ) : ℝ) + 2 / 3))) =
        ((∏ j ∈ Finset.Icc 1 n, ((j : ℝ) - 1 / 3) / ((j : ℝ) + 1 / 3)) *
          (∏ j ∈ Finset.Icc 1 n, ((j : ℝ) - 2 / 3) / ((j : ℝ) + 2 / 3))) *
          (((((n + 1 : ℕ) : ℝ) - 1 / 3) / (((n + 1 : ℕ) : ℝ) + 1 / 3)) *
            ((((n + 1 : ℕ) : ℝ) - 2 / 3) / (((n + 1 : ℕ) : ℝ) + 2 / 3))) by ring]
    rw [ih]
    push_cast
    field_simp
    <;> ring

private lemma sphere_ne_zero (x : Sphere) : (x : Ambient) ≠ 0 := by
  have h : ‖(x : Ambient)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.property
  intro h0
  simp [h0] at h

private lemma smooth_diff (F : Sphere → ℂ) (hF : IsSphereSmooth F) (x : Sphere) :
    DifferentiableAt ℝ (radialExtension F) (x : Ambient) := by
  exact (hF.differentiableOn (by simp)).differentiableAt
    (isOpen_ne.mem_nhds (sphere_ne_zero x))

private lemma harmonic_rotationVector_smooth (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (rotationVector i) := by
  unfold rotationVector
  change ContDiff ℝ (⊤ : ℕ∞) (WithLp.toLp 2 ∘
    (fun x : Ambient => fun j : Fin 3 => if j = i + 1 then -x (i + 2) else if j = i + 2 then x (i + 1) else 0))
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro j
  split_ifs
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 2)).contDiff.neg
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i + 1)).contDiff
  · exact contDiff_const

private lemma normalize_smooth :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Ambient => ‖x‖⁻¹ • x) {x | x ≠ 0} := by
  exact ((contDiff_id.contDiffOn.norm ℝ (by intro x hx; exact hx)).inv
    (by intro x hx; exact norm_ne_zero_iff.mpr hx)).smul contDiff_id.contDiffOn

private lemma rotation_smooth (i : Fin 3) (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    IsSphereSmooth (rotationDeriv i F) := by
  have hd := hF.fderiv_of_isOpen isOpen_ne (m := (⊤ : ℕ∞)) (by simp)
  have hg := hd.clm_apply (harmonic_rotationVector_smooth i).contDiffOn
  have hn : Set.MapsTo (fun x : Ambient => ‖x‖⁻¹ • x) {x | x ≠ 0} {x | x ≠ 0} := by
    intro x hx
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx
  apply (hg.comp normalize_smooth hn).congr
  intro x hx
  change x ≠ 0 at hx
  simp only [Function.comp_apply, radialExtension, dif_pos hx, rotationDeriv]

private lemma radial_sum {ι : Type*} (I : Finset ι) (F : ι → Sphere → ℂ) :
    radialExtension (fun x => ∑ i ∈ I, F i x) = ∑ i ∈ I, radialExtension (F i) := by
  classical
  funext x
  by_cases hx : x = 0
  · simp [radialExtension, hx]
  · simp [radialExtension, hx]

private lemma radial_mul (c : ℂ) (F : Sphere → ℂ) :
    radialExtension (fun x => c * F x) = c • radialExtension F := by
  funext x
  by_cases hx : x = 0 <;> simp [radialExtension, hx]

private lemma mul_smooth (c : ℂ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    IsSphereSmooth (fun x => c * F x) := by
  unfold IsSphereSmooth
  rw [radial_mul]
  exact contDiffOn_const.smul hF

private lemma rotation_sum {ι : Type*} (I : Finset ι) (F : ι → Sphere → ℂ)
    (hF : ∀ i ∈ I, IsSphereSmooth (F i)) (j : Fin 3) :
    rotationDeriv j (fun x => ∑ i ∈ I, F i x) = fun x => ∑ i ∈ I, rotationDeriv j (F i) x := by
  classical
  funext x
  simp only [rotationDeriv, radial_sum]
  rw [fderiv_sum (by intro i hi; exact smooth_diff _ (hF i hi) x)]
  simp

private lemma rotation_mul (c : ℂ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) (j : Fin 3) :
    rotationDeriv j (fun x => c * F x) = fun x => c * rotationDeriv j F x := by
  funext x
  simp only [rotationDeriv, radial_mul]
  rw [fderiv_const_smul (smooth_diff _ hF x)]
  simp

private lemma lap_sum {ι : Type*} (I : Finset ι) (F : ι → Sphere → ℂ)
    (hF : ∀ i ∈ I, IsSphereSmooth (F i)) :
    positiveLaplacian (fun x => ∑ i ∈ I, F i x) = fun x => ∑ i ∈ I, positiveLaplacian (F i) x := by
  classical
  funext x
  simp only [positiveLaplacian, rotation_sum I F hF]
  have hh (j : Fin 3) := rotation_sum I (fun k => rotationDeriv j (F k))
    (by intro k hk; exact rotation_smooth _ _ (hF k hk)) j
  simp only [hh]
  rw [Finset.sum_comm]
  simp

private lemma lap_mul (c : ℂ) (F : Sphere → ℂ) (hF : IsSphereSmooth F) :
    positiveLaplacian (fun x => c * F x) = fun x => c * positiveLaplacian F x := by
  funext x
  simp only [positiveLaplacian, rotation_mul c F hF]
  simp only [rotation_mul c (rotationDeriv _ F) (rotation_smooth _ _ hF)]
  simp [Finset.mul_sum]

private lemma integral_sum {ι : Type*} (I : Finset ι) (F : ι → Sphere → ℂ)
    (hF : ∀ i ∈ I, IsSphereSmooth (F i)) (α : ℝ) (hα : 0 < α) :
    fractionalIntegral α (fun x => ∑ i ∈ I, F i x) = fun x => ∑ i ∈ I, fractionalIntegral α (F i) x := by
  classical
  funext x
  simp only [fractionalIntegral, Finset.mul_sum]
  exact MeasureTheory.integral_finset_sum I
    (by intro i hi; exact (fractionalIntegral_rotation α hα _ (hF i hi)).1 x)

private lemma integral_mul (c : ℂ) (F : Sphere → ℂ) (α : ℝ) :
    fractionalIntegral α (fun x => c * F x) = fun x => c * fractionalIntegral α F x := by
  funext x
  simp only [fractionalIntegral]
  simp_rw [show ∀ y : Sphere, (fractionalKernel α x y : ℂ) * (c * F y) =
    c • ((fractionalKernel α x y : ℂ) * F y) by intro y; simp [mul_left_comm]]
  rw [MeasureTheory.integral_smul]
  rfl

theorem fractional_polynomial_identity (p : MvPolynomial (Fin 3) ℂ) :
    let G := fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) (polynomialSphere p))
    (fun x => G x + (9 / 2 : ℂ) * positiveLaplacian G x) = polynomialSphere p := by
  classical
  obtain ⟨I, h, hh, he⟩ := finite_fischer_spanning p
  have hp : polynomialSphere p = fun x => ∑ ℓ ∈ I, polynomialSphere (h ℓ) x := funext he
  have hf (ℓ : ℕ) := polynomialSphere_smooth (h ℓ)
  have hi : fractionalIntegral (1 / 3) (polynomialSphere p) =
      fun x => ∑ ℓ ∈ I, (fractionalEigenvalue (1 / 3) ℓ : ℂ) * polynomialSphere (h ℓ) x := by
    rw [hp, integral_sum I _ (by intro ℓ hℓ; exact hf ℓ) _ (by norm_num)]
    funext x
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [(fractionalIntegral_harmonic ℓ _ (hh ℓ hℓ)).1 _ (by norm_num) (by norm_num)]
  have hg : fractionalIntegral (2 / 3) (fractionalIntegral (1 / 3) (polynomialSphere p)) =
      fun x => ∑ ℓ ∈ I, ((fractionalEigenvalue (1 / 3) ℓ : ℂ) *
        (fractionalEigenvalue (2 / 3) ℓ : ℂ)) * polynomialSphere (h ℓ) x := by
    rw [hi, integral_sum I _ (by intro ℓ hℓ; exact mul_smooth _ _ (hf ℓ)) _ (by norm_num)]
    funext x
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [integral_mul, (fractionalIntegral_harmonic ℓ _ (hh ℓ hℓ)).1 _ (by norm_num) (by norm_num)]
    exact (mul_assoc _ _ _).symm
  dsimp only
  rw [hg, lap_sum I _ (by intro ℓ hℓ; exact mul_smooth _ _ (hf ℓ))]
  funext x
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, hp]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [lap_mul _ _ (hf ℓ), (fractionalIntegral_harmonic ℓ _ (hh ℓ hℓ)).2]
  change _ * polynomialSphere (h ℓ) x + (9 / 2 : ℂ) *
    (_ * (((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * polynomialSphere (h ℓ) x)) = _
  have hs := congrArg (fun r : ℝ => (r : ℂ)) (fractionalEigenvalue_product ℓ)
  push_cast at hs
  rw [hs]
  have h1 : (3 : ℂ) * ℓ + 1 ≠ 0 := by
    exact_mod_cast (show (3 : ℝ) * ℓ + 1 ≠ 0 by positivity)
  have h2 : (3 : ℂ) * ℓ + 2 ≠ 0 := by
    exact_mod_cast (show (3 : ℝ) * ℓ + 2 ≠ 0 by positivity)
  field_simp
  <;> ring

end DedekindZetaZeroFree.ComplexFractionalInverse
