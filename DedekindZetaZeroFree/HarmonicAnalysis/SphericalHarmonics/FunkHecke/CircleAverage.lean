module

public import DedekindZetaZeroFree.Geometry.HarmonicPolynomialLatitudeAverage
public import DedekindZetaZeroFree.Geometry.ZonalHarmonicLegendreEquation

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
open MeasureTheory KPCplxIntertwinerEigenvalues
open scoped RealInnerProductSpace

instance angleMeasure_isProbabilityMeasure : IsProbabilityMeasure angleMeasure := by
  constructor
  change angleMeasure Set.univ = 1
  rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (by norm_num) Real.pi_pos))) ENNReal.ofReal_ne_top

@[simp] theorem shiftedLegendre_eval_zero (ℓ : ℕ) :
    (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) 0 = 1 := by
  simp [Polynomial.shiftedLegendre, Polynomial.eval₂_finset_sum, Finset.sum_range_succ']

@[simp] theorem latitudePoint_zero_val (g : Ambient ≃ₗᵢ[ℝ] Ambient) (θ : ℝ) :
    (latitudePoint g 0 θ : Ambient) = g north := by
  rw [latitudePoint_val _ _ _ (by constructor <;> norm_num)]
  apply congrArg g
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [latitudeAmbient, north, PiLp.single_apply]

@[simp] theorem latitudePoint_one_val (g : Ambient ≃ₗᵢ[ℝ] Ambient) (θ : ℝ) :
    (latitudePoint g 1 θ : Ambient) = -g north := by
  rw [latitudePoint_val _ _ _ (by constructor <;> norm_num), latitudeAmbient, ← map_neg]
  apply congrArg g
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> norm_num [north, PiLp.single_apply]

@[simp] theorem shiftedLegendre_eval_one (ℓ : ℕ) :
    (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) 1 = (-1 : ℝ) ^ ℓ := by
  have h := Polynomial.shiftedLegendre_eval_symm ℓ (1 : ℝ)
  simpa [Polynomial.aeval_def, Polynomial.coeff_shiftedLegendre] using h

theorem harmonic_latitude_average_north (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g 0 θ) ∂angleMeasure) =
      ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) 0 : ℝ) *
        polynomialSphere p ⟨g north,
          mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  simp [polynomialSphere, integral_const, Polynomial.coeff_shiftedLegendre]

noncomputable def linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

theorem pderiv_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (linearSubstitution A p) =
      ∑ i, MvPolynomial.C (A i j) * linearSubstitution A (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [linearSubstitution]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, linearSubstitution, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold linearSubstitution at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

theorem polynomialLaplacian_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (linearSubstitution A p) = linearSubstitution A (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (linearSubstitution A p))) =
    ∑ j, linearSubstitution A (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_linearSubstitution, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_linearSubstitution, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

theorem linearSubstitution_homogeneous (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (linearSubstitution A p).IsHomogeneous ℓ := by
  unfold linearSubstitution
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

theorem linearSubstitution_harmonic (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    linearSubstitution A p ∈ harmonicPolynomials ℓ := by
  refine ⟨linearSubstitution_homogeneous A p ℓ hp.1, ?_⟩
  change polynomialLaplacian (linearSubstitution A p) = 0
  rw [polynomialLaplacian_linearSubstitution A hA]
  have hh : polynomialLaplacian p = 0 := hp.2
  rw [hh, map_zero]

noncomputable def orthogonalSubstitutionMatrix (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j => (g.symm (EuclideanSpace.single i 1)) j

theorem orthogonalSubstitutionMatrix_orthogonal (g : Ambient ≃ₗᵢ[ℝ] Ambient) (i k : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * orthogonalSubstitutionMatrix g k j =
      if i = k then 1 else 0 := by
  simp only [orthogonalSubstitutionMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hh := g.symm.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)
  rw [PiLp.inner_apply] at hh
  simp only [RCLike.inner_apply, conj_trivial] at hh
  rw [show (∑ j, (g.symm (EuclideanSpace.single i 1)) j * (g.symm (EuclideanSpace.single k 1)) j) =
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single k 1) by
      simpa [mul_comm] using hh]
  by_cases h : i = k
  · subst k
    simp [EuclideanSpace.inner_single_left, PiLp.single_apply]
  · simp [EuclideanSpace.inner_single_left, PiLp.single_apply, h, Ne.symm h]

theorem orthogonalSubstitutionMatrix_eval (g : Ambient ≃ₗᵢ[ℝ] Ambient) (v : Ambient) (i : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * (v j : ℂ) = ((g v) i : ℂ) := by
  simp only [orthogonalSubstitutionMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  have hh := g.symm.inner_map_map (EuclideanSpace.single i 1) (g v)
  simp only [g.symm_apply_apply, EuclideanSpace.inner_single_left, mul_one] at hh
  rw [PiLp.inner_apply] at hh
  simp only [RCLike.inner_apply, conj_trivial] at hh
  simpa [mul_comm] using hh

theorem orthogonalSubstitution_eval (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℂ) (v : Ambient) :
    MvPolynomial.eval (fun j => (v j : ℂ)) (linearSubstitution (orthogonalSubstitutionMatrix g) p) =
      MvPolynomial.eval (fun i => ((g v) i : ℂ)) p := by
  unfold linearSubstitution
  change MvPolynomial.aeval (fun j => (v j : ℂ))
    (MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (orthogonalSubstitutionMatrix g i j) * MvPolynomial.X j) p) =
    MvPolynomial.aeval (fun i => ((g v) i : ℂ)) p
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self]
  exact orthogonalSubstitutionMatrix_eval g v i

theorem orthogonalSubstitution_latitude (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℂ) (u θ : ℝ) :
    polynomialSphere (linearSubstitution (orthogonalSubstitutionMatrix g) p)
      (latitudePoint (.refl ℝ Ambient) u θ) = polynomialSphere p (latitudePoint g u θ) := by
  simp only [polynomialSphere, orthogonalSubstitution_eval]
  apply congrArg (fun v : Ambient => MvPolynomial.eval (fun i => (v i : ℂ)) p)
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, latitudeAmbient]
  · simp [latitudePoint, hu]

theorem harmonic_latitude_average_of_standardFrame (ℓ : ℕ)
    (hstandard : ∀ q : MvPolynomial (Fin 3) ℂ, q ∈ harmonicPolynomials ℓ →
      ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere q (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere q ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere p ⟨g north,
            mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  have hh := hstandard (linearSubstitution (orthogonalSubstitutionMatrix g) p)
    (linearSubstitution_harmonic _ (orthogonalSubstitutionMatrix_orthogonal g) ℓ p hp) u hu
  simp_rw [orthogonalSubstitution_latitude] at hh
  simpa only [polynomialSphere, orthogonalSubstitution_eval] using hh

theorem harmonic_latitude_average (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
      ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
        polynomialSphere p ⟨g north,
          mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  apply harmonic_latitude_average_of_standardFrame ℓ _ p hp g u hu
  intro q hq v hv
  obtain ⟨Q, hprofile, hnorth⟩ := CircleAverage.latitude_average_polynomial q
  have hode := CircleAverage.latitude_average_legendre_ode ℓ q hq Q hprofile
  have hunique := CircleAverage.polynomial_shiftedLegendre_ode_unique ℓ Q hode
  rw [hprofile v hv, hunique, Polynomial.eval_mul, Polynomial.eval_C, hnorth]
  rw [Polynomial.eval_map]
  have hcast := Polynomial.hom_eval₂ (Polynomial.shiftedLegendre ℓ)
    (Int.castRingHom ℝ) Complex.ofRealHom v
  have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n
    simp
  rw [hcomp] at hcast
  change (((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) v : ℝ) : ℂ) =
    (Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℂ) (v : ℂ) at hcast
  rw [hcast, mul_comm]

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
