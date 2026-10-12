module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
open KPCplxIntertwinerEigenvalues
open scoped BigOperators
open MvPolynomial

noncomputable def rot (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p

private theorem rot_X (i j : Fin 3) (x : Ambient) :
    eval (fun k => (x k : ℂ)) (rot i (X j)) = ((rotationVector i x) j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [rot, pderiv_X, Pi.single_apply, rotationVector, Fin.reduceAdd]

private theorem rot_eval_flow (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => eval (fun j => ((rotationFlow i t x) j : ℂ)) p)
      (eval (fun j => ((rotationFlow i t x) j : ℂ)) (rot i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [rot] using (hasDerivAt_const t a)
  | add p q hp hq =>
    have hd := hp.add hq
    change HasDerivAt (fun t => eval _ p + eval _ q) _ t at hd
    convert hd using 1
    · simp only [map_add]
    · simp only [rot, map_add, map_sub, map_mul, eval_X]
      ring
  | mul_X p j hp =>
    have hj := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t
        (rotationFlow_hasDerivAt i x t))
    change HasDerivAt (fun t => ((rotationFlow i t x) j : ℂ))
      ((rotationVector i (rotationFlow i t x)) j : ℂ) t at hj
    have hd := hp.mul hj
    change HasDerivAt (fun t => eval _ p * ((rotationFlow i t x) j : ℂ)) _ t at hd
    convert hd using 1
    · simp only [map_mul, eval_X]
    · rw [← rot_X i j (rotationFlow i t x)]
      simp only [rot, pderiv_mul, map_sub, map_add, map_mul, eval_X]
      ring

private theorem rotationDeriv_polynomial (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    rotationDeriv i (polynomialSphere p) = polynomialSphere (rot i p) := by
  funext x
  have h := sphereOrthogonal_rotationFlow_hasDerivAt i (polynomialSphere_smooth p) x 0
  have g := rot_eval_flow i p (x : Ambient) 0
  have he : (fun t => polynomialSphere p (sphereOrthogonal (rotationFlow i t) x)) =
      (fun t => eval (fun j => ((rotationFlow i t (x : Ambient)) j : ℂ)) p) := rfl
  rw [he] at h
  have hh := h.unique g
  have hz : sphereOrthogonal (rotationFlow i 0) x = x := by
    apply Subtype.ext
    exact rotationFlow_zero i x
  simpa only [hz, rotationFlow_zero, polynomialSphere] using hh

noncomputable def euler (p : MvPolynomial (Fin 3) ℂ) :=
  ∑ i : Fin 3, X i * pderiv i p

private theorem casimir (p : MvPolynomial (Fin 3) ℂ) :
    -(∑ i : Fin 3, rot i (rot i p)) =
      euler (euler p) + euler p - (∑ i : Fin 3, X i ^ 2) * polynomialLaplacian p := by
  simp only [rot, euler, polynomialLaplacian, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
    map_add, map_sub, pderiv_mul, Fin.reduceAdd, pderiv_X, Pi.single_apply]
  norm_num
  ring

theorem homogeneous_positiveLaplacian (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :
    positiveLaplacian (polynomialSphere p) = fun x =>
      ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * polynomialSphere p x -
        polynomialSphere (polynomialLaplacian p) x := by
  have he : euler p = ℓ • p :=
    (MvPolynomial.mem_homogeneousSubmodule ℓ p).mp hp |>.sum_X_mul_pderiv
  have hee : euler (euler p) = ℓ • (ℓ • p) := by
    calc
      euler (euler p) = euler (ℓ • p) := by rw [he]
      _ = ℓ • euler p := by
        simp only [euler, Fin.sum_univ_three, map_nsmul]
        simp only [nsmul_eq_mul]
        ring
      _ = ℓ • (ℓ • p) := by rw [he]
  funext x
  have hn : ‖(x : Ambient)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have hs : ∑ i : Fin 3, ((x : Ambient) i : ℂ)^2 = 1 := by
    have hr : ∑ i : Fin 3, ((x : Ambient) i)^2 = 1 := by
      simpa [Real.norm_eq_abs, sq_abs, hn] using
        (EuclideanSpace.norm_sq_eq (x : Ambient)).symm
    exact_mod_cast hr
  simp only [positiveLaplacian]
  simp_rw [rotationDeriv_polynomial]
  unfold polynomialSphere
  rw [← map_sum, ← map_neg, casimir, hee, he]
  simp only [map_add, map_sub, map_mul, map_sum, map_pow, eval_X, hs, one_mul,
    map_nsmul]
  simp only [nsmul_eq_mul]
  ring

end DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity
