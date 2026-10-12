module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.LatitudeDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
open MeasureTheory KPCplxIntertwinerEigenvalues MvPolynomial
open scoped BigOperators

noncomputable def rot (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p
noncomputable def euler (p : MvPolynomial (Fin 3) ℂ) :=
  ∑ i : Fin 3, X i * pderiv i p
noncomputable def casOp (p : MvPolynomial (Fin 3) ℂ) :=
  -(∑ i : Fin 3, rot i (rot i p))
private theorem casimir (p : MvPolynomial (Fin 3) ℂ) :
    casOp p = euler (euler p) + euler p -
      (∑ i : Fin 3, X i ^ 2) * polynomialLaplacian p := by
  simp only [casOp, rot, euler, polynomialLaplacian, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
    map_add, map_sub, pderiv_mul, Fin.reduceAdd, pderiv_X, Pi.single_apply]
  norm_num
  ring
private theorem casOp_eigen (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    casOp p = ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) • p := by
  have he : euler p = ℓ • p :=
    (MvPolynomial.mem_homogeneousSubmodule ℓ p).mp hp.1 |>.sum_X_mul_pderiv
  have hee : euler (euler p) = ℓ • (ℓ • p) := by
    calc
      euler (euler p) = euler (ℓ • p) := by rw [he]
      _ = ℓ • euler p := by
        simp only [euler, Fin.sum_univ_three, map_nsmul]
        simp only [nsmul_eq_mul]
        ring
      _ = ℓ • (ℓ • p) := by rw [he]
  have hl : polynomialLaplacian p = 0 := hp.2
  rw [casimir, hee, he, hl, mul_zero, sub_zero]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_mul, map_add, map_natCast, map_one]
  ring
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
private theorem rot_zero (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (rot i p) x = 0 := by
  intro x
  have hd := rot_eval_flow i p (x : Ambient) 0
  have he : (fun t => eval (fun j => ((rotationFlow i t (x : Ambient)) j : ℂ)) p) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    exact h (sphereOrthogonal (rotationFlow i t) x)
  rw [he] at hd
  simpa only [rotationFlow_zero, polynomialSphere] using hd.unique (hasDerivAt_const 0 (0 : ℂ))
private theorem casOp_zero (p : MvPolynomial (Fin 3) ℂ)
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (casOp p) x = 0 := by
  intro x
  simp only [polynomialSphere, casOp, map_neg, map_sum]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i hi
    exact rot_zero i (rot i p) (rot_zero i p h) x
noncomputable def heightLift : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Polynomial.aeval ((1 - X 0) * C (1 / 2))
private theorem pderiv_heightLift (i : Fin 3) (Q : Polynomial ℂ) :
    pderiv i (heightLift Q) = (if i = 0 then C (-1 / 2) else 0) *
      heightLift Q.derivative := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq, mul_add]
  | monomial n a =>
    simp only [heightLift, Polynomial.aeval_monomial, Polynomial.derivative_monomial,
      Polynomial.aeval_C, Polynomial.aeval_mul, map_pow, Polynomial.aeval_X, algebraMap_eq]
    rw [pderiv_C_mul, pderiv_pow]
    have hx : pderiv i ((1 - X 0) * C (1 / 2 : ℂ)) = if i = 0 then C (-1 / 2 : ℂ) else 0 := by
      by_cases hi : i = 0
      · subst i; simp [div_eq_mul_inv]
      · simp [pderiv_mul, pderiv_X, Pi.single_apply, hi, Ne.symm hi]
    simp only [hx, map_mul, map_natCast]
    by_cases hi : i = 0 <;> simp [hi] <;> ring
private theorem casOp_heightLift (Q : Polynomial ℂ) :
    casOp (heightLift Q) =
      -(X 1 ^ 2 + X 2 ^ 2) * C (1 / 4) * heightLift Q.derivative.derivative -
        X 0 * heightLift Q.derivative := by
  simp only [casOp, rot, Fin.sum_univ_three, Fin.reduceAdd, pderiv_heightLift,
    pderiv_mul, map_sub, pderiv_X, Pi.single_apply, pderiv_C]
  norm_num
  have hc : C (1 / 2 : ℂ) ^ 2 = (C (1 / 4 : ℂ) : MvPolynomial (Fin 3) ℂ) := by
    rw [← map_pow]; congr 1; norm_num
  have ht : C (1 / 2 : ℂ) * 2 = (1 : MvPolynomial (Fin 3) ℂ) := by
    rw [show (2 : MvPolynomial (Fin 3) ℂ) = C (2 : ℂ) by exact (map_ofNat C 2).symm, ← map_mul]; norm_num
  linear_combination -(X 0 * heightLift Q.derivative) * ht -
    ((X 1 ^ 2 + X 2 ^ 2) * heightLift Q.derivative.derivative) * hc
private theorem casOp_sub (p q : MvPolynomial (Fin 3) ℂ) :
    casOp (p - q) = casOp p - casOp q := by
  simp only [casOp, rot, map_sub, mul_sub, Fin.sum_univ_three]
  ring
private theorem eval_heightLift (Q : Polynomial ℂ) (x : Fin 3 → ℂ) :
    eval x (heightLift Q) = Q.eval ((1 - x 0) / 2) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n a => simp [heightLift, Polynomial.aeval_monomial, div_eq_mul_inv]
private theorem sphere_radius (x : Sphere) :
    ((x : Ambient) 0 : ℂ) ^ 2 + ((x : Ambient) 1 : ℂ) ^ 2 +
      ((x : Ambient) 2 : ℂ) ^ 2 = 1 := by
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have h := congrArg (fun t : ℝ => t ^ 2) hn
  rw [EuclideanSpace.real_norm_sq_eq] at h
  norm_num [Fin.sum_univ_three] at h
  exact_mod_cast h

theorem zonal_harmonic_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ x : Sphere, polynomialSphere p x =
      Q.eval ((1 - ((x : Ambient) 0 : ℂ)) / 2)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by
  have hz : ∀ x : Sphere, polynomialSphere (casOp (p - heightLift Q)) x = 0 :=
    casOp_zero _ (by
      intro x
      simp only [polynomialSphere, map_sub, eval_heightLift]
      exact sub_eq_zero.mpr (hQ x))
  have he (x : Sphere) :
      let u : ℂ := (1 - ((x : Ambient) 0 : ℂ)) / 2
      u * (1 - u) * Q.derivative.derivative.eval u +
        (1 - 2 * u) * Q.derivative.eval u +
        ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q.eval u = 0 := by
    have hx := hz x
    rw [casOp_sub, casOp_eigen ℓ p hp, casOp_heightLift] at hx
    simp only [polynomialSphere, map_sub, map_mul, map_add, map_neg, map_pow,
      eval_C, eval_X, smul_eq_C_mul, eval_heightLift] at hx
    rw [show eval (fun i => ((x : Ambient) i : ℂ)) p = _ from hQ x] at hx
    have hr := sphere_radius x
    dsimp
    linear_combination hx - (Q.derivative.derivative.eval
      ((1 - ((x : Ambient) 0 : ℂ)) / 2) / 4) * hr
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := Complex.ofReal '' Set.Icc (0 : ℝ) 1)
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hh := he (latitudePoint (.refl ℝ Ambient) u 0)
    have hc : ((latitudePoint (.refl ℝ Ambient) u 0 : Ambient) 0 : ℂ) = 1 - 2 * (u : ℂ) := by
      rw [latitudePoint_val _ _ _ hu]
      simp [latitudeAmbient, Complex.ofReal_sub, Complex.ofReal_mul]
    dsimp at hh
    rw [hc, show (1 - (1 - 2 * (u : ℂ))) / 2 = (u : ℂ) by ring] at hh
    simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul] using hh
  · exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn

noncomputable def spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

private theorem pderiv_spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (spinSubst A p) =
      ∑ i, MvPolynomial.C (A i j) * spinSubst A (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [spinSubst]
  | add p q ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add, Finset.sum_add_distrib]
  | mul_X p i ih =>
      simp only [map_mul, spinSubst, MvPolynomial.aeval_X]
      rw [MvPolynomial.pderiv_mul]
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, map_sum, MvPolynomial.pderiv_C, zero_mul, zero_add]
      unfold spinSubst at ih
      rw [ih]
      simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
        Pi.single_apply, mul_add, mul_ite, mul_assoc, mul_comm, mul_left_comm]

private theorem polynomialLaplacian_spinSubst (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (spinSubst A p) = spinSubst A (polynomialLaplacian p) := by
  classical
  simp only [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    map_sum]
  change (∑ j, MvPolynomial.pderiv j (MvPolynomial.pderiv j (spinSubst A p))) =
    ∑ j, spinSubst A (MvPolynomial.pderiv j (MvPolynomial.pderiv j p))
  simp only [pderiv_spinSubst, map_sum, MvPolynomial.pderiv_C_mul]
  simp only [pderiv_spinSubst, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  simp_rw [hA]
  simp

private theorem spinSubst_homogeneous (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (spinSubst A p).IsHomogeneous ℓ := by
  unfold spinSubst
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

private theorem spinSubst_harmonic (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    spinSubst A p ∈ harmonicPolynomials ℓ := by
  refine ⟨spinSubst_homogeneous A p ℓ hp.1, ?_⟩
  change polynomialLaplacian (spinSubst A p) = 0
  rw [polynomialLaplacian_spinSubst A hA]
  have hh : polynomialLaplacian p = 0 := hp.2
  rw [hh, map_zero]

noncomputable def spinMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1,0,0], ![0,(Real.cos t : ℂ),-(Real.sin t : ℂ)],
    ![0,(Real.sin t : ℂ),(Real.cos t : ℂ)]]
private theorem spinMatrix_orthogonal (t : ℝ) (i k : Fin 3) :
    ∑ j, spinMatrix t i j * spinMatrix t k j = if i = k then 1 else 0 := by
  have h : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq t
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at h
  fin_cases i <;> fin_cases k <;> simp [spinMatrix, Fin.sum_univ_three] <;>
    (first | (solve | ring) | (linear_combination h))
private theorem spinSubst_eval (t : ℝ) (p : MvPolynomial (Fin 3) ℂ) (x : Ambient) :
    eval (fun j => (x j : ℂ)) (spinSubst (spinMatrix t) p) =
      eval (fun j => ((rotationFlow 0 t x) j : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [spinSubst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, spinSubst, aeval_X, map_sum, eval_C, eval_X]
    congr 1
    fin_cases i <;> simp [spinMatrix, Fin.sum_univ_three, rotationFlowMap,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] <;> ring
instance sphere_compact : CompactSpace Sphere :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
noncomputable def polyCM : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] C(Sphere, ℂ) where
  toFun p := ⟨polynomialSphere p, (MvPolynomial.continuous_eval p).comp (by fun_prop)⟩
  map_add' p q := by ext x; change polynomialSphere (p + q) x = polynomialSphere p x + polynomialSphere q x; simp [polynomialSphere]
  map_smul' c p := by ext x; change polynomialSphere (c • p) x = c • polynomialSphere p x; simp [polynomialSphere]
noncomputable def spinCM (p : MvPolynomial (Fin 3) ℂ) (t : ℝ) : C(Sphere, ℂ) :=
  ⟨fun x => polynomialSphere p (sphereOrthogonal (rotationFlow 0 t) x),
    (polyCM p).continuous.comp (sphereOrthogonal (rotationFlow 0 t)).continuous⟩
private theorem spinCM_continuous (p : MvPolynomial (Fin 3) ℂ) : Continuous (spinCM p) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun tx : ℝ × Sphere => eval
    (fun j => ((rotationFlow 0 tx.1 (tx.2 : Ambient)) j : ℂ)) p)
  apply (MvPolynomial.continuous_eval p).comp
  apply continuous_pi
  intro j
  fin_cases j <;> simp [rotationFlowMap] <;> fun_prop
private theorem spinCM_integrable (p : MvPolynomial (Fin 3) ℂ) :
    Integrable (spinCM p) angleMeasure :=
  (spinCM_continuous p).integrableOn_Icc.smul_measure (by
    simp [ENNReal.inv_ne_top]; positivity)
private theorem average_harmonic (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    ∃ q ∈ harmonicPolynomials ℓ, ∀ x : Sphere,
      polynomialSphere q x = ∫ t, polynomialSphere p
        (sphereOrthogonal (rotationFlow 0 t) x) ∂angleMeasure := by
  classical
  let H := (harmonicPolynomials ℓ).map polyCM
  haveI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  haveI : FiniteDimensional ℂ (harmonicPolynomials ℓ) :=
    Submodule.finiteDimensional_of_le (show harmonicPolynomials ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ from inf_le_left)
  haveI : FiniteDimensional ℂ H := inferInstance
  have hm (t : ℝ) : spinCM p t ∈ H := by
    refine ⟨spinSubst (spinMatrix t) p,
      spinSubst_harmonic _ (spinMatrix_orthogonal t) ℓ p hp, ?_⟩
    ext x
    exact spinSubst_eval t p x
  have hmass : angleMeasure Set.univ = 1 := by
    rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
    simp only [sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)
  letI : IsProbabilityMeasure angleMeasure := ⟨hmass⟩
  have hmem : (∫ t, spinCM p t ∂angleMeasure) ∈ H :=
    (H.restrictScalars ℝ).convex.integral_mem H.closed_of_finiteDimensional
      (Filter.Eventually.of_forall hm) (spinCM_integrable p)
  obtain ⟨q, hq, he⟩ := hmem
  refine ⟨q, hq, fun x => ?_⟩
  have hex := congrArg (fun f : C(Sphere, ℂ) => f x) he
  exact hex.trans (ContinuousMap.integral_apply (spinCM_integrable p) x)

private lemma latitude_surjective_aux (y : Sphere) :
    ∃ θ : ℝ, latitudePoint (.refl ℝ Ambient)
      ((1 - (y : Ambient) 0) / 2) θ = y := by
  let u := (1 - (y : Ambient) 0) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, hhi⟩ := RawSphereProjection.coordinate_bound y 0
    constructor <;> dsimp [u] <;> linarith
  let z : ℂ := ⟨(y : Ambient) 1, (y : Ambient) 2⟩
  have hn : ‖z‖ = Real.sqrt (4*u*(1-u)) := by
    have hy := mem_sphere_zero_iff_norm.mp y.property
    have hs : (y : Ambient) 0 ^ 2 + ((y : Ambient) 1 ^ 2 + (y : Ambient) 2 ^ 2) = 1 := by
      have h := congrArg (fun t : ℝ => t ^ 2) hy
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ] using h
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq, z]
    dsimp [u]
    ring_nf at hs ⊢
    nlinarith
  refine ⟨z.arg, ?_⟩
  apply Subtype.ext
  rw [latitudePoint_val _ _ _ hu]
  ext i
  fin_cases i
  · simp [latitudeAmbient, u]
    ring
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_cos_arg z
  · simpa [latitudeAmbient, ← hn, z] using Complex.norm_mul_sin_arg z

private lemma angle_shift_aux (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi))
    (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by
  rw [angleMeasure, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  simp_rw [add_comm θ]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm θ] using hf.intervalIntegral_add_eq θ 0

private theorem latitude_flow (u θ t : ℝ) :
    sphereOrthogonal (rotationFlow 0 t) (latitudePoint (.refl ℝ Ambient) u θ) =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp only [sphereOrthogonal_coe, latitudePoint_val _ _ _ hu,
      latitudeAmbient, rotationFlow_apply, rotationFlowMap]
    ext i
    fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring
  · simp only [sphereOrthogonal_coe, latitudePoint, dif_neg hu]
    ext i
    fin_cases i <;> simp [rotationFlowMap, north, PiLp.single_apply]
private theorem latitude_periodic_aux (u : ℝ) :
    Function.Periodic (latitudePoint (.refl ℝ Ambient) u) (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · simp [latitudePoint_val _ _ _ hu, latitudeAmbient, Real.cos_add_two_pi,
      Real.sin_add_two_pi]
  · simp [latitudePoint, hu]

theorem latitude_average_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p
        (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by
  obtain ⟨q, hq, havg⟩ := average_harmonic ℓ p hp
  apply zonal_harmonic_legendre_ode ℓ q hq Q
  intro x
  obtain ⟨θ, hθ⟩ := latitude_surjective_aux x
  let u : ℝ := (1 - (x : Ambient) 0) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, hhi⟩ := RawSphereProjection.coordinate_bound x 0
    constructor <;> dsimp [u] <;> linarith
  rw [havg x]
  have hflow (t : ℝ) : sphereOrthogonal (rotationFlow 0 t) x =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by
    rw [← hθ, latitude_flow]
  simp_rw [hflow]
  have hshift := angle_shift_aux _
    ((latitude_periodic_aux u).comp (polynomialSphere p)) θ
  simp only [Function.comp_apply] at hshift
  rw [hshift, hQ u hu]
  congr 1
  simp [u, Complex.ofReal_div, Complex.ofReal_sub]

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
