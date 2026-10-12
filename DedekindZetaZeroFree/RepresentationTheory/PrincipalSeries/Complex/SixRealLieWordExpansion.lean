module

public import DedekindZetaZeroFree.Eisenstein.Sections.SmoothIwasawaLogNorm
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicClearing

@[expose] public section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

def slotLieMatrix (i : Fin 3) (j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  let z : Fin 3 → ℂ := fun k => if k = i then (if j = 0 then 1 else Complex.I) else 0
  !![z 0, z 1; z 2, -z 0]

private theorem complex_spherical_twist (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2) :
    Complex.exp (s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ)) *
      KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter g =
        KPContHolomorphicKGeneration.complexSpherical s g := by
  have hr : 0 < ‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
      (‖g 1 0‖^2+‖g 1 1‖^2) := by
    have hsq := KPContFlatLogNormSmooth.complexMatrixLogNorm_argument_pos g
    have hn : 0 ≤ ‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
        (‖g 1 0‖^2+‖g 1 1‖^2) := by positivity
    nlinarith
  rw [← KPContHolomorphicKGeneration.complexSpherical_zero]
  unfold KPContFlatLogNormSmooth.complexMatrixLogNorm KPContHolomorphicKGeneration.complexSpherical
  dsimp only [KPCplxPrincipalSeriesCharts.bottomRowNormSq]
  rw [Real.log_pow, ← Complex.exp_add]
  push_cast
  congr 1
  change s * (2 * (Real.log (‖((g : Matrix (Fin 2) (Fin 2) ℂ).det)‖ /
    (‖g 1 0‖^2+‖g 1 1‖^2)) : ℂ)) + _ = _
  have hdet : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det := rfl
  rw [hdet]
  ring

private theorem spherical_word_matrix_smooth (w : KPContHolomorphicKGeneration.RealLieWord) (s : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (KPCplxPrincipalSeriesCharts.matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s))
      {g | g.det ≠ 0} := by
  obtain ⟨n,p,h,hh,he⟩ := ActualRaisingLocal.sphericalWord_polynomial_smooth_factors w
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun g => s * (KPContFlatLogNormSmooth.complexMatrixLogNorm g : ℂ)) {g | g.det ≠ 0} := by
    apply ContDiffOn.mul contDiffOn_const
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KPContFlatLogNormSmooth.complexMatrixLogNorm_contDiffOn.of_le (by simp))
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ _).mp
    (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter).property).2
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun g => ∑ j, (p j).eval s * h j g) {g | g.det ≠ 0} := by
    apply ContDiffOn.sum
    intro j hj
    exact contDiffOn_const.mul (hh j)
  apply ((hs.cexp.mul hf).mul hsum).congr
  intro g hg
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg
  have hm (f : KPCplxCharacterHaar.ComplexGL2 → ℂ) :
      KPCplxPrincipalSeriesCharts.matrixFunction f g = f a := by
    simp only [KPCplxPrincipalSeriesCharts.matrixFunction]
    rw [dite_eq_left (show g.det ≠ 0 from hg)]
  rw [hm, he, ← complex_spherical_twist]
  rw [hm (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter)]
  rfl

 def tracelessCoordinates (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![(X 0 0 - X 1 1)/2, X 0 1, X 1 0]

private theorem matrix_six_real_decomposition (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X = ((X 0 0 + X 1 1)/2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ∑ i : Fin 3, ∑ j : Fin 2,
        (if j = 0 then (tracelessCoordinates X i).re else (tracelessCoordinates X i).im) •
          slotLieMatrix i j := by
  have hz (z : ℂ) : (z.re : ℂ) + (z.im : ℂ)*Complex.I = z := by
    exact Complex.re_add_im z
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_succ, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      slotLieMatrix, tracelessCoordinates, Complex.real_smul] <;>
    try simp only [hz]
  all_goals apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] <;> ring

 abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
 abbrev CGL := KPCplxCharacterHaar.ComplexGL2
 abbrev ambient := KPCplxPrincipalSeriesCharts.matrixFunction

private theorem ambient_gl (f : CGL → ℂ) (g : CGL) : ambient f (g : Mat) = f g := by
  simp only [KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dite_eq_left (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl

private theorem ambient_scalar (f : CGL → ℂ)
    (hf : ∀ (c : ℂˣ) (g : CGL), f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = f g)
    (c : ℂˣ) (g : Mat) : ambient f ((c : ℂ) • g) = ambient f g := by
  by_cases hg : g.det = 0
  · have hc : ((c : ℂ) • g).det = 0 := by rw [Matrix.det_smul, hg]; simp
    simp [ambient, KPCplxPrincipalSeriesCharts.matrixFunction, hg, hc]
  · let a := Matrix.GeneralLinearGroup.mkOfDetNeZero g hg
    have he : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * a : CGL) : Mat) = (c : ℂ) • g := by
      ext i j
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_mul, a]
    rw [← he, ambient_gl, hf]
    exact (ambient_gl f a).symm

private theorem spherical_scalar (s : ℂ) (c : ℂˣ) (g : CGL) :
    KPContHolomorphicKGeneration.complexSpherical s (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) =
      KPContHolomorphicKGeneration.complexSpherical s g := by
  rw [← complex_spherical_twist, ← complex_spherical_twist,
    KPContFlatLogNormSmooth.complexMatrixLogNorm_scalar,
    KPCplxPrincipalSeriesCharts.central_invariance]

private theorem right_scalar (f : CGL → ℂ) (X : Mat)
    (hf : ∀ (c : ℂˣ) (g : CGL), f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = f g)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (ambient f) {g | g.det ≠ 0})
    (c : ℂˣ) (g : CGL) :
    KPContHolomorphicKGeneration.rightLieFunction X f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) =
      KPContHolomorphicKGeneration.rightLieFunction X f g := by
  let L : Mat →L[ℝ] Mat := ((c : ℂ) • (ContinuousLinearMap.id ℂ Mat)).restrictScalars ℝ
  have hco : ambient f ∘ L = ambient f := funext (ambient_scalar f hf c)
  have hg : DifferentiableAt ℝ (ambient f) (g : Mat) :=
    (hs.contDiffAt ((isOpen_ne.preimage (by fun_prop : Continuous (fun g : Mat => g.det))).mem_nhds
      (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp)
  have hcg : DifferentiableAt ℝ (ambient f) (L (g : Mat)) := by
    apply (hs.contDiffAt ((isOpen_ne.preimage (by fun_prop : Continuous (fun g : Mat => g.det))).mem_nhds _)).differentiableAt (by simp)
    change ((c : ℂ) • (g : Mat)).det ≠ 0
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero c)) (Matrix.GeneralLinearGroup.det_ne_zero g)
  have he := (hcg.hasFDerivAt.comp (g : Mat) L.hasFDerivAt).fderiv
  rw [hco] at he
  have hx := congrArg (fun D : Mat →L[ℝ] ℂ => D ((g : Mat)*X)) he
  unfold KPContHolomorphicKGeneration.rightLieFunction
  have hmat : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : CGL) : Mat) = L (g : Mat) := by
    ext i j
    simp [L, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [hmat]
  change fderiv ℝ (ambient f) (L (g : Mat)) (L (g : Mat) * X) = _
  have hLX : L (g : Mat) * X = L ((g : Mat) * X) := smul_mul_assoc (c : ℂ) (g : Mat) X
  rw [hLX]
  exact hx.symm

private theorem spherical_word_scalar (W : KPContHolomorphicKGeneration.RealLieWord)
    (s : ℂ) (c : ℂˣ) (g : CGL) :
    KPContHolomorphicKGeneration.complexSphericalWord W s (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) =
      KPContHolomorphicKGeneration.complexSphericalWord W s g := by
  induction W generalizing c g with
  | nil => exact spherical_scalar s c g
  | cons X W ih =>
    exact right_scalar _ X ih (spherical_word_matrix_smooth W s) c g

private theorem central_derivative_zero (f : CGL → ℂ)
    (hf : ∀ (c : ℂˣ) (g : CGL), f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = f g)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) (ambient f) {g | g.det ≠ 0}) (z : ℂ) (g : CGL) :
    fderiv ℝ (ambient f) (g : Mat) (z • (g : Mat)) = 0 := by
  have hg : DifferentiableAt ℝ (ambient f) (g : Mat) :=
    (hs.contDiffAt ((isOpen_ne.preimage (by fun_prop : Continuous (fun g : Mat => g.det))).mem_nhds
      (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)*z) • (g : Mat)) (z • (g : Mat)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [Matrix.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_one,
      zero_mul, add_zero, one_mul] using
      (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z).const_add 1).mul_const ((g : Mat) i j)
  have hne : ∀ᶠ t : ℝ in nhds 0, 1 + (t : ℂ)*z ≠ 0 := by
    exact (by fun_prop : Continuous (fun t : ℝ => 1 + (t : ℂ)*z)).continuousAt.eventually_ne (by simp)
  have he : (fun t : ℝ => ambient f ((1 + (t : ℂ)*z) • (g : Mat))) =ᶠ[nhds 0] fun _ => ambient f (g : Mat) := by
    filter_upwards [hne] with t ht
    exact ambient_scalar f hf (Units.mk0 _ ht) (g : Mat)
  have hd := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have hz := hd.congr_of_eventuallyEq he.symm
  exact hz.unique (hasDerivAt_const 0 (ambient f (g : Mat)))

private theorem right_six (X : Mat) (W : KPContHolomorphicKGeneration.RealLieWord) (s : ℂ) (g : CGL) :
    KPContHolomorphicKGeneration.rightLieFunction X (KPContHolomorphicKGeneration.complexSphericalWord W s) g =
      ∑ i : Fin 3, ∑ j : Fin 2,
        ((if j = 0 then (tracelessCoordinates X i).re else (tracelessCoordinates X i).im) : ℂ) *
          KPContHolomorphicKGeneration.rightLieFunction (slotLieMatrix i j)
            (KPContHolomorphicKGeneration.complexSphericalWord W s) g := by
  unfold KPContHolomorphicKGeneration.rightLieFunction
  let D := fderiv ℝ (ambient (KPContHolomorphicKGeneration.complexSphericalWord W s)) (g : Mat)
  change D ((g : Mat)*X) = _
  conv_lhs => rw [matrix_six_real_decomposition X]
  rw [mul_add, Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_smul_comm]
  rw [D.map_add]
  have hcentral : D (((X 0 0 + X 1 1)/2) • (g : Mat)) = 0 :=
    central_derivative_zero _ (spherical_word_scalar W s) (spherical_word_matrix_smooth W s) _ g
  simp only [mul_one, hcentral, zero_add]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  simp only [Complex.real_smul, smul_eq_mul, apply_ite, Complex.ofReal_re, Complex.ofReal_im]
  rfl

private theorem word_differentiable (W : KPContHolomorphicKGeneration.RealLieWord) (s : ℂ) (g : CGL) :
    DifferentiableAt ℝ (ambient (KPContHolomorphicKGeneration.complexSphericalWord W s)) (g : Mat) :=
  ((spherical_word_matrix_smooth W s).contDiffAt
    ((isOpen_ne.preimage (by fun_prop : Continuous (fun g : Mat => g.det))).mem_nhds
      (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp)

private theorem derivative_word_sum (X : Mat) (W : KPContHolomorphicKGeneration.RealLieWord)
    {n : ℕ} (r : Fin n → List (Fin 3 × Fin 2)) (c : Fin n → ℂ)
    (he : ∀ s g, KPContHolomorphicKGeneration.complexSphericalWord W s g =
      ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord
        ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s g) (s : ℂ) (g : CGL) :
    KPContHolomorphicKGeneration.rightLieFunction X (KPContHolomorphicKGeneration.complexSphericalWord W s) g =
      ∑ j, c j * KPContHolomorphicKGeneration.rightLieFunction X
        (KPContHolomorphicKGeneration.complexSphericalWord ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s) g := by
  have hfun : ambient (KPContHolomorphicKGeneration.complexSphericalWord W s) =
      fun a : Mat => ∑ j, c j * ambient (KPContHolomorphicKGeneration.complexSphericalWord
        ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s) a := by
    funext a
    by_cases ha : a.det ≠ 0
    · let ga := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha
      simpa only [ambient, KPCplxPrincipalSeriesCharts.matrixFunction, dite_eq_left ha] using he s ga
    · simp [ambient, KPCplxPrincipalSeriesCharts.matrixFunction, ha]
  unfold KPContHolomorphicKGeneration.rightLieFunction
  change fderiv ℝ (ambient (KPContHolomorphicKGeneration.complexSphericalWord W s)) (g : Mat) _ = _
  rw [hfun]
  have hdiff := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j hj =>
    ((word_differentiable ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s g).hasFDerivAt.const_mul (c j))))
  have hd := congrArg (fun D : Mat →L[ℝ] ℂ => D ((g : Mat)*X)) hdiff.fderiv
  refine hd.trans ?_
  change (∑ j : Fin n, c j • fderiv ℝ (ambient (KPContHolomorphicKGeneration.complexSphericalWord
    ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s)) (g : Mat)) ((g : Mat)*X) = _
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ContinuousLinearMap.smul_apply]
  rfl

theorem complex_spherical_word_six_real_expansion
    (W : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ (n : ℕ) (r : Fin n → List (Fin 3 × Fin 2)) (c : Fin n → ℂ),
      ∀ (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2),
        KPContHolomorphicKGeneration.complexSphericalWord W s g =
          ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord
            ((r j).map (fun ij => slotLieMatrix ij.1 ij.2)) s g := by
  induction W with
  | nil =>
    refine ⟨1, fun _ => [], fun _ => 1, ?_⟩
    intro s g
    simp [KPContHolomorphicKGeneration.complexSphericalWord]
  | cons X W ih =>
    obtain ⟨n,r,c,he⟩ := ih
    let idx : Type := Fin 3 × Fin 2 × Fin n
    let e := Fintype.equivFin idx
    let rr : idx → List (Fin 3 × Fin 2) := fun k => (k.1,k.2.1) :: r k.2.2
    let cc : idx → ℂ := fun k =>
      ((if k.2.1 = 0 then (tracelessCoordinates X k.1).re else
        (tracelessCoordinates X k.1).im) : ℂ)*c k.2.2
    refine ⟨Fintype.card idx, fun k => rr (e.symm k), fun k => cc (e.symm k), ?_⟩
    intro s g
    change KPContHolomorphicKGeneration.rightLieFunction X
      (KPContHolomorphicKGeneration.complexSphericalWord W s) g = _
    rw [right_six X W s g]
    simp_rw [derivative_word_sum _ W r c he s g, Finset.mul_sum]
    have hsum : (∑ k : idx, cc k * KPContHolomorphicKGeneration.complexSphericalWord
        ((rr k).map (fun ij => slotLieMatrix ij.1 ij.2)) s g) =
        ∑ i : Fin 3, ∑ j : Fin 2, ∑ k : Fin n,
          ((if j = 0 then (tracelessCoordinates X i).re else (tracelessCoordinates X i).im) : ℂ) *
            c k * KPContHolomorphicKGeneration.rightLieFunction (slotLieMatrix i j)
              (KPContHolomorphicKGeneration.complexSphericalWord
                ((r k).map (fun ij => slotLieMatrix ij.1 ij.2)) s) g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.sum_prod_type]
      rfl
    simp_rw [← mul_assoc]
    rw [← hsum]
    exact (Equiv.sum_comp e.symm _).symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

end
