module

public import DedekindZetaZeroFree.Theta.Whittaker.RotatedKernelDerivativeEstimates
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarmonicPolynomials.SymmetricPowerAction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypeDimension

@[expose] public section

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar
open scoped BigOperators

noncomputable def linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

private theorem pderiv_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
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

private theorem polynomialLaplacian_linearSubstitution (A : Matrix (Fin 3) (Fin 3) ℂ)
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

private theorem linearSubstitution_homogeneous (A : Matrix (Fin 3) (Fin 3) ℂ)
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (linearSubstitution A p).IsHomogeneous ℓ := by
  unfold linearSubstitution
  simpa using hp.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)
    (fun i => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun j _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _))

private theorem linearSubstitution_harmonic (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    linearSubstitution A p ∈ harmonicPolynomials ℓ := by
  refine ⟨linearSubstitution_homogeneous A p ℓ hp.1, ?_⟩
  change polynomialLaplacian (linearSubstitution A p) = 0
  rw [polynomialLaplacian_linearSubstitution A hA]
  have hh : polynomialLaplacian p = 0 := hp.2
  rw [hh, map_zero]

private theorem su2_entries (k : ComplexSU2) : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ∧
  (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have ha : star m = Matrix.adjugate m := by
    calc
      star m = 1 * star m := by simp
      _ = (Matrix.adjugate m * m) * star m := by rw [Matrix.adjugate_mul, hd]; simp
      _ = Matrix.adjugate m * (m * star m) := by rw [mul_assoc]
      _ = Matrix.adjugate m := by rw [hu]; simp
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) ha
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) ha
  simp only [Matrix.star_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h10
  constructor
  · simpa using congrArg star h00
  · simpa using congrArg star h10

private theorem su2_row_norm (k : ComplexSU2) :
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ^ 2 +
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im ^ 2 = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.mul_re, Complex.star_def, Complex.normSq_apply] at h
  nlinarith

noncomputable def hopfMatrix (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => (((!![
    b.re^2-b.im^2-a.re^2+a.im^2, 2*b.re*b.im-2*a.re*a.im, -2*a.re*b.re-2*a.im*b.im;
    -2*b.re*b.im-2*a.re*a.im, b.re^2-b.im^2+a.re^2-a.im^2, -2*a.im*b.re+2*a.re*b.im;
    2*a.re*b.re-2*a.im*b.im, 2*a.re*b.im+2*a.im*b.re, b.re^2+b.im^2-a.re^2-a.im^2]
      : Matrix (Fin 3) (Fin 3) ℝ) i j) : ℂ)

private theorem hopfMatrix_orthogonal (a b : ℂ)
    (h : a.re^2+a.im^2+b.re^2+b.im^2 = 1) (i k : Fin 3) :
    ∑ j, hopfMatrix a b i j * hopfMatrix a b k j = if i = k then 1 else 0 := by
  fin_cases i <;> fin_cases k <;>
    simp [hopfMatrix, Fin.sum_univ_three, ← Complex.ofReal_mul,
      ← Complex.ofReal_add]
  all_goals norm_cast
  all_goals first | (solve | ring) | (calc
    _ = (a.re^2+a.im^2+b.re^2+b.im^2)^2 := by ring
    _ = _ := by rw [h]; norm_num)

private theorem hopfMatrix_action (l k : ComplexSU2) (i : Fin 3) :
    compactSphereCoordinate (l * k) i =
      ∑ j, hopfMatrix ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
        ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) i j * compactSphereCoordinate l j := by
  obtain ⟨h0, h1⟩ := su2_entries k
  fin_cases i <;>
    simp [compactSphereCoordinate, hopfMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, h0, h1,
      Complex.mul_re, Complex.mul_im, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  all_goals ring

theorem harmonicPolynomials_su2_translation (ℓ : ℕ)
    (k : ComplexSU2) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    ∃ q : MvPolynomial (Fin 3) ℂ, q ∈ harmonicPolynomials ℓ ∧
      ∀ h : ComplexSU2,
        MvPolynomial.eval (compactSphereCoordinate (h * k)) p =
          MvPolynomial.eval (compactSphereCoordinate h) q := by
  classical
  let A := hopfMatrix ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  refine ⟨linearSubstitution A p,
    linearSubstitution_harmonic A (hopfMatrix_orthogonal _ _ (su2_row_norm k)) ℓ p hp, ?_⟩
  intro h
  unfold linearSubstitution
  change MvPolynomial.aeval _ p = MvPolynomial.aeval _ (MvPolynomial.aeval _ p)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self]
  exact hopfMatrix_action h k i

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open scoped Matrix.Norms.Elementwise

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
noncomputable def rowB (m : Mat) : ℝ := ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2
noncomputable def rowW (m : Mat) : ℂ := 2 * m 1 0 * star (m 1 1) / (rowB m : ℂ)
noncomputable def rowZ (m : Mat) : ℂ :=
  ((‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ) : ℂ) / (rowB m : ℂ)
noncomputable def rowSphere (m : Mat) : Fin 3 → ℂ :=
  ![(rowW m).re, (rowW m).im, rowZ m]

private theorem rowB_pos (g : ComplexGL2) : 0 < rowB g :=
  KPCplxRotatedKernelEstimates.bottomRowNormSq_pos g

private theorem rowW_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowW {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Mat => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Mat => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowW
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact ((contDiff_const.mul h0).mul (Complex.conjCLE.contDiff.comp h1)).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb |>.contDiffOn)
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'

private theorem rowZ_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowZ {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Mat => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : Mat => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowZ
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact (Complex.ofRealCLM.contDiff.comp ((h0.norm_sq (𝕜 := ℂ)).sub (h1.norm_sq (𝕜 := ℂ)))).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb |>.contDiffOn)
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'

private theorem rowSphere_smooth (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun m => rowSphere m i) {m | m.det ≠ 0} := by
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (Complex.reCLM.contDiff.comp_contDiffOn rowW_smooth)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (Complex.imCLM.contDiff.comp_contDiffOn rowW_smooth)
  · exact rowZ_smooth

private theorem rowB_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowB (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * rowB g := by
  change rowB ((upperTriangular a d b : Mat) * (g : Mat)) = _
  change rowB (!![(a : ℂ), b; 0, (d : ℂ)] * (g : Mat)) = _
  simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, mul_add]

private theorem rowW_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowW (upperTriangular a d b * g) = rowW g := by
  unfold rowW
  rw [rowB_left]
  change 2 * ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Mat)) 1 0) *
    star ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : Mat)) 1 1) /
    (‖(d : ℂ)‖ ^ 2 * rowB g : ℝ) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change 2 * ((0 : ℂ) * (g : Mat) 0 0 + (d : ℂ) * (g : Mat) 1 0) *
    star ((0 : ℂ) * (g : Mat) 0 1 + (d : ℂ) * (g : Mat) 1 1) / _ = _
  simp only [zero_mul, zero_add, star_mul]
  rw [show 2 * ((d : ℂ) * (g : Mat) 1 0) * (star ((g : Mat) 1 1) * star (d : ℂ)) =
    ((d : ℂ) * star (d : ℂ)) * (2 * (g : Mat) 1 0 * star ((g : Mat) 1 1)) by ring]
  simp only [Complex.star_def, Complex.mul_conj']
  push_cast
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero)))

private theorem rowZ_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowZ (upperTriangular a d b * g) = rowZ g := by
  unfold rowZ
  rw [rowB_left]
  change ((‖(!![(a : ℂ), b; 0, (d : ℂ)] * (g : Mat)) 1 0‖ ^ 2 -
    ‖(!![(a : ℂ), b; 0, (d : ℂ)] * (g : Mat)) 1 1‖ ^ 2 : ℝ) : ℂ) / _ = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change ((‖(0 : ℂ) * (g : Mat) 0 0 + (d : ℂ) * (g : Mat) 1 0‖ ^ 2 -
    ‖(0 : ℂ) * (g : Mat) 0 1 + (d : ℂ) * (g : Mat) 1 1‖ ^ 2 : ℝ) : ℂ) / _ = _
  simp only [zero_mul, zero_add, norm_mul, mul_pow, ← mul_sub]
  push_cast
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero)))

private theorem rowSphere_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowSphere (upperTriangular a d b * g) = rowSphere g := by
  simp only [rowSphere, rowW_left, rowZ_left]

private theorem polynomial_smooth (p : MvPolynomial (Fin 3) ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun m => MvPolynomial.eval (rowSphere m) p) {m | m.det ≠ 0} := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using contDiffOn_const (c := c)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (rowSphere_smooth i)

noncomputable def polynomialFunction (s : ℝ) (p : MvPolynomial (Fin 3) ℂ)
    (g : ComplexGL2) : ℂ := sphericalSection s g * MvPolynomial.eval (rowSphere g) p

private theorem polynomialFunction_mem (s : ℝ) (p : MvPolynomial (Fin 3) ℂ) :
    polynomialFunction s p ∈ principalSeriesSubmodule s := by
  apply (principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have hc := (sphericalSection s).property.1 a d b g
    unfold polynomialFunction
    rw [hc]
    simp only [Matrix.GeneralLinearGroup.coe_mul, rowSphere_left]
    ring
  · have hs := ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
    have hh := hs.mul (polynomial_smooth p)
    apply hh.congr
    intro m hm
    change m.det ≠ 0 at hm
    simp only [matrixFunction, dif_pos hm, polynomialFunction]
    rfl

private theorem rowB_compact (k : ComplexSU2) : rowB k = 1 := by
  have hrow := congrArg (fun B : Mat => (B 1 1).re)
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hrow
  change (((k : Mat) 1 0 * (starRingEnd ℂ) ((k : Mat) 1 0)) +
    ((k : Mat) 1 1 * (starRingEnd ℂ) ((k : Mat) 1 1))).re = 1 at hrow
  simpa only [rowB, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] using hrow

private theorem spherical_compact (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change (Real.rpow (‖(k : Mat).det‖ / rowB k) (1 + 2 * s) : ℂ) = 1
  rw [hd, rowB_compact]; simp

private theorem rowSphere_compact (k : ComplexSU2) : rowSphere k = compactSphereCoordinate k := by
  ext i
  fin_cases i <;> simp [rowSphere, rowW, rowZ, rowB_compact, compactSphereCoordinate,
    Complex.mul_re, Complex.mul_im] <;> ring

theorem polynomialCompactHarmonics_extend (s : ℝ) (ℓ : ℕ) :
    (harmonicPolynomials ℓ).map polynomialCompactRestriction ≤
      (compactRestriction s).range := by
  rintro f ⟨p, hp, rfl⟩
  refine ⟨⟨polynomialFunction s p, polynomialFunction_mem s p⟩, ?_⟩
  ext k
  change sphericalSection s (complexSU2Embedding k) * MvPolynomial.eval (rowSphere k) p =
    MvPolynomial.eval (compactSphereCoordinate k) p
  rw [spherical_compact, rowSphere_compact, one_mul]

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HighestWeightOrbit
open KPCplxCharacterHaar

noncomputable def highestWeightCompactHarmonic (ℓ : ℕ) : ComplexSU2 → ℂ :=
  polynomialCompactRestriction
    ((MvPolynomial.X (0 : Fin 3) +
      MvPolynomial.C Complex.I * MvPolynomial.X (1 : Fin 3)) ^ ℓ)

noncomputable def highestWeightIsotropicLinearPolynomial : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1
private theorem highestWeightIsotropicPower_directionalDerivative_eq_zero (ℓ : ℕ) :
    MvPolynomial.pderiv 0 (highestWeightIsotropicLinearPolynomial ^ ℓ) +
      MvPolynomial.C Complex.I * MvPolynomial.pderiv 1 (highestWeightIsotropicLinearPolynomial ^ ℓ) = 0 := by
  simp only [MvPolynomial.pderiv_pow]
  simp [highestWeightIsotropicLinearPolynomial, MvPolynomial.pderiv_C_mul, Pi.single_apply]
  have hI : (MvPolynomial.C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow]; norm_num
  linear_combination (ℓ : MvPolynomial (Fin 3) ℂ) *
    (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1) ^ (ℓ - 1) * hI
private theorem highestWeightIsotropicPower_mem_harmonicPolynomials (ℓ : ℕ) : highestWeightIsotropicLinearPolynomial ^ ℓ ∈ harmonicPolynomials ℓ := by
  refine ⟨?_, ?_⟩
  · simpa [highestWeightIsotropicLinearPolynomial] using ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 3)).add
      ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).pow ℓ
  · change polynomialLaplacian (highestWeightIsotropicLinearPolynomial ^ ℓ) = 0
    have hmul (p : MvPolynomial (Fin 3) ℂ) :
        polynomialLaplacian (highestWeightIsotropicLinearPolynomial * p) = highestWeightIsotropicLinearPolynomial * polynomialLaplacian p +
          2 * (MvPolynomial.pderiv 0 p + MvPolynomial.C Complex.I * MvPolynomial.pderiv 1 p) := by
      simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
        Fin.sum_univ_succ, highestWeightIsotropicLinearPolynomial, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C_mul]
      ring
    induction ℓ with
    | zero => simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply]
    | succ n ih =>
      rw [pow_succ', hmul, ih, highestWeightIsotropicPower_directionalDerivative_eq_zero]
      simp

theorem highestWeightCompactHarmonic_mem_orbit_span (ℓ : ℕ)
    (v : ComplexSU2 → ℂ)
    (hv : v ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction)
    (hne : v ≠ 0) :
    highestWeightCompactHarmonic ℓ ∈
      Submodule.span ℂ (Set.range (fun k : ComplexSU2 => fun h => v (h * k))) := by
  classical
  obtain ⟨p, hp, hpv⟩ := hv
  let u : HarmonicVendor.Harmonic ℓ := ⟨p, hp⟩
  let ρ := HarmonicVendor.harmonicRepresentation ℓ
  obtain ⟨e⟩ := HarmonicVendor.harmonic_equiv_symPower ℓ
  haveI : ρ.IsIrreducible :=
    Representation.isIrreducible_of_linearEquiv e.symm.toLinearEquiv
      (fun g w => congrArg (fun f => f w) (e.symm.isIntertwining' g))
      (TauCeti.SU2.isIrreducible_symPower (2 * ℓ))
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g : ComplexSU2 => ρ g u))
      apply_mem_toSubmodule g w hw := by
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k, rfl⟩ := hw
          change ((ρ g * ρ k) u) ∈ _
          rw [← map_mul]
          exact Submodule.subset_span ⟨g * k, rfl⟩
        | zero => simp
        | add a b ha hb ia ib => simpa using Submodule.add_mem _ ia ib
        | smul c a ha ia => simpa using Submodule.smul_mem _ c ia }
  have hu : u ∈ W.toSubmodule := by
    change u ∈ Submodule.span ℂ (Set.range (fun g : ComplexSU2 => ρ g u))
    have h : ρ 1 u ∈ Submodule.span ℂ (Set.range (fun g : ComplexSU2 => ρ g u)) :=
      Submodule.subset_span ⟨1, rfl⟩
    simpa only [map_one, Module.End.one_apply] using h
  have htop : W = ⊤ := by
    rcases eq_bot_or_eq_top W with hbot | htop
    · have hz : u = 0 := by simpa [hbot] using hu
      exfalso
      apply hne
      rw [← hpv]
      have hpz : p = 0 := congrArg Subtype.val hz
      simp [hpz]
    · exact htop
  let r : HarmonicVendor.Harmonic ℓ →ₗ[ℂ] (ComplexSU2 → ℂ) :=
    polynomialCompactRestriction.comp (harmonicPolynomials ℓ).subtype
  have hmap : W.toSubmodule.map r =
      Submodule.span ℂ (Set.range (fun k : ComplexSU2 => fun h => v (h * k))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span ℂ)
    apply congrArg Set.range
    funext k h
    change polynomialCompactRestriction (ρ k u) h = v (h * k)
    rw [HarmonicVendor.harmonicRepresentation_restriction]
    exact congrFun hpv (h * k)
  rw [← hmap]
  exact ⟨⟨highestWeightIsotropicLinearPolynomial ^ ℓ, highestWeightIsotropicPower_mem_harmonicPolynomials ℓ⟩,
    by rw [htop]; trivial, rfl⟩

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HighestWeightOrbit

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HighestWeightOrbit
open KPCplxCharacterHaar MeasureTheory
open scoped BigOperators

theorem cyclic_of_extraction {G E : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : G → E →ₗ[ℂ] E)
    (hρ : ∀ g h v, ρ (g * h) v = ρ g (ρ h v))
    (h1 : ∀ v, ρ 1 v = v)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (w : E) (hw : w ≠ 0)
    (hextract : ∀ v : E, v ≠ 0 → w ∈ Submodule.span ℂ (Set.range (fun g => ρ g v))) :
    Submodule.span ℂ (Set.range (fun g => ρ g w)) = ⊤ := by
  classical
  let W := Submodule.span ℂ (Set.range (fun g => ρ g w))
  apply W.orthogonal_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  by_contra hne
  have horbit : Submodule.span ℂ (Set.range (fun g => ρ g v)) ≤ Wᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    apply (W.mem_orthogonal _).mpr
    intro u hu
    have hinv : ρ g⁻¹ u ∈ W := by
      induction hu using Submodule.span_induction with
      | mem u hu =>
        rcases hu with ⟨k, rfl⟩
        rw [← hρ]
        exact Submodule.subset_span ⟨g⁻¹ * k, rfl⟩
      | zero => simpa using W.zero_mem
      | add u z hu hz ihu ihz => simpa using W.add_mem ihu ihz
      | smul c u hu ih => simpa using W.smul_mem c ih
    have he : ρ g (ρ g⁻¹ u) = u := by rw [← hρ, mul_inv_cancel, h1]
    rw [← he, hunit]
    exact (W.mem_orthogonal _).mp hv _ hinv
  have hwo : w ∈ Wᗮ := horbit (hextract v hne)
  have hww : w ∈ W := by
    have := Submodule.subset_span (R := ℂ) (s := Set.range (fun g => ρ g w)) ⟨1, rfl⟩
    simpa [h1] using this
  exact hw (by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    exact (W.mem_orthogonal _).mp hwo w hww)

private theorem restriction_cont (p : MvPolynomial (Fin 3) ℂ) :
    Continuous (polynomialCompactRestriction p) := by
  apply p.continuous_eval.comp
  have hc : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ =>
      ![(2 * (m 1 0 * star (m 1 1)).re : ℝ),
        (2 * (m 1 0 * star (m 1 1)).im : ℝ),
        (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)] : Matrix (Fin 2) (Fin 2) ℂ → Fin 3 → ℂ) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact hc.comp continuous_subtype_val
private theorem harmonic_cont (ℓ : ℕ) (v : (harmonicPolynomials ℓ).map polynomialCompactRestriction) :
    Continuous (v : ComplexSU2 → ℂ) := by
  obtain ⟨p, hp, he⟩ := v.property
  rw [← he]
  exact restriction_cont p
private theorem harmonic_finite (ℓ : ℕ) :
    FiniteDimensional ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  letI : FiniteDimensional ℂ (harmonicPolynomials ℓ) :=
    Submodule.finiteDimensional_of_le (show harmonicPolynomials ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ from inf_le_left)
  infer_instance
private theorem harmonic_stable (ℓ : ℕ) (k : ComplexSU2)
    (v : (harmonicPolynomials ℓ).map polynomialCompactRestriction) :
    (fun h => (v : ComplexSU2 → ℂ) (h * k)) ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction := by
  obtain ⟨p, hp, he⟩ := v.property
  obtain ⟨q, hq, heq⟩ := harmonicPolynomials_su2_translation ℓ k p hp
  refine ⟨q, hq, ?_⟩
  ext h
  exact (heq h).symm.trans (congrFun he (h * k))
noncomputable def highestWeightNullLinearPolynomial : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1
private theorem highestWeightNullLinearPolynomial_pow_nullDirectionalDerivative_eq_zero (ℓ : ℕ) :
    MvPolynomial.pderiv 0 (highestWeightNullLinearPolynomial ^ ℓ) +
      MvPolynomial.C Complex.I * MvPolynomial.pderiv 1 (highestWeightNullLinearPolynomial ^ ℓ) = 0 := by
  simp only [MvPolynomial.pderiv_pow]
  simp [highestWeightNullLinearPolynomial, MvPolynomial.pderiv_C_mul, Pi.single_apply]
  have hI : (MvPolynomial.C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow]; norm_num
  linear_combination (ℓ : MvPolynomial (Fin 3) ℂ) *
    (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1) ^ (ℓ - 1) * hI
private theorem highestWeightNullLinearPolynomial_pow_mem_harmonicPolynomials (ℓ : ℕ) : highestWeightNullLinearPolynomial ^ ℓ ∈ harmonicPolynomials ℓ := by
  refine ⟨?_, ?_⟩
  · simpa [highestWeightNullLinearPolynomial] using ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 3)).add
      ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).pow ℓ
  · change polynomialLaplacian (highestWeightNullLinearPolynomial ^ ℓ) = 0
    have hmul (p : MvPolynomial (Fin 3) ℂ) :
        polynomialLaplacian (highestWeightNullLinearPolynomial * p) = highestWeightNullLinearPolynomial * polynomialLaplacian p +
          2 * (MvPolynomial.pderiv 0 p + MvPolynomial.C Complex.I * MvPolynomial.pderiv 1 p) := by
      simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
        Fin.sum_univ_succ, highestWeightNullLinearPolynomial, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C_mul]
      ring
    induction ℓ with
    | zero => simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply]
    | succ n ih =>
      rw [pow_succ', hmul, ih, highestWeightNullLinearPolynomial_pow_nullDirectionalDerivative_eq_zero]
      simp
private theorem highest_mem (ℓ : ℕ) : highestWeightCompactHarmonic ℓ ∈
    (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
  ⟨highestWeightNullLinearPolynomial ^ ℓ, highestWeightNullLinearPolynomial_pow_mem_harmonicPolynomials ℓ, rfl⟩
private theorem highest_ne (ℓ : ℕ) : highestWeightCompactHarmonic ℓ ≠ 0 := by
  let r : ℝ := Real.sqrt 2 / 2
  have hr2 : r ^ 2 = 1 / 2 := by dsimp [r]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrc : (r : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, hr2]
    norm_num
  let k : ComplexSU2 := ⟨!![(r : ℂ), -(r : ℂ); (r : ℂ), (r : ℂ)], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
      all_goals linear_combination 2 * hrc
    · simp [Matrix.det_fin_two]
      linear_combination 2 * hrc⟩
  have he : highestWeightCompactHarmonic ℓ k = 1 := by
    simp [highestWeightCompactHarmonic, polynomialCompactRestriction,
      compactSphereCoordinate, k, Complex.mul_re, Complex.mul_im,
      ← Complex.ofReal_pow, hr2, ← pow_two, hrc]
  intro hz
  have hh := congrFun hz k
  rw [he] at hh
  exact one_ne_zero hh

theorem highestWeightCompactHarmonic_orbit_span (ℓ : ℕ) :
    (harmonicPolynomials ℓ).map polynomialCompactRestriction ≤
      Submodule.span ℂ (Set.range (fun k : ComplexSU2 => fun h =>
        highestWeightCompactHarmonic ℓ (h * k))) := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : ContinuousInv ComplexSU2 := ⟨by
    apply continuous_induced_rng.mpr
    change Continuous (fun k : ComplexSU2 => star (k : Matrix (Fin 2) (Fin 2) ℂ))
    exact continuous_star.comp continuous_subtype_val⟩
  letI : IsTopologicalGroup ComplexSU2 := {}
  letI : MeasurableSpace ComplexSU2 := borel ComplexSU2
  letI : BorelSpace ComplexSU2 := ⟨rfl⟩
  let μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts ComplexSU2)
  letI : μ.IsHaarMeasure := inferInstance
  let ν := μ.inv
  haveI : IsFiniteMeasure ν := inferInstance
  haveI : ν.IsOpenPosMeasure := inferInstance
  haveI : ν.IsMulRightInvariant := inferInstance
  classical
  let H := (harmonicPolynomials ℓ).map polynomialCompactRestriction
  letI := harmonic_finite ℓ
  let c : H →ₗ[ℂ] C(ComplexSU2, ℂ) :=
    { toFun := fun v => ⟨v.val, harmonic_cont ℓ v⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  let f : H →ₗ[ℂ] Lp ℂ 2 ν := (ContinuousMap.toLp 2 ν ℂ).toLinearMap.comp c
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact congrArg (fun u : C(ComplexSU2, ℂ) => (u : ComplexSU2 → ℂ))
      (ContinuousMap.toLp_injective ν hvw)
  letI := NormedAddCommGroup.induced H _ f hf
  letI := NormedSpace.induced ℂ H _ f
  letI : InnerProductSpace ℂ H := InnerProductSpace.induced f
  let ρ : ComplexSU2 → H →ₗ[ℂ] H := fun k =>
    { toFun := fun v => ⟨fun h => v.val (h * k), harmonic_stable ℓ k v⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hρ (g k : ComplexSU2) (v : H) : ρ (g * k) v = ρ g (ρ k v) := by
    apply Subtype.ext
    ext h
    exact congrArg v.val (mul_assoc h g k).symm
  have h1 (v : H) : ρ 1 v = v := by
    apply Subtype.ext
    ext h
    exact congrArg v.val (mul_one h)
  have hunit (g : ComplexSU2) (v w : H) :
      inner ℂ (ρ g v) (ρ g w) = inner ℂ v w := by
    change inner ℂ (f (ρ g v)) (f (ρ g w)) = inner ℂ (f v) (f w)
    simp only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
    exact integral_mul_right_eq_self (fun h => w.val h * star (v.val h)) g
  let w : H := ⟨highestWeightCompactHarmonic ℓ, highest_mem ℓ⟩
  have hw : w ≠ 0 := by
    intro hz
    exact highest_ne ℓ (congrArg Subtype.val hz)
  have hextract (v : H) (hv : v ≠ 0) :
      w ∈ Submodule.span ℂ (Set.range (fun g => ρ g v)) := by
    have hv' : v.val ≠ 0 := by
      intro hz
      exact hv (Subtype.ext hz)
    have he := highestWeightCompactHarmonic_mem_orbit_span ℓ v.val v.property hv'
    have hm : (Submodule.span ℂ (Set.range (fun g => ρ g v))).map H.subtype =
        Submodule.span ℂ (Set.range (fun g => fun h => v.val (h * g))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hm] at he
    obtain ⟨x, hx, hxe⟩ := he
    have hew : x = w := Subtype.ext hxe
    exact hew ▸ hx
  have hc := cyclic_of_extraction ρ hρ h1 hunit w hw hextract
  intro v hv
  have hsub : (Submodule.span ℂ (Set.range (fun g => ρ g w))).map H.subtype =
      Submodule.span ℂ (Set.range (fun g => fun h => highestWeightCompactHarmonic ℓ (h * g))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hsub]
  exact ⟨⟨v, hv⟩, by rw [hc]; trivial, rfl⟩

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HighestWeightOrbit

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar

theorem polynomialCompactHarmonics_zero_eq_span :
    (harmonicPolynomials 0).map polynomialCompactRestriction =
      Submodule.span ℂ {(1 : ComplexSU2 → ℂ)} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    have hc : p = MvPolynomial.C (p.coeff 0) := by
      rw [← MvPolynomial.homogeneousComponent_zero p]
      exact (MvPolynomial.homogeneousComponent_eq_self hp.1).symm
    rw [hc]
    have he : polynomialCompactRestriction (MvPolynomial.C (p.coeff 0)) =
        (p.coeff 0) • (1 : ComplexSU2 → ℂ) := by
      ext k
      simp [polynomialCompactRestriction]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    apply Submodule.mem_map.mpr
    refine ⟨1, ?_, ?_⟩
    · constructor
      · exact MvPolynomial.isHomogeneous_one (Fin 3) ℂ
      · simp [LinearMap.mem_ker, polynomialLaplacian, LinearMap.sum_apply,
          LinearMap.comp_apply]
    · ext k
      simp [polynomialCompactRestriction]

theorem polynomialCompactHarmonics_zero_irreducible
    (V : Submodule ℂ (ComplexSU2 → ℂ))
    (hV : V ≤ (harmonicPolynomials 0).map polynomialCompactRestriction) :
    V = ⊥ ∨ V = (harmonicPolynomials 0).map polynomialCompactRestriction := by
  classical
  by_cases hzero : V = ⊥
  · exact Or.inl hzero
  · right
    rw [polynomialCompactHarmonics_zero_eq_span] at hV ⊢
    apply (nonzero_span_atom (1 : ComplexSU2 → ℂ) ?_).le_iff_eq hzero |>.mp hV
    intro h
    have := congrFun h 1
    simp at this

theorem polynomialCompactHarmonics_irreducible (ℓ : ℕ)
    (V : Submodule ℂ (ComplexSU2 → ℂ))
    (hV : V ≤ (harmonicPolynomials ℓ).map polynomialCompactRestriction)
    (hstable : ∀ (k : ComplexSU2) (v : ComplexSU2 → ℂ), v ∈ V →
      (fun h => v (h * k)) ∈ V) :
    V = ⊥ ∨ V = (harmonicPolynomials ℓ).map polynomialCompactRestriction := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact polynomialCompactHarmonics_zero_irreducible V hV
  · classical
    by_cases hb : V = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨v, hv, hne⟩ := V.ne_bot_iff.mp hb
      have hspan : Submodule.span ℂ
          (Set.range (fun k : ComplexSU2 => fun h => v (h * k))) ≤ V := by
        apply Submodule.span_le.mpr
        rintro w ⟨k, rfl⟩
        exact hstable k v hv
      have hhighest : HighestWeightOrbit.highestWeightCompactHarmonic ℓ ∈ V :=
        hspan (HighestWeightOrbit.highestWeightCompactHarmonic_mem_orbit_span
          ℓ v (hV hv) hne)
      apply le_antisymm hV
      refine (HighestWeightOrbit.highestWeightCompactHarmonic_orbit_span ℓ).trans
        (Submodule.span_le.mpr ?_)
      rintro w ⟨k, rfl⟩
      exact hstable k _ hhighest

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

theorem compactRestriction_pi_su2 (s : ℝ) (k h : ComplexSU2) (f : PrincipalSeries s) :
    compactRestriction s (pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) f) h =
      compactRestriction s f (h * k) := by
  rw [pi_mk]
  change f (complexSU2Embedding h * complexSU2Embedding k) = f (complexSU2Embedding (h * k))
  rw [map_mul]

theorem harmonicKType_mem_iff (s : ℝ) (ℓ : ℕ) (f : PrincipalSeries s) :
    f ∈ harmonicKType s ℓ ↔ ∃ p : MvPolynomial (Fin 3) ℂ,
      p ∈ harmonicPolynomials ℓ ∧ ∀ k : ComplexSU2,
        f (complexSU2Embedding k) = MvPolynomial.eval (compactSphereCoordinate k) p := by
  change compactRestriction s f ∈ (harmonicPolynomials ℓ).map polynomialCompactRestriction ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, fun k => (congrFun he k).symm⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, funext fun k => (he k).symm⟩

theorem harmonicKType_invariant_of_polynomial_translation (s : ℝ) (ℓ : ℕ)
    (hstable : ∀ (k : ComplexSU2) (p : MvPolynomial (Fin 3) ℂ),
      p ∈ harmonicPolynomials ℓ → ∃ q : MvPolynomial (Fin 3) ℂ,
        q ∈ harmonicPolynomials ℓ ∧ ∀ h : ComplexSU2,
          MvPolynomial.eval (compactSphereCoordinate (h * k)) p =
            MvPolynomial.eval (compactSphereCoordinate h) q) :
    IsKInvariant s (harmonicKType s ℓ) := by
  intro k f hf
  obtain ⟨k', hk'⟩ := k.property
  obtain ⟨p, hp, hfp⟩ := (harmonicKType_mem_iff s ℓ f).mp hf
  obtain ⟨q, hq, hpq⟩ := hstable k' p hp
  apply (harmonicKType_mem_iff s ℓ _).mpr
  refine ⟨q, hq, ?_⟩
  intro h
  change compactRestriction s (pi s (k : ComplexPGL2) f) h = _
  rw [← hk']
  change compactRestriction s (pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k')) f) h = _
  rw [compactRestriction_pi_su2]
  exact (hfp (h * k')).trans (hpq h)

theorem harmonicPolynomials_finiteDimensional (ℓ : ℕ) :
    FiniteDimensional ℂ (harmonicPolynomials ℓ) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show harmonicPolynomials ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ from inf_le_left))
    (Submodule.inclusion_injective _)

theorem polynomialCompactHarmonics_finiteDimensional (ℓ : ℕ) :
    FiniteDimensional ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) := by
  letI := harmonicPolynomials_finiteDimensional ℓ
  infer_instance

lemma su2_matrix (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) :
    (!![star b, -star a; a, b] : Matrix (Fin 2) (Fin 2) ℂ) ∈ ComplexSU2 := by
  have hc : a * star a + b * star b = 1 := by
    rw [show a * star a = (Complex.normSq a : ℂ) from Complex.mul_conj a,
      show b * star b = (Complex.normSq b : ℂ) from Complex.mul_conj b,
      ← Complex.ofReal_add, h, Complex.ofReal_one]
  change a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 at hc
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    · convert hc using 1 <;> ring
    · ring
    · ring
    · exact hc
  · simp [Matrix.det_fin_two]
    convert hc using 1 <;> ring
noncomputable def openSU2 (x : ℂ) : ComplexSU2 := by
  let r : ℝ := Real.sqrt (1 + Complex.normSq x)
  have hn := Complex.normSq_nonneg x
  have hr : r ^ 2 = 1 + Complex.normSq x := Real.sq_sqrt (by linarith)
  refine ⟨!![(star x) / r, -(1 / r); 1 / r, x / r], ?_⟩
  convert su2_matrix (1 / (r : ℂ)) (x / (r : ℂ)) ?_ using 1
  · simp [map_div₀]
  · simp only [Complex.normSq_div, Complex.normSq_one, Complex.normSq_ofReal]
    rw [← pow_two, hr]
    field_simp [show 1 + Complex.normSq x ≠ 0 by linarith]

private lemma openSU2_factor (x : ℂ) :
    ∃ (a d : ℂˣ) (b : ℂ), weyl * upperUnipotent x =
      upperTriangular a d b * complexSU2Embedding (openSU2 x) := by
  let r : ℝ := Real.sqrt (1 + Complex.normSq x)
  have hn := Complex.normSq_nonneg x
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hn := Complex.normSq_nonneg x
  have hr : r ^ 2 = 1 + Complex.normSq x := Real.sq_sqrt (by linarith)
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hrc : (r : ℂ) ^ 2 = 1 + x * (starRingEnd ℂ) x := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_add, ← hr,
      Complex.ofReal_pow]
  refine ⟨Units.mk0 (-(1 / (r : ℂ))) (by simp [hrne]),
    Units.mk0 (r : ℂ) hrne, (star x) / r, ?_⟩
  apply Units.ext
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, x; 0, 1] =
    !![-(1 / (r : ℂ)), star x / r; 0, (r : ℂ)] *
      !![star x / r, -(1 / (r : ℂ)); 1 / (r : ℂ), x / r]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
    ring
  · change (1 : ℂ) = (r : ℂ)⁻¹ * (r : ℂ)⁻¹ + (starRingEnd ℂ) x / r * (x / r)
    field_simp
    linear_combination hrc
  · change (1 : ℂ) = (r : ℂ) * (r : ℂ)⁻¹
    simp [hrne]
  · change x = (r : ℂ) * (x / r)
    field_simp

theorem compactRestriction_injective (s : ℝ) : Function.Injective (compactRestriction s) := by
  intro f h hfh
  apply openCoordinate_injective s
  funext x
  obtain ⟨a, d, b, hx⟩ := openSU2_factor x
  change f (weyl * upperUnipotent x) = h (weyl * upperUnipotent x)
  rw [hx, f.property.1, h.property.1]
  congr 1
  exact congrFun hfh (openSU2 x)

noncomputable def harmonicKTypeRestrictionEquiv (s : ℝ) (ℓ : ℕ)
    (h : (harmonicPolynomials ℓ).map polynomialCompactRestriction ≤
      (compactRestriction s).range) :
    harmonicKType s ℓ ≃ₗ[ℂ] (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
  Submodule.comap_equiv_self_of_inj_of_le (compactRestriction_injective s) h

theorem harmonicKType_finrank_of_extension (s : ℝ) (ℓ : ℕ)
    (h : (harmonicPolynomials ℓ).map polynomialCompactRestriction ≤
      (compactRestriction s).range) :
    Module.finrank ℂ (harmonicKType s ℓ) =
      Module.finrank ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) :=
  (harmonicKTypeRestrictionEquiv s ℓ h).finrank_eq

theorem harmonicKType_finite (s : ℝ) (ℓ : ℕ) : Module.Finite ℂ (harmonicKType s ℓ) := by
  letI := polynomialCompactHarmonics_finiteDimensional ℓ
  let r : harmonicKType s ℓ →ₗ[ℂ]
      (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
    ((compactRestriction s).domRestrict (harmonicKType s ℓ)).codRestrict _
      (fun f => f.property)
  apply Module.Finite.of_injective r
  intro f g hfg
  apply Subtype.ext
  apply compactRestriction_injective s
  exact congrArg Subtype.val hfg

theorem harmonicKType_structure (s : ℝ) (ℓ : ℕ) :
    IsKInvariant s (harmonicKType s ℓ) ∧
    Module.finrank ℂ (harmonicKType s ℓ) = 2 * ℓ + 1 ∧
    (∀ U : Submodule ℂ (PrincipalSeries s), U ≤ harmonicKType s ℓ →
      IsKInvariant s U → U = ⊥ ∨ U = harmonicKType s ℓ) := by
  have hext := polynomialCompactHarmonics_extend s ℓ
  have hmap : (harmonicKType s ℓ).map (compactRestriction s) =
      (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
    Submodule.map_comap_eq_self hext
  refine ⟨harmonicKType_invariant_of_polynomial_translation s ℓ
    (harmonicPolynomials_su2_translation ℓ), ?_, ?_⟩
  · exact (harmonicKType_finrank_of_extension s ℓ hext).trans
      (polynomialCompactHarmonics_finrank ℓ)
  · intro U hU hinv
    have hV : U.map (compactRestriction s) ≤
        (harmonicPolynomials ℓ).map polynomialCompactRestriction := by
      rw [← hmap]
      exact Submodule.map_mono hU
    have hstable : ∀ (k : ComplexSU2) (v : ComplexSU2 → ℂ),
        v ∈ U.map (compactRestriction s) →
          (fun h => v (h * k)) ∈ U.map (compactRestriction s) := by
      intro k v hv
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hv
      let k' : compactSubgroup :=
        ⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding k), ⟨k, rfl⟩⟩
      apply Submodule.mem_map.mpr
      refine ⟨pi s k' f, hinv k' f hf, ?_⟩
      funext h
      exact compactRestriction_pi_su2 s k h f
    rcases polynomialCompactHarmonics_irreducible ℓ
      (U.map (compactRestriction s)) hV hstable with hzero | hfull
    · left
      apply Submodule.map_injective_of_injective (compactRestriction_injective s)
      simpa using hzero
    · right
      apply Submodule.map_injective_of_injective (compactRestriction_injective s)
      exact hfull.trans hmap.symm

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end
