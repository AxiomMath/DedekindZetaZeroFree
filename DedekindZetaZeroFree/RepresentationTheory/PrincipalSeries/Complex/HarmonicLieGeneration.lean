module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedCasimir

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix

abbrev RawMat := Matrix (Fin 2) (Fin 2) ℂ

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

open scoped Matrix.Norms.Elementwise ContDiff

attribute [local instance] Complex.instNormedAddCommGroup

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

noncomputable instance instNormedAddCommGroupHarmonicLieRawMat : NormedAddCommGroup RawMat :=
  { Matrix.normedAddCommGroup.replaceTopology (by rfl) with
    norm := Matrix.normedAddCommGroup.norm
    dist_eq := Matrix.normedAddCommGroup.dist_eq }

noncomputable instance instNormedSpaceRealHarmonicLieRawMat : NormedSpace ℝ RawMat := Matrix.normedSpace

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix

abbrev RawWord := List RawMat

noncomputable def rawLie (X : RawMat) (f : ComplexGL2 → ℂ) (g : ComplexGL2) : ℂ :=
  fderiv ℝ (matrixFunction f) (g : RawMat) ((g : RawMat) * X)

noncomputable def rawWord (w : RawWord) (f : ComplexGL2 → ℂ) : ComplexGL2 → ℂ :=
  w.foldr rawLie f

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

open scoped Matrix.Norms.Elementwise ContDiff
attribute [local instance] Complex.instNormedAddCommGroup
private theorem locus_open : IsOpen {g : RawMat | g.det ≠ 0} := by
  apply isOpen_ne.preimage
  change Continuous (fun g : RawMat => g.det)
  simp only [Matrix.det_fin_two]
  fun_prop
private theorem tangent_smooth (X : RawMat) : ContDiff ℝ ∞ (fun g : RawMat => g * X) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro k _
  exact ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)).mul contDiff_const
private theorem lie_smooth (X : RawMat) (f : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0}) :
    ContDiffOn ℝ ∞ (matrixFunction (rawLie X f)) {g | g.det ≠ 0} := by
  have hd := (contDiffOn_infty_iff_fderiv_of_isOpen locus_open).mp hf
  apply (hd.2.clm_apply (tangent_smooth X).contDiffOn).congr
  intro g hg
  change g.det ≠ 0 at hg
  dsimp only [matrixFunction]
  rw [dif_pos hg]
  rfl
private theorem word_smooth (s : ℝ) (w : RawWord) :
    ContDiffOn ℝ ∞ (matrixFunction (rawWord w (sphericalSection s : ComplexGL2 → ℂ)))
      {g | g.det ≠ 0} := by
  induction w with
  | nil =>
    exact ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
  | cons X w ih => exact lie_smooth X _ ih
private theorem matrix_add (f h : ComplexGL2 → ℂ) :
    matrixFunction (f + h) = matrixFunction f + matrixFunction h := by
  funext g
  simp only [matrixFunction, Pi.add_apply]
  split <;> simp
private theorem matrix_smul (a : ℂ) (f : ComplexGL2 → ℂ) :
    matrixFunction (a • f) = a • matrixFunction f := by
  funext g
  simp only [matrixFunction, Pi.smul_apply]
  split <;> simp
private theorem matrix_zero : matrixFunction (0 : ComplexGL2 → ℂ) = 0 := by
  funext g
  simp [matrixFunction]
private theorem lie_add (X : RawMat) (f h : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0})
    (hh : ContDiffOn ℝ ∞ (matrixFunction h) {g | g.det ≠ 0}) :
    rawLie X (f + h) = rawLie X f + rawLie X h := by
  funext g
  have hgf : DifferentiableAt ℝ (matrixFunction f) (g : RawMat) :=
    (hf.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  have hgh : DifferentiableAt ℝ (matrixFunction h) (g : RawMat) :=
    (hh.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  simp only [rawLie, matrix_add, Pi.add_apply]
  convert congrArg (fun T : RawMat →L[ℝ] ℂ => T ((g : RawMat) * X))
    (fderiv_add hgf hgh) using 1 <;> rfl
private theorem lie_smul (X : RawMat) (a : ℂ) (f : ComplexGL2 → ℂ)
    (hf : ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0}) :
    rawLie X (a • f) = a • rawLie X f := by
  funext g
  have hgf : DifferentiableAt ℝ (matrixFunction f) (g : RawMat) :=
    (hf.differentiableOn (by simp)).differentiableAt (locus_open.mem_nhds g.det_ne_zero)
  simp only [rawLie, matrix_smul, Pi.smul_apply]
  convert congrArg (fun T : RawMat →L[ℝ] ℂ => T ((g : RawMat) * X))
    (fderiv_const_smul hgf a) using 1 <;> rfl

theorem raw_spherical_span_lie_stable (s : ℝ) (X : RawMat)
    (f : PrincipalSeries s)
    (hf : (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ)))) :
    rawLie X (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
  have h : ∀ (u : ComplexGL2 → ℂ), u ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord => rawWord w (sphericalSection s : ComplexGL2 → ℂ))) →
      ContDiffOn ℝ ∞ (matrixFunction u) {g | g.det ≠ 0} ∧
      rawLie X u ∈ Submodule.span ℂ
        (Set.range (fun w : RawWord => rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      rcases hu with ⟨w, rfl⟩
      exact ⟨word_smooth s w, Submodule.subset_span ⟨X :: w, rfl⟩⟩
    | zero =>
      constructor
      · rw [matrix_zero]; exact contDiffOn_const
      · have hz : rawLie X (0 : ComplexGL2 → ℂ) = 0 := by
          funext g
          simp [rawLie, matrix_zero]
        rw [hz]
        exact Submodule.zero_mem _
    | add u v hu hv ihu ihv =>
      constructor
      · rw [matrix_add]; exact ihu.1.add ihv.1
      · rw [lie_add X u v ihu.1 ihv.1]
        exact Submodule.add_mem _ ihu.2 ihv.2
    | smul a u hu ihu =>
      constructor
      · rw [matrix_smul]; exact ihu.1.const_smul a
      · rw [lie_smul X a u ihu.1]
        exact Submodule.smul_mem _ a ihu.2
  exact (h _ hf).2

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

private noncomputable def translate (a : ComplexGL2) :
    (ComplexGL2 → ℂ) →ₗ[ℂ] (ComplexGL2 → ℂ) where
  toFun f g := f (g * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def matrixRight (a : ComplexGL2) : RawMat ≃L[ℝ] RawMat :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun m => m * (a : RawMat)
      invFun := fun m => m * ((a⁻¹ : ComplexGL2) : RawMat)
      left_inv := by intro m; simp [Matrix.mul_assoc, ← Units.val_mul]
      right_inv := by intro m; simp [Matrix.mul_assoc, ← Units.val_mul]
      map_add' := by intro m n; exact Matrix.add_mul _ _ _
      map_smul' := by intro c m; exact Matrix.smul_mul _ _ _ }

private lemma matrixFunction_translate (a : ComplexGL2) (f : ComplexGL2 → ℂ) :
    matrixFunction (translate a f) = matrixFunction f ∘ matrixRight a := by
  funext m
  have hd := Matrix.GeneralLinearGroup.det_ne_zero a
  have he : (m * (a : RawMat)).det ≠ 0 ↔ m.det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero_iff.trans (and_iff_left hd)
  change (if h : m.det ≠ 0 then
    translate a f (Matrix.GeneralLinearGroup.mkOfDetNeZero m h) else 0) =
    (if h : (m * (a : RawMat)).det ≠ 0 then
      f (Matrix.GeneralLinearGroup.mkOfDetNeZero (m * (a : RawMat)) h) else 0)
  by_cases hm : m.det ≠ 0
  · rw [dif_pos hm, dif_pos (he.mpr hm)]
    change f (_ * a) = f _
    congr 1
    apply Units.ext
    rfl
  · rw [dif_neg hm, dif_neg (fun h => hm (he.mp h))]

private lemma translate_rawLie (a : ComplexGL2) (X : RawMat)
    (f : ComplexGL2 → ℂ) :
    translate a (rawLie X f) =
      rawLie ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat)) (translate a f) := by
  funext g
  change fderiv ℝ (matrixFunction f) ((g * a : ComplexGL2) : RawMat)
      (((g * a : ComplexGL2) : RawMat) * X) =
    fderiv ℝ (matrixFunction (translate a f)) (g : RawMat)
      ((g : RawMat) * ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat)))
  rw [matrixFunction_translate]
  have hd := (matrixRight a).comp_right_fderiv (f := matrixFunction f) (x := (g : RawMat))
  erw [hd]
  change fderiv ℝ (matrixFunction f) ((g : RawMat) * (a : RawMat))
      (((g : RawMat) * (a : RawMat)) * X) =
    fderiv ℝ (matrixFunction f) ((g : RawMat) * (a : RawMat))
      (((g : RawMat) * ((a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat))) * (a : RawMat))
  congr 1
  have ha : ((a⁻¹ : ComplexGL2) : RawMat) * (a : RawMat) = 1 := a.inv_val
  simpa only [Matrix.mul_assoc, ha, Matrix.mul_one]

private lemma translate_rawWord (a : ComplexGL2) (w : RawWord)
    (f : ComplexGL2 → ℂ) :
    translate a (rawWord w f) =
      rawWord (w.map (fun X => (a : RawMat) * X * ((a⁻¹ : ComplexGL2) : RawMat))) (translate a f) := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    simp only [rawWord, List.foldr_cons, List.map_cons] at *
    rw [translate_rawLie, ih]

theorem raw_spherical_span_compact_stable (s : ℝ) (k : compactSubgroup)
    (f : PrincipalSeries s)
    (hf : (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ)))) :
    (pi s k f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
  obtain ⟨u, hu⟩ := k.property
  let a := complexSU2Embedding u
  have hk : Matrix.ProjGenLinGroup.mk a = (k : ComplexPGL2) := hu
  have hfixed : translate a (sphericalSection s : ComplexGL2 → ℂ) =
      (sphericalSection s : ComplexGL2 → ℂ) := by
    have h := sphericalSection_fixed s k
    rw [← hk, pi_mk] at h
    exact congrArg (fun t : PrincipalSeries s => (t : ComplexGL2 → ℂ)) h
  have hspan : ∀ v : ComplexGL2 → ℂ,
      v ∈ Submodule.span ℂ (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) →
      translate a v ∈ Submodule.span ℂ (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection s : ComplexGL2 → ℂ))) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨w, rfl⟩ := hv
      rw [translate_rawWord, hfixed]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add v z hv hz iv iz =>
      rw [map_add]
      exact Submodule.add_mem _ iv iz
    | smul c v hv iv =>
      rw [map_smul]
      exact Submodule.smul_mem _ c iv
  rw [← hk, pi_mk]
  exact hspan (f : ComplexGL2 → ℂ) hf

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues KPCplxCharacterHaar

namespace RaisingCalculation
open MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise

noncomputable def transverse : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1
theorem transverse_homogeneous (ℓ : ℕ) :
    (transverse ^ ℓ).IsHomogeneous ℓ := by
  simpa [transverse] using ((isHomogeneous_X ℂ (0 : Fin 3)).add
    ((isHomogeneous_X ℂ (1 : Fin 3)).C_mul Complex.I)).pow ℓ
theorem lap_mul_transverse (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (transverse * p) = transverse * polynomialLaplacian p +
      2 * (pderiv 0 p + C Complex.I * pderiv 1 p) := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, transverse, pderiv_mul, pderiv_C_mul]
  ring
theorem transverse_direction (ℓ : ℕ) :
    pderiv 0 (transverse ^ ℓ) + C Complex.I * pderiv 1 (transverse ^ ℓ) = 0 := by
  simp only [pderiv_pow]
  simp [transverse, pderiv_C_mul, Pi.single_apply]
  have hI : (C Complex.I : MvPolynomial (Fin 3) ℂ) ^ 2 = -1 := by
    rw [← map_pow]; norm_num
  linear_combination (ℓ : MvPolynomial (Fin 3) ℂ) *
    (X 0 + C Complex.I * X 1) ^ (ℓ - 1) * hI
theorem transverse_harmonic (ℓ : ℕ) : transverse ^ ℓ ∈ harmonicPolynomials ℓ := by
  refine ⟨transverse_homogeneous ℓ, ?_⟩
  change polynomialLaplacian (transverse ^ ℓ) = 0
  induction ℓ with
  | zero => simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply]
  | succ n ih =>
    rw [pow_succ', lap_mul_transverse, ih, transverse_direction]
    simp
theorem lap_mul_height (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (X 2 * p) = X 2 * polynomialLaplacian p + 2 * pderiv 2 p := by
  simp [polynomialLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Fin.sum_univ_succ, pderiv_mul]
  ring
theorem height_transverse_harmonic (ℓ : ℕ) :
    X 2 * transverse ^ ℓ ∈ harmonicPolynomials (ℓ + 1) := by
  constructor
  · simpa [Nat.add_comm] using (isHomogeneous_X ℂ (2 : Fin 3)).mul (transverse_homogeneous ℓ)
  · change polynomialLaplacian (X 2 * transverse ^ ℓ) = 0
    rw [lap_mul_height, (transverse_harmonic ℓ).2]
    simp [pderiv_pow, transverse, pderiv_C_mul, Pi.single_apply]

noncomputable def rowB (m : RawMat) : ℝ := ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2
noncomputable def rowW (m : RawMat) : ℂ := 2 * m 1 0 * star (m 1 1) / (rowB m : ℂ)
theorem rowB_pos (g : ComplexGL2) : 0 < rowB g :=
  KPCplxRotatedKernelEstimates.bottomRowNormSq_pos g
theorem rowW_smooth : ContDiffOn ℝ (⊤ : ℕ∞) rowW {m | m.det ≠ 0} := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun m : RawMat => m 1 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun m : RawMat => m 1 1) := by fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) rowB := (h0.norm_sq (𝕜 := ℂ)).add (h1.norm_sq (𝕜 := ℂ))
  unfold rowW
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · exact ((contDiff_const.mul h0).mul (Complex.conjCLE.contDiff.comp h1)).contDiffOn
  · apply ContDiffOn.inv (Complex.ofRealCLM.contDiff.comp hb |>.contDiffOn)
    intro m hm
    exact Complex.ofReal_ne_zero.mpr (rowB_pos (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm)).ne'
theorem rowW_left (a d : ℂˣ) (b : ℂ) (g : ComplexGL2) :
    rowW (upperTriangular a d b * g) = rowW g := by
  have hup : (upperTriangular a d b : RawMat) = !![(a : ℂ), b; 0, (d : ℂ)] := rfl
  have he : rowB (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * rowB g := by
    change rowB ((upperTriangular a d b : RawMat) * (g : RawMat)) = _
    rw [hup]
    simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, mul_add]
  unfold rowW
  rw [he]
  change 2 * ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : RawMat)) 1 0) *
    star ((!![(a : ℂ), b; 0, (d : ℂ)] * (g : RawMat)) 1 1) /
    (‖(d : ℂ)‖ ^ 2 * rowB g : ℝ) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change 2 * ((0 : ℂ) * (g : RawMat) 0 0 + (d : ℂ) * (g : RawMat) 1 0) *
    star ((0 : ℂ) * (g : RawMat) 0 1 + (d : ℂ) * (g : RawMat) 1 1) / _ = _
  simp only [zero_mul, zero_add, star_mul]
  rw [show 2 * ((d : ℂ) * (g : RawMat) 1 0) * (star ((g : RawMat) 1 1) * star (d : ℂ)) =
    ((d : ℂ) * star (d : ℂ)) * (2 * (g : RawMat) 1 0 * star ((g : RawMat) 1 1)) by ring]
  simp only [Complex.star_def, Complex.mul_conj']
  push_cast
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr d.ne_zero)))
noncomputable def harmonicFunction (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) : ℂ :=
  sphericalSection s g * rowW g ^ ℓ
theorem harmonicFunction_mem (s : ℝ) (ℓ : ℕ) :
    harmonicFunction s ℓ ∈ principalSeriesSubmodule s := by
  apply (principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have hc := (sphericalSection s).property.1 a d b g
    unfold harmonicFunction
    rw [hc]
    change _ * _ * rowW ((upperTriangular a d b : RawMat) * (g : RawMat)) ^ ℓ = _
    rw [rowW_left]
    ring
  · have hs := ((principalSeries_mem_iff s _).mp (sphericalSection s).property).2
    have hh := hs.mul (rowW_smooth.pow ℓ)
    apply hh.congr
    intro m hm
    change m.det ≠ 0 at hm
    simp only [matrixFunction, dif_pos hm, harmonicFunction]
    rfl
noncomputable def harmonicSection (s : ℝ) (ℓ : ℕ) : PrincipalSeries s :=
  ⟨harmonicFunction s ℓ, harmonicFunction_mem s ℓ⟩

noncomputable def rowZ (m : RawMat) : ℂ := ((‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ) : ℂ) / (rowB m : ℂ)
theorem rowB_compact (k : ComplexSU2) : rowB k = 1 := by
  have hrow := congrArg (fun B : RawMat => (B 1 1).re)
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply_eq] at hrow
  change (((k : RawMat) 1 0 * (starRingEnd ℂ) ((k : RawMat) 1 0)) +
    ((k : RawMat) 1 1 * (starRingEnd ℂ) ((k : RawMat) 1 1))).re = 1 at hrow
  simpa only [rowB, Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] using hrow
theorem spherical_compact (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  change (Real.rpow (‖(k : RawMat).det‖ / rowB k) (1 + 2 * s) : ℂ) = 1
  rw [hd, rowB_compact]; simp
theorem rowW_compact (k : ComplexSU2) :
    rowW k = compactSphereCoordinate k 0 + Complex.I * compactSphereCoordinate k 1 := by
  simp only [rowW, rowB_compact, Complex.ofReal_one, div_one, compactSphereCoordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hr := Complex.re_add_im ((k : RawMat) 1 0 * star ((k : RawMat) 1 1))
  push_cast
  linear_combination 2 * hr.symm
theorem rowZ_compact (k : ComplexSU2) : rowZ k = compactSphereCoordinate k 2 := by
  simp [rowZ, rowB_compact, compactSphereCoordinate]

theorem harmonicSection_compact (s : ℝ) (ℓ : ℕ) :
    compactRestriction s (harmonicSection s ℓ) = polynomialCompactRestriction (transverse ^ ℓ) := by
  ext k
  change sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ =
    MvPolynomial.eval (compactSphereCoordinate k) (transverse ^ ℓ)
  rw [spherical_compact, rowW_compact]
  simp [transverse]

theorem harmonicSection_harmonic (s : ℝ) (ℓ : ℕ) :
    harmonicSection s ℓ ∈ harmonicKType s ℓ := by
  exact ⟨transverse ^ ℓ, transverse_harmonic ℓ, (harmonicSection_compact s ℓ).symm⟩

theorem height_harmonic_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) :
    v ∈ harmonicKType s (ℓ + 1) := by
  refine ⟨c • (X 2 * transverse ^ ℓ),
    (harmonicPolynomials (ℓ + 1)).smul_mem c (height_transverse_harmonic ℓ), ?_⟩
  ext k
  change MvPolynomial.eval (compactSphereCoordinate k) (c • (X 2 * transverse ^ ℓ)) =
    v (complexSU2Embedding k)
  rw [hv]
  change _ = c * rowZ k * (sphericalSection s (complexSU2Embedding k) * rowW k ^ ℓ)
  rw [spherical_compact, rowZ_compact, rowW_compact]
  simp [transverse, mul_assoc]

theorem rawLie_section_exists (s : ℝ) (X : RawMat) (u : PrincipalSeries s) :
    ∃ v : PrincipalSeries s, (v : ComplexGL2 → ℂ) = rawLie X u := by
  let D := RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.rightDerivativeLinear s X
  refine ⟨D u, ?_⟩
  funext g
  rw [RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.rightDerivativeLinear_apply,
    RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.rightDerivative_fderiv]
  rfl

theorem height_ne_zero_of_formula (s : ℝ) (ℓ : ℕ) (c : ℂ) (hc : c ≠ 0)
    (v : PrincipalSeries s)
    (hv : ∀ g, v g = c * rowZ g * harmonicSection s ℓ g) : v ≠ 0 := by
  let g : ComplexGL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 2] (by
    norm_num [Matrix.det_fin_two])
  have hZ : rowZ g = -(3 / 5 : ℂ) := by
    norm_num [rowZ, rowB, g]
  have hW : rowW g = (4 / 5 : ℂ) := by
    norm_num [rowW, rowB, g]
  have hS : sphericalSection s g ≠ 0 := by
    change (Real.rpow _ (1 + 2 * s) : ℂ) ≠ 0
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    apply div_pos
    · exact norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
    · exact rowB_pos g
  intro he
  have hz := congrArg (fun f : PrincipalSeries s => f g) he
  change v g = 0 at hz
  rw [hv] at hz
  change c * rowZ g * (sphericalSection s g * rowW g ^ ℓ) = 0 at hz
  rw [hZ, hW] at hz
  exact (mul_ne_zero (mul_ne_zero hc (by norm_num))
    (mul_ne_zero hS (pow_ne_zero ℓ (by norm_num)))) hz

noncomputable def boostUnit (t : ℝ) : ℂˣ := Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))
noncomputable def boost (t : ℝ) : ComplexGL2 := diagonal (boostUnit t)
noncomputable def boostMatrix : RawMat := !![1, 0; 0, 0]
theorem boost_zero : boost 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boost, diagonal, boostUnit, Matrix.one_apply]
theorem boost_bottom (g : ComplexGL2) (t : ℝ) :
    rowB (g * boost t) = ‖(g : RawMat) 1 0‖ ^ 2 * Real.exp t ^ 2 + ‖(g : RawMat) 1 1‖ ^ 2 := by
  have hb : (boost t : RawMat) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  change rowB ((g : RawMat) * (boost t : RawMat)) = _
  rw [hb]
  simp [rowB, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow, le_of_lt (Real.exp_pos t)]
theorem boost_transverse (g : ComplexGL2) (t : ℝ) :
    rowW (g * boost t) =
      (2 * (g : RawMat) 1 0 * star ((g : RawMat) 1 1)) * (Real.exp t : ℂ) / (rowB (g * boost t) : ℂ) := by
  have hb : (boost t : RawMat) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  unfold rowW
  change 2 * (((g : RawMat) * (boost t : RawMat)) 1 0) *
    star (((g : RawMat) * (boost t : RawMat)) 1 1) / _ = _
  rw [hb]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm, mul_left_comm]
theorem boost_det_norm (g : ComplexGL2) (t : ℝ) :
    ‖((Matrix.GeneralLinearGroup.det (g * boost t) : ℂˣ) : ℂ)‖ =
      ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ * Real.exp t := by
  simp [map_mul, boost, diagonal, boostUnit, Matrix.det_fin_two, norm_mul, le_of_lt (Real.exp_pos t)]
theorem boost_bottom_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowB (g * boost t)) (2 * ‖(g : RawMat) 1 0‖ ^ 2) 0 := by
  simp_rw [boost_bottom]
  convert ((Real.hasDerivAt_exp (0 : ℝ)).pow 2).const_mul (‖(g : RawMat) 1 0‖ ^ 2) |>.add_const
    (‖(g : RawMat) 1 1‖ ^ 2) using 1 <;> simp <;> ring
theorem boost_transverse_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => rowW (g * boost t)) (-rowZ g * rowW g) 0 := by
  let A := ‖(g : RawMat) 1 0‖ ^ 2
  let B := rowB g
  let W := 2 * (g : RawMat) 1 0 * star ((g : RawMat) 1 1)
  have hB : B ≠ 0 := (rowB_pos g).ne'
  have hh := ((Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp.const_mul W).div
    (boost_bottom_hasDerivAt g).ofReal_comp (by simpa [boost_zero] using Complex.ofReal_ne_zero.mpr hB)
  simp only [Real.exp_zero, Complex.ofReal_one, mul_one, boost_zero, mul_one] at hh
  simp_rw [boost_transverse]
  convert hh using 1
  dsimp [rowZ, rowW, W, B, A, rowB]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hB]
  ring

theorem boost_spherical_hasDerivAt (s : ℝ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t))
      (-((1 + 2 * s : ℝ) : ℂ) * rowZ g * sphericalSection s g) 0 := by
  let a := ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖
  let B := rowB g
  let A := ‖(g : RawMat) 1 0‖ ^ 2
  let e := 1 + 2 * s
  have ha : 0 < a := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hB : 0 < B := rowB_pos g
  have hz : rowB (g * boost 0) = B := by simp [boost_zero, B]
  have hq := ((Real.hasDerivAt_exp (0 : ℝ)).const_mul a).div
    (boost_bottom_hasDerivAt g) (by rw [hz]; exact hB.ne')
  have hp := hq.rpow_const (p := e) (Or.inl (by change a * Real.exp 0 / rowB (g * boost 0) ≠ 0; rw [hz]; positivity))
  have hh := hp.ofReal_comp
  have he : (fun t : ℝ => sphericalSection s (g * boost t)) =
      fun t : ℝ => (((a * Real.exp t / rowB (g * boost t)) ^ e : ℝ) : ℂ) := by
    funext t
    change (Real.rpow _ _ : ℂ) = _
    rw [boost_det_norm]
    rfl
  rw [he]
  convert hh using 1
  simp only [Real.exp_zero, mul_one, hz, Pi.div_apply]
  change -((e : ℝ) : ℂ) * rowZ g * ((a / B) ^ e : ℝ) = _
  have hepow : (a / B) ^ e = (a / B) ^ (e - 1) * (a / B) := by
    conv_rhs => rhs; rw [← Real.rpow_one (a / B)]
    rw [← Real.rpow_add (div_pos ha hB)]
    congr 1; ring
  rw [hepow]
  dsimp [rowZ, B, A, rowB]
  push_cast
  field_simp
  ring

private theorem boost_path_hasDerivAt (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => ((g * boost t : ComplexGL2) : RawMat))
      ((g : RawMat) * boostMatrix) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hb (t : ℝ) : (boost t : RawMat) = !![(Real.exp t : ℂ), 0; 0, 1] := rfl
  change HasDerivAt (fun t : ℝ => ((g : RawMat) * (boost t : RawMat)) i j) _ 0
  simp_rw [hb]
  fin_cases j
  · simpa [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      (Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp.const_mul ((g : RawMat) i 0)
  · simpa [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two] using
      hasDerivAt_const (0 : ℝ) ((g : RawMat) i 1)

private theorem rawLie_boost_deriv (s : ℝ) (u : PrincipalSeries s) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => u (g * boost t)) (rawLie boostMatrix u g) 0 := by
  have hf := ((principalSeries_mem_iff s u.val).mp u.property).2
  have hcont : Continuous (fun m : RawMat => m.det) := by fun_prop
  have hd := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (boost_path_hasDerivAt g)
    (by simp [boost_zero])
  have he : (fun t : ℝ => u (g * boost t)) =
      matrixFunction u.val ∘ (fun t : ℝ => ((g * boost t : ComplexGL2) : RawMat)) := by
    funext t
    simp only [Function.comp_def, matrixFunction,
      dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (g * boost t))]
    apply congrArg (u : ComplexGL2 → ℂ)
    apply Units.ext
    rfl
  rw [he]
  exact hh

private theorem harmonic_boost_hasDerivAt (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) :
    HasDerivAt (fun t : ℝ => harmonicSection s ℓ (g * boost t))
      (-(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g * harmonicSection s ℓ g) 0 := by
  have hh := (boost_spherical_hasDerivAt s g).mul ((boost_transverse_hasDerivAt g).pow ℓ)
  simp only [boost_zero, mul_one] at hh
  change HasDerivAt (fun t : ℝ => sphericalSection s (g * boost t) * rowW (g * boost t) ^ ℓ) _ 0
  convert hh using 1
  change -(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ) * rowZ g *
    (sphericalSection s g * rowW g ^ ℓ) = _
  push_cast
  cases ℓ with
  | zero => simp
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply,
      boost_zero, Units.val_one, Matrix.mul_one, pow_succ]
    ring

private theorem rawLie_harmonic_boost (s : ℝ) (ℓ : ℕ) (g : ComplexGL2) :
    rawLie boostMatrix (harmonicSection s ℓ) g =
      (-(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ)) * rowZ g * harmonicSection s ℓ g := by
  exact (rawLie_boost_deriv s (harmonicSection s ℓ) g).unique
    (harmonic_boost_hasDerivAt s ℓ g)

end RaisingCalculation

theorem harmonic_noncompact_raising (s : ℝ) (ℓ : ℕ)
    (hcoeff : (ℓ : ℝ) + 1 + 2 * s ≠ 0) :
    ∃ (X : RawMat) (u v h : PrincipalSeries s),
      u ∈ harmonicKType s ℓ ∧
      v ∈ harmonicKType s (ℓ + 1) ∧
      v ≠ 0 ∧
      h ∈ harmonicKType s (ℓ - 1) ∧
      rawLie X (u : ComplexGL2 → ℂ) =
        (v : ComplexGL2 → ℂ) + (h : ComplexGL2 → ℂ) := by
  let c : ℂ := -(((ℓ : ℝ) + 1 + 2 * s : ℝ) : ℂ)
  have hc : c ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hcoeff)
  obtain ⟨v, hv⟩ := RaisingCalculation.rawLie_section_exists s
    RaisingCalculation.boostMatrix (RaisingCalculation.harmonicSection s ℓ)
  have hformula (g : ComplexGL2) : v g = c * RaisingCalculation.rowZ g *
      RaisingCalculation.harmonicSection s ℓ g := by
    rw [show v g = rawLie RaisingCalculation.boostMatrix
      (RaisingCalculation.harmonicSection s ℓ) g from congrFun hv g]
    exact RaisingCalculation.rawLie_harmonic_boost s ℓ g
  refine ⟨RaisingCalculation.boostMatrix, RaisingCalculation.harmonicSection s ℓ,
    v, 0, RaisingCalculation.harmonicSection_harmonic s ℓ,
    RaisingCalculation.height_harmonic_of_formula s ℓ c v hformula,
    RaisingCalculation.height_ne_zero_of_formula s ℓ c hc v hformula,
    (harmonicKType s (ℓ - 1)).zero_mem, ?_⟩
  simpa using hv.symm

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues KPCplxCharacterHaar

private lemma spherical_compact_value (s : ℝ) (k : ComplexSU2) :
    sphericalSection s (complexSU2Embedding k) = 1 := by
  let k' : compactSubgroup :=
    ⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding k), ⟨k, rfl⟩⟩
  have he := congrArg (fun f : PrincipalSeries s => f 1)
    (sphericalSection_fixed s k')
  change (pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k))
    (sphericalSection s)) 1 = sphericalSection s 1 at he
  rw [pi_mk] at he
  change sphericalSection s (1 * complexSU2Embedding k) = sphericalSection s 1 at he
  simpa only [one_mul, sphericalSection_one] using he

theorem harmonic_zero_mem_raw_spherical_span
    (f : PrincipalSeries positiveParameter)
    (hf : f ∈ harmonicKType positiveParameter 0) :
    (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ))) := by
  change compactRestriction positiveParameter f ∈
    (harmonicPolynomials 0).map polynomialCompactRestriction at hf
  obtain ⟨p, hp, he⟩ := hf
  have hp0 : p.IsHomogeneous 0 := hp.1
  have hpC : p = MvPolynomial.C (p.coeff 0) := by
    exact (MvPolynomial.homogeneousComponent_eq_self hp0).symm.trans
      (MvPolynomial.homogeneousComponent_zero p)
  have hfeq : f = (p.coeff 0) • sphericalSection positiveParameter := by
    apply (harmonicKType_compact_identification positiveParameter positiveParameter 0).1
    rw [← he, map_smul]
    ext k
    change MvPolynomial.eval (compactSphereCoordinate k) p =
      (p.coeff 0) * sphericalSection positiveParameter (complexSU2Embedding k)
    rw [hpC, MvPolynomial.eval_C, spherical_compact_value, mul_one]
    simp
  rw [hfeq]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨[], rfl⟩

theorem harmonic_mem_raw_spherical_span (ℓ : ℕ)
    (f : PrincipalSeries positiveParameter)
    (hf : f ∈ harmonicKType positiveParameter ℓ) :
    (f : ComplexGL2 → ℂ) ∈ Submodule.span ℂ
      (Set.range (fun w : RawWord =>
        rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ))) := by
  induction ℓ using Nat.strong_induction_on generalizing f with
  | h n ih =>
    cases n with
    | zero => exact harmonic_zero_mem_raw_spherical_span f hf
    | succ ℓ =>
      let S : Submodule ℂ (ComplexGL2 → ℂ) := Submodule.span ℂ
        (Set.range (fun w : RawWord =>
          rawWord w (sphericalSection positiveParameter : ComplexGL2 → ℂ)))
      let U : Submodule ℂ (PrincipalSeries positiveParameter) :=
        S.comap (principalSeriesSubmodule positiveParameter).subtype
      let W : Submodule ℂ (PrincipalSeries positiveParameter) :=
        harmonicKType positiveParameter (ℓ + 1) ⊓ U
      have hcoeff : (ℓ : ℝ) + 1 + 2 * positiveParameter ≠ 0 := by
        dsimp only [positiveParameter]
        positivity
      obtain ⟨X, u, v, h, hu, hv, hvne, hh, he⟩ :=
        harmonic_noncompact_raising positiveParameter ℓ hcoeff
      have huS : (u : ComplexGL2 → ℂ) ∈ S :=
        ih ℓ (Nat.lt_succ_self ℓ) u hu
      have hhS : (h : ComplexGL2 → ℂ) ∈ S :=
        ih (ℓ - 1) (by omega) h hh
      have hvS : (v : ComplexGL2 → ℂ) ∈ S := by
        have hlie := raw_spherical_span_lie_stable positiveParameter X u huS
        have he' : (v : ComplexGL2 → ℂ) =
            rawLie X (u : ComplexGL2 → ℂ) - (h : ComplexGL2 → ℂ) := by
          rw [he]
          abel
        rw [he']
        exact S.sub_mem hlie hhS
      have hvW : v ∈ W := ⟨hv, hvS⟩
      have hW : IsKInvariant positiveParameter W := by
        intro k g hg
        refine ⟨(harmonicKType_multiplicity_one positiveParameter (ℓ + 1)).1 k g hg.1,
          ?_⟩
        exact raw_spherical_span_compact_stable positiveParameter k g hg.2
      have hcases := (harmonicKType_multiplicity_one positiveParameter (ℓ + 1)).2.2.1
        W inf_le_left hW
      have hWeq : W = harmonicKType positiveParameter (ℓ + 1) := by
        rcases hcases with hzero | hfull
        · have : v = 0 := by
            have hvbot : v ∈ (⊥ : Submodule ℂ (PrincipalSeries positiveParameter)) := by
              rw [← hzero]
              exact hvW
            simpa only [Submodule.mem_bot] using hvbot
          exact (hvne this).elim
        · exact hfull
      have hfW : f ∈ W := by
        rw [hWeq]
        exact hf
      exact hfW.2

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end
