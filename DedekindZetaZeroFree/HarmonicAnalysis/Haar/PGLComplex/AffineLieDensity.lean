module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLAffineCoordinates
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLChartNormalization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex
open MeasureTheory Topology
open scoped Matrix.Norms.Operator Manifold ContDiff

abbrev Group := Matrix.ProjGenLinGroup (Fin 2) ℂ
abbrev Coordinates := Fin 6 → ℝ

instance : TopologicalSpace Group := inferInstanceAs
  (TopologicalSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))
instance : IsTopologicalGroup Group := inferInstanceAs
  (IsTopologicalGroup (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

instance : MeasurableSpace Group := borel _

instance : BorelSpace Group := ⟨rfl⟩

def complexCoordinates (x : Coordinates) : Fin 3 → ℂ :=
  ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩, ⟨x 4, x 5⟩]

def affineMatrix (x : Coordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, complexCoordinates x 1; complexCoordinates x 2, 1 + complexCoordinates x 0]

def delta (x : Coordinates) : ℂ :=
  1 + complexCoordinates x 0 - complexCoordinates x 1 * complexCoordinates x 2

def affineSource : Set Coordinates := {x | delta x ≠ 0}

theorem affineMatrix_det (x : Coordinates) : (affineMatrix x).det = delta x := by
  simp [affineMatrix, delta, Matrix.det_fin_two]

def affinePoint (x : Coordinates) : Group :=
  if h : delta x ≠ 0 then Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix x)
      (by rwa [affineMatrix_det])) else 1

def affineTarget : Set Group := {g | g.out.val 0 0 ≠ 0}

def affineInverse (g : Group) : Coordinates :=
  let u := g.out.val 1 1 / g.out.val 0 0 - 1
  let b := g.out.val 0 1 / g.out.val 0 0
  let c := g.out.val 1 0 / g.out.val 0 0
  ![u.re, u.im, b.re, b.im, c.re, c.im]

abbrev AffineGL := Matrix.GeneralLinearGroup (Fin 2) ℂ
def rawInverse (a : AffineGL) : Coordinates :=
  let u := a.val 1 1 / a.val 0 0 - 1
  let b := a.val 0 1 / a.val 0 0
  let c := a.val 1 0 / a.val 0 0
  ![u.re, u.im, b.re, b.im, c.re, c.im]
private theorem scalar_val (a : AffineGL) (z : ℂˣ) (i j : Fin 2) :
    (a * Matrix.GeneralLinearGroup.scalar (Fin 2) z).val i j = a.val i j * (z : ℂ) := by
  simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal]
private theorem rawInverse_scalar (a : AffineGL) (z : ℂˣ) :
    rawInverse (a * Matrix.GeneralLinearGroup.scalar (Fin 2) z) = rawInverse a := by
  simp [rawInverse, scalar_val, mul_div_mul_right _ _ (Units.ne_zero z)]
private theorem rawInverse_mk (a : AffineGL) : affineInverse (Matrix.ProjGenLinGroup.mk a) = rawInverse a := by
  have he : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk (Matrix.ProjGenLinGroup.mk a).out := (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  change rawInverse (Matrix.ProjGenLinGroup.mk a).out = rawInverse a
  rw [← hz, rawInverse_scalar]
theorem target_mk (a : AffineGL) : Matrix.ProjGenLinGroup.mk a ∈ affineTarget ↔ a.val 0 0 ≠ 0 := by
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp ((Quotient.out_eq (Matrix.ProjGenLinGroup.mk a)).symm)
  change (Matrix.ProjGenLinGroup.mk a).out.val 0 0 ≠ 0 ↔ a.val 0 0 ≠ 0
  rw [← hz, scalar_val]
  simp
private theorem complex_raw (a : AffineGL) : complexCoordinates (rawInverse a) =
    ![a.val 1 1 / a.val 0 0 - 1, a.val 0 1 / a.val 0 0, a.val 1 0 / a.val 0 0] := by
  ext i
  fin_cases i <;> apply Complex.ext <;> simp [complexCoordinates, rawInverse]
private theorem raw_matrix (a : AffineGL) (ha : a.val 0 0 ≠ 0) :
    affineMatrix (rawInverse a) = (a.val 0 0)⁻¹ • a.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affineMatrix, complex_raw, smul_eq_mul, div_eq_mul_inv, ha, mul_comm]
  exact mul_comm _ _
private theorem raw_source (a : AffineGL) (ha : a.val 0 0 ≠ 0) : rawInverse a ∈ affineSource := by
  change delta (rawInverse a) ≠ 0
  rw [← affineMatrix_det, raw_matrix a ha, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha)) (Matrix.GeneralLinearGroup.det_ne_zero a)
private theorem raw_point (a : AffineGL) (ha : a.val 0 0 ≠ 0) :
    affinePoint (rawInverse a) = Matrix.ProjGenLinGroup.mk a := by
  have hs := raw_source a ha
  unfold affinePoint
  rw [dif_pos (show delta (rawInverse a) ≠ 0 from hs)]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (a.val 0 0) ha, Units.ext ?_⟩
  change (affineMatrix (rawInverse a)) * Matrix.scalar (Fin 2) (a.val 0 0) = a.val
  rw [raw_matrix a ha]
  ext i j
  simp [Matrix.mul_diagonal, smul_eq_mul, ha]
  field_simp
private theorem complex_zero : complexCoordinates (0 : Coordinates) = 0 := by
  ext i
  fin_cases i <;> rfl
private theorem raw_affine (x : Coordinates) (hx : x ∈ affineSource) :
    rawInverse (Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix x)
      (by rwa [affineMatrix_det])) = x := by
  ext i
  fin_cases i <;> simp [rawInverse, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    affineMatrix, complexCoordinates]
private theorem point_target (x : Coordinates) (hx : x ∈ affineSource) :
    affinePoint x ∈ affineTarget := by
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), target_mk]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, affineMatrix]
private theorem inverse_point (x : Coordinates) (hx : x ∈ affineSource) :
    affineInverse (affinePoint x) = x := by
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), rawInverse_mk, raw_affine x hx]
private theorem inverse_source (g : Group) (hg : g ∈ affineTarget) :
    affineInverse g ∈ affineSource := by
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [rawInverse_mk]
  exact raw_source a ((target_mk a).mp hg)
private theorem point_inverse (g : Group) (hg : g ∈ affineTarget) :
    affinePoint (affineInverse g) = g := by
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [rawInverse_mk]
  exact raw_point a ((target_mk a).mp hg)
private theorem continuous_complex_pair (i j : Fin 6) :
    Continuous (fun x : Coordinates => (⟨x i, x j⟩ : ℂ)) := by
  have h : Continuous (fun x : Coordinates => (x i : ℂ) + (x j : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp (continuous_apply i)).add
      ((Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const)
  convert h using 1
  funext x
  apply Complex.ext <;> simp
private theorem continuous_complexCoordinates : Continuous complexCoordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [complexCoordinates]
  · exact continuous_complex_pair 0 1
  · exact continuous_complex_pair 2 3
  · exact continuous_complex_pair 4 5
private theorem continuous_coordinate (i : Fin 3) :
    Continuous (fun x : Coordinates => complexCoordinates x i) :=
  (continuous_apply i).comp continuous_complexCoordinates
private theorem continuous_affineMatrix : Continuous affineMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [affineMatrix]
  · exact continuous_const
  · exact continuous_coordinate 1
  · exact continuous_coordinate 2
  · exact continuous_const.add (continuous_coordinate 0)
private theorem continuous_delta : Continuous delta :=
  (continuous_const.add (continuous_coordinate 0)).sub
    ((continuous_coordinate 1).mul (continuous_coordinate 2))
private theorem open_source : IsOpen affineSource :=
  isOpen_ne_fun continuous_delta continuous_const
private theorem quotient_open : IsOpenQuotientMap (Matrix.ProjGenLinGroup.mk : AffineGL → Group) :=
  ⟨Matrix.ProjGenLinGroup.mk_surjective, QuotientGroup.continuous_mk,
    QuotientGroup.isOpenMap_coe⟩
private theorem continuous_entry (i j : Fin 2) : Continuous (fun a : AffineGL => a.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)))
private theorem open_target : IsOpen affineTarget := by
  rw [← quotient_open.isQuotientMap.isOpen_preimage]
  have he : (Matrix.ProjGenLinGroup.mk : AffineGL → Group) ⁻¹' affineTarget =
      {a | a.val 0 0 ≠ 0} := by ext a; exact target_mk a
  rw [he]
  exact isOpen_ne_fun (continuous_entry 0 0) continuous_const
private theorem continuous_rawAt (a : AffineGL) (ha : a.val 0 0 ≠ 0) :
    ContinuousAt rawInverse a := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> simp [rawInverse]
  all_goals fun_prop (disch := first | exact ha | exact (continuous_entry _ _).continuousAt)
private theorem continuous_inverse : ContinuousOn affineInverse affineTarget := by
  intro g hg
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  apply ContinuousAt.continuousWithinAt
  apply quotient_open.continuousAt_comp_iff.mp
  have he : affineInverse ∘ Matrix.ProjGenLinGroup.mk = rawInverse := funext rawInverse_mk
  rw [he]
  exact continuous_rawAt a ((target_mk a).mp hg)
private theorem continuous_point : ContinuousOn affinePoint affineSource := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hx' : delta x ≠ 0 := hx
  have he : affinePoint =ᶠ[𝓝 x] (fun y => Matrix.ProjGenLinGroup.mk
      (if h : delta y ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix y)
        (by rwa [affineMatrix_det]) else 1)) := by
    filter_upwards [] with y
    unfold affinePoint
    split_ifs <;> rfl
  apply ContinuousAt.congr_of_eventuallyEq _ he
  apply quotient_open.continuous.continuousAt.comp
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuousAt_iff.mpr
  have hne : ∀ᶠ y in 𝓝 x, delta y ≠ 0 := open_source.mem_nhds hx
  apply ContinuousAt.congr_of_eventuallyEq continuous_affineMatrix.continuousAt
  filter_upwards [hne] with y hy
  simp [Function.comp_def, hy, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem smooth_complex_pair (i j : Fin 6) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Coordinates => (⟨x i, x j⟩ : ℂ)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Coordinates => (x i : ℂ) + (x j : ℂ) * Complex.I) := by
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ j)).mul contDiff_const)
  convert h using 1
  funext x
  apply Complex.ext <;> simp
theorem contDiff_complexCoordinates : ContDiff ℝ (⊤ : ℕ∞) complexCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [complexCoordinates]
  · exact smooth_complex_pair 0 1
  · exact smooth_complex_pair 2 3
  · exact smooth_complex_pair 4 5

theorem affine_chart_exists : ∃ C : OpenPartialHomeomorph Coordinates Group,
    C.source = affineSource ∧ C.target = affineTarget ∧
    (∀ x ∈ affineSource, C x = affinePoint x) ∧
    (∀ g ∈ affineTarget, C.symm g = affineInverse g) := by
  let C : OpenPartialHomeomorph Coordinates Group :=
    { toFun := affinePoint
      invFun := affineInverse
      source := affineSource
      target := affineTarget
      map_source' := fun _ hx => point_target _ hx
      map_target' := fun _ hg => inverse_source _ hg
      left_inv' := fun _ hx => inverse_point _ hx
      right_inv' := fun _ hg => point_inverse _ hg
      continuousOn_toFun := continuous_point
      continuousOn_invFun := continuous_inverse
      open_source := open_source
      open_target := open_target }
  exact ⟨C, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def affineChart : OpenPartialHomeomorph Coordinates Group := affine_chart_exists.choose

@[simp] theorem affineChart_source : affineChart.source = affineSource :=
  affine_chart_exists.choose_spec.1

@[simp] theorem affineChart_target : affineChart.target = affineTarget :=
  affine_chart_exists.choose_spec.2.1

theorem affineChart_apply (x : Coordinates) (hx : x ∈ affineSource) :
    affineChart x = affinePoint x := affine_chart_exists.choose_spec.2.2.1 x hx

theorem affineChart_symm_apply (g : Group) (hg : g ∈ affineTarget) :
    affineChart.symm g = affineInverse g := affine_chart_exists.choose_spec.2.2.2 g hg

@[simp] theorem zero_mem_affineSource : (0 : Coordinates) ∈ affineSource := by
  simp [affineSource, delta, complex_zero]

@[simp] theorem affinePoint_zero : affinePoint 0 = 1 := by
  unfold affinePoint
  rw [dif_pos (show delta 0 ≠ 0 from zero_mem_affineSource)]
  have he : affineMatrix 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [affineMatrix, complex_zero]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix 0)
      (by rw [affineMatrix_det]; exact zero_mem_affineSource) = 1 := Units.ext he
  rw [hg, Matrix.ProjGenLinGroup.mk_one]

@[simp] theorem affineChart_zero : affineChart 0 = 1 := by
  rw [affineChart_apply 0 zero_mem_affineSource, affinePoint_zero]

section AffineConstruction
open scoped Matrix.Norms.Elementwise

def translatedAffineChart (g : Group) : OpenPartialHomeomorph Group Coordinates :=
  (affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm

@[instance_reducible]
def affineChartedSpace : ChartedSpace Coordinates Group where
  atlas := Set.range translatedAffineChart
  chartAt := translatedAffineChart
  mem_chart_source g := by
    change g ∈ (affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).target
    rw [OpenPartialHomeomorph.trans_target]
    refine ⟨?_, ?_⟩
    · simp
    · change g⁻¹ * g ∈ affineChart.target
      simpa using affineChart.map_source (show (0 : Coordinates) ∈ affineChart.source by simp)
  chart_mem_atlas g := ⟨g, rfl⟩

def matrixRatios (a : Matrix (Fin 2) (Fin 2) ℂ) : Coordinates :=
  let u := a 1 1 / a 0 0 - 1
  let b := a 0 1 / a 0 0
  let c := a 1 0 / a 0 0
  ![u.re, u.im, b.re, b.im, c.re, c.im]

theorem contDiffAt_matrixRatios (a : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : a 0 0 ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) matrixRatios a := by
  have hd (i j : Fin 2) : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : Matrix (Fin 2) (Fin 2) ℂ => x i j / x 0 0) a := by
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Matrix (Fin 2) (Fin 2) ℂ => x i j) :=
      (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)
    simpa only [div_eq_mul_inv] using!
      (he i j).contDiffAt.mul ((he 0 0).contDiffAt.inv ha)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> simp only [matrixRatios, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  · exact (Complex.reCLM.contDiff.comp_contDiffAt a (hd 1 1)).sub contDiffAt_const
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 1 1)
  · exact Complex.reCLM.contDiff.comp_contDiffAt a (hd 0 1)
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 0 1)
  · exact Complex.reCLM.contDiff.comp_contDiffAt a (hd 1 0)
  · exact Complex.imCLM.contDiff.comp_contDiffAt a (hd 1 0)

theorem contDiff_affineMatrix : ContDiff ℝ (⊤ : ℕ∞) affineMatrix := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [affineMatrix]
  · exact contDiff_const
  · exact (contDiff_pi.mp contDiff_complexCoordinates) 1
  · exact (contDiff_pi.mp contDiff_complexCoordinates) 2
  · exact contDiff_const.add ((contDiff_pi.mp contDiff_complexCoordinates) 0)

def affineAdjugate (x : Coordinates) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 + complexCoordinates x 0, -complexCoordinates x 1;
    -complexCoordinates x 2, 1]

theorem affineAdjugate_eq (x : Coordinates) :
    affineAdjugate x = (affineMatrix x).adjugate := by
  simp [affineAdjugate, affineMatrix, Matrix.adjugate_fin_two]

theorem affineAdjugate_det (x : Coordinates) : (affineAdjugate x).det = delta x := by
  simp [affineAdjugate, delta, Matrix.det_fin_two]

theorem contDiff_affineAdjugate : ContDiff ℝ (⊤ : ℕ∞) affineAdjugate := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp [affineAdjugate]
  · exact contDiff_const.add ((contDiff_pi.mp contDiff_complexCoordinates) 0)
  · exact ((contDiff_pi.mp contDiff_complexCoordinates) 1).neg
  · exact ((contDiff_pi.mp contDiff_complexCoordinates) 2).neg
  · exact contDiff_const

theorem matrixRatios_mk (a : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    affineInverse (Matrix.ProjGenLinGroup.mk a) = matrixRatios a.val :=
  rawInverse_mk a

theorem affineAdjugate_class (x : Coordinates) (hx : x ∈ affineSource) :
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero (affineAdjugate x)
      (by rwa [affineAdjugate_det])) = (affinePoint x)⁻¹ := by
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix x)
    (by rwa [affineMatrix_det])
  let b := Matrix.GeneralLinearGroup.mkOfDetNeZero (affineAdjugate x)
    (by rwa [affineAdjugate_det])
  have hab : a * b = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (delta x) hx) := by
    apply Units.ext
    change affineMatrix x * affineAdjugate x = Matrix.scalar (Fin 2) (delta x)
    rw [affineAdjugate_eq, Matrix.mul_adjugate, affineMatrix_det]
    ext i j
    simp [Matrix.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  have hm : Matrix.ProjGenLinGroup.mk b = (Matrix.ProjGenLinGroup.mk a)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul Matrix.ProjGenLinGroup.mk, hab, Matrix.ProjGenLinGroup.mk_scalar]
  have hx' : affinePoint x = Matrix.ProjGenLinGroup.mk a := by
    unfold affinePoint
    rw [dif_pos (show delta x ≠ 0 from hx)]
  rw [hx', ← hm]

def affineTranslate (a b : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Coordinates) : Coordinates := matrixRatios (a.val * affineMatrix x * b.val)

theorem contDiffAt_affineTranslate (a b : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Coordinates) (hx : (a.val * affineMatrix x * b.val) 0 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (affineTranslate a b) x := by
  have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Coordinates => affineMatrix x i j) :=
    (contDiff_pi.mp ((contDiff_pi.mp contDiff_affineMatrix) i)) j
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Coordinates => a.val * affineMatrix x * b.val) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((contDiff_const.mul (he 0 0) |>.add (contDiff_const.mul (he 1 0))).mul
      contDiff_const).add
      ((contDiff_const.mul (he 0 1) |>.add (contDiff_const.mul (he 1 1))).mul
        contDiff_const)
  exact (contDiffAt_matrixRatios _ hx).comp x hm.contDiffAt

theorem affineTranslate_eq_inverse_translate (a b : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Coordinates) (hx : x ∈ affineSource) :
    affineTranslate a b x = affineInverse
      (Matrix.ProjGenLinGroup.mk a * affinePoint x * Matrix.ProjGenLinGroup.mk b) := by
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), ← map_mul Matrix.ProjGenLinGroup.mk,
    ← map_mul Matrix.ProjGenLinGroup.mk, matrixRatios_mk]
  rfl

theorem affineTranslate_denominator (a b : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (x : Coordinates) (hx : x ∈ affineSource) :
    (a.val * affineMatrix x * b.val) 0 0 ≠ 0 ↔
      Matrix.ProjGenLinGroup.mk a * affinePoint x * Matrix.ProjGenLinGroup.mk b ∈
        affineTarget := by
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), ← map_mul Matrix.ProjGenLinGroup.mk,
    ← map_mul Matrix.ProjGenLinGroup.mk, target_mk]
  rfl

end AffineConstruction

theorem one_mem_affineTarget : (1 : Group) ∈ affineTarget := by
  rw [← Matrix.ProjGenLinGroup.mk_one, target_mk]
  simp

open scoped Matrix.Norms.Elementwise

namespace AffineHaarFrame

def leftFrame (x : Coordinates) : Matrix (Fin 3) (Fin 3) ℂ :=
  let d := 1 + complexCoordinates x 0
  let b := complexCoordinates x 1
  let c := complexCoordinates x 2
  !![d, c, -d * b; b, 1, -(b ^ 2); 0, 0, delta x]

def leftFrameLinear (x : Coordinates) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  Matrix.toLin' (leftFrame x)

def leftFrameCLM (x : Coordinates) : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  (leftFrameLinear x).toContinuousLinearMap

def coordinatesEquiv : Coordinates ≃ₗ[ℝ] (Fin 3 → ℂ) where
  toFun := complexCoordinates
  invFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im, (z 2).re, (z 2).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp [complexCoordinates]
  map_add' x y := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp [complexCoordinates]
  map_smul' r x := by
    ext i
    fin_cases i <;> apply Complex.ext <;> simp [complexCoordinates, Complex.real_smul]

def coordinatesCLE : Coordinates ≃L[ℝ] (Fin 3 → ℂ) :=
  coordinatesEquiv.toContinuousLinearEquiv

end AffineHaarFrame

end DedekindZetaZeroFree.PGLComplex

end

section

noncomputable section
namespace DedekindZetaZeroFree.PGLComplex
open MeasureTheory Topology
open scoped Matrix.Norms.Operator Manifold ContDiff

private theorem smooth_coordinate (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Coordinates => complexCoordinates x i) := by
  exact (contDiff_pi.mp contDiff_complexCoordinates) i
theorem contDiff_delta : ContDiff ℝ (⊤ : ℕ∞) delta :=
  (contDiff_const.add (smooth_coordinate 0)).sub
    ((smooth_coordinate 1).mul (smooth_coordinate 2))

section AffineConstruction
open scoped Matrix.Norms.Elementwise

def affineMultiply (p : Coordinates × Coordinates) : Coordinates :=
  matrixRatios (affineMatrix p.1 * affineMatrix p.2)

theorem affineMultiply_denominator (x y : Coordinates) :
    (affineMatrix x * affineMatrix y) 0 0 =
      1 + complexCoordinates x 1 * complexCoordinates y 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, affineMatrix]

theorem contDiffAt_affineMultiply (p : Coordinates × Coordinates)
    (hp : 1 + complexCoordinates p.1 1 * complexCoordinates p.2 2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) affineMultiply p := by
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Coordinates × Coordinates => affineMatrix p.1 * affineMatrix p.2) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Coordinates => affineMatrix x i j) :=
      (contDiff_pi.mp ((contDiff_pi.mp contDiff_affineMatrix) i)) j
    exact ((he i 0).comp contDiff_fst |>.mul ((he 0 j).comp contDiff_snd)).add
      ((he i 1).comp contDiff_fst |>.mul ((he 1 j).comp contDiff_snd))
  apply (contDiffAt_matrixRatios _ ?_).comp p hm.contDiffAt
  rwa [affineMultiply_denominator]

def affineInvert (x : Coordinates) : Coordinates := matrixRatios (affineAdjugate x)

theorem contDiffAt_affineInvert (x : Coordinates)
    (hx : 1 + complexCoordinates x 0 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) affineInvert x := by
  apply (contDiffAt_matrixRatios _ ?_).comp x contDiff_affineAdjugate.contDiffAt
  simpa [affineAdjugate] using hx

theorem affineMultiply_eq_inverse_mul (x y : Coordinates)
    (hx : x ∈ affineSource) (hy : y ∈ affineSource) :
    affineMultiply (x, y) = affineInverse (affinePoint x * affinePoint y) := by
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), dif_pos (show delta y ≠ 0 from hy),
    ← map_mul Matrix.ProjGenLinGroup.mk, matrixRatios_mk]
  rfl

theorem affineMultiply_mem_source (x y : Coordinates)
    (hx : x ∈ affineSource) (hy : y ∈ affineSource)
    (hp : 1 + complexCoordinates x 1 * complexCoordinates y 2 ≠ 0) :
    affineMultiply (x, y) ∈ affineSource := by
  rw [affineMultiply_eq_inverse_mul x y hx hy]
  apply inverse_source
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), dif_pos (show delta y ≠ 0 from hy),
    ← map_mul Matrix.ProjGenLinGroup.mk, target_mk]
  change (affineMatrix x * affineMatrix y) 0 0 ≠ 0
  rwa [affineMultiply_denominator]

theorem affinePoint_affineMultiply (x y : Coordinates)
    (hx : x ∈ affineSource) (hy : y ∈ affineSource)
    (hp : 1 + complexCoordinates x 1 * complexCoordinates y 2 ≠ 0) :
    affinePoint (affineMultiply (x, y)) = affinePoint x * affinePoint y := by
  rw [affineMultiply_eq_inverse_mul x y hx hy]
  apply point_inverse
  unfold affinePoint
  rw [dif_pos (show delta x ≠ 0 from hx), dif_pos (show delta y ≠ 0 from hy),
    ← map_mul Matrix.ProjGenLinGroup.mk, target_mk]
  change (affineMatrix x * affineMatrix y) 0 0 ≠ 0
  rwa [affineMultiply_denominator]

theorem affineInvert_eq_inverse_inv (x : Coordinates) (hx : x ∈ affineSource) :
    affineInvert x = affineInverse (affinePoint x)⁻¹ := by
  rw [← affineAdjugate_class x hx, matrixRatios_mk]
  rfl

theorem affineInvert_mem_source (x : Coordinates) (hx : x ∈ affineSource)
    (hi : 1 + complexCoordinates x 0 ≠ 0) : affineInvert x ∈ affineSource := by
  let b := Matrix.GeneralLinearGroup.mkOfDetNeZero (affineAdjugate x)
    (by rwa [affineAdjugate_det])
  have hb : b.val 0 0 ≠ 0 := by simpa [b, affineAdjugate] using hi
  exact raw_source b hb

theorem affinePoint_affineInvert (x : Coordinates) (hx : x ∈ affineSource)
    (hi : 1 + complexCoordinates x 0 ≠ 0) :
    affinePoint (affineInvert x) = (affinePoint x)⁻¹ := by
  have he := affineInvert_eq_inverse_inv x hx
  have hs := affineInvert_mem_source x hx hi
  have ht : (affinePoint x)⁻¹ ∈ affineTarget := by
    rw [← affineAdjugate_class x hx, target_mk]
    simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero, affineAdjugate] using hi
  rw [he, point_inverse _ ht]

theorem translatedAffineChart_source (g : Group) :
    (translatedAffineChart g).source = {h | g⁻¹ * h ∈ affineTarget} := by
  ext h
  simp [translatedAffineChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.mulLeft_symm]

theorem translatedAffineChart_target (g : Group) :
    (translatedAffineChart g).target = affineSource := by
  ext x
  simp [translatedAffineChart, OpenPartialHomeomorph.trans_source]

theorem translatedAffineChart_apply (g h : Group)
    (hh : g⁻¹ * h ∈ affineTarget) :
    translatedAffineChart g h = affineInverse (g⁻¹ * h) := by
  change affineChart.symm (g⁻¹ * h) = _
  exact affineChart_symm_apply _ hh

theorem translatedAffineChart_symm_apply (g : Group) (x : Coordinates)
    (hx : x ∈ affineSource) :
    (translatedAffineChart g).symm x = g * affinePoint x := by
  change g * affineChart x = _
  rw [affineChart_apply x hx]

 theorem affine_isManifold : @IsManifold ℝ _ Coordinates _ _ Coordinates _
    (𝓘(ℝ, Coordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) Group _ affineChartedSpace := by
  letI := affineChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨g, rfl⟩ := he
  obtain ⟨h, rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id]
  intro x hx
  have hsource : ∀ y ∈ ((translatedAffineChart g).symm ≫ₕ translatedAffineChart h).source,
      y ∈ affineSource ∧ h⁻¹ * (g * affinePoint y) ∈ affineTarget := by
    intro y hy
    simp only [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source,
      translatedAffineChart_target, Set.mem_inter_iff, Set.mem_preimage] at hy
    refine ⟨hy.1, ?_⟩
    rw [translatedAffineChart_symm_apply g y hy.1, translatedAffineChart_source] at hy
    exact hy.2
  obtain ⟨hxS, ht⟩ := hsource x hx
  let a : Matrix.GeneralLinearGroup (Fin 2) ℂ := (h⁻¹ * g).out
  have ha : Matrix.ProjGenLinGroup.mk a = h⁻¹ * g := Quotient.out_eq _
  have hb : Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ) = 1 :=
    Matrix.ProjGenLinGroup.mk_one
  have hd : (a.val * affineMatrix x * (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ).val) 0 0 ≠ 0 := by
    rw [affineTranslate_denominator a 1 x hxS, ha, hb, mul_one, mul_assoc]
    exact ht
  have he : ∀ y ∈ ((translatedAffineChart g).symm ≫ₕ translatedAffineChart h).source,
      ((translatedAffineChart g).symm ≫ₕ translatedAffineChart h) y = affineTranslate a 1 y := by
    intro y hy
    obtain ⟨hyS, hy'⟩ := hsource y hy
    change translatedAffineChart h ((translatedAffineChart g).symm y) = _
    rw [translatedAffineChart_symm_apply g y hyS,
      translatedAffineChart_apply h _ hy', affineTranslate_eq_inverse_translate a 1 y hyS,
      ha, hb, mul_one, mul_assoc]
  exact ((contDiffAt_affineTranslate a 1 x hd).contDiffWithinAt).congr he (he x hx)

end AffineConstruction

set_option backward.isDefEq.respectTransparency false in
private theorem affineChart_normalized : AffineLie.NormalizedChart affineChart where
  source := affineChart_source
  target := affineChart_target
  displayed x hx := by
    change affineChart x = Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (affineMatrix x) _)
    change delta x ≠ 0 at hx
    rw [affineChart_apply x hx]
    unfold affinePoint
    rw [dif_pos hx]

open scoped Matrix.Norms.Elementwise

set_option maxHeartbeats 800000 in

theorem affine_lie_structure : ∃ C : ChartedSpace Coordinates Group,
    letI := C
    ∃ L : LieGroup (𝓘(ℝ, Coordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) Group,
      ∀ g : Group, chartAt Coordinates g =
        ((affineChart.trans (Homeomorph.mulLeft g).toOpenPartialHomeomorph).symm) := by
  refine ⟨affineChartedSpace, ?_⟩
  letI := affineChartedSpace
  haveI := affine_isManifold
  have hm : ContMDiff ((𝓘(ℝ, Coordinates)).prod (𝓘(ℝ, Coordinates)))
      (𝓘(ℝ, Coordinates)) (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : Group × Group => p.1 * p.2) := by
    intro p
    rw [contMDiffAt_iff]
    refine ⟨continuous_mul.continuousAt, ?_⟩
    rw [extChartAt_prod]
    simp only [PartialEquiv.prod_coe, PartialEquiv.prod_coe_symm,
      ModelWithCorners.range_prod, ModelWithCorners.range_eq_univ, Set.univ_prod_univ]
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id]
    change ContDiffWithinAt ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun z : Coordinates × Coordinates => translatedAffineChart (p.1 * p.2)
        ((p.1 * affineChart z.1) * (p.2 * affineChart z.2))) Set.univ
      (translatedAffineChart p.1 p.1, translatedAffineChart p.2 p.2)
    have hz (g : Group) : translatedAffineChart g g = 0 := by
      change affineChart.symm (g⁻¹ * g) = 0
      rw [inv_mul_cancel, ← affineChart_zero]
      exact affineChart.left_inv (by simp)
    rw [hz, hz]
    rw [contDiffWithinAt_univ]
    let a : Matrix.GeneralLinearGroup (Fin 2) ℂ := p.2.out
    have ha : Matrix.ProjGenLinGroup.mk a = p.2 := Quotient.out_eq _
    let F (z : Coordinates × Coordinates) :=
      matrixRatios ((a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2)
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Coordinates × Coordinates =>
          ((a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2) i j) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      have hm (i j : Fin 2) :=
        (contDiff_pi.mp ((contDiff_pi.mp contDiff_affineMatrix) i)) j
      fun_prop
    have hm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Coordinates × Coordinates =>
          (a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2) :=
      contDiff_pi.mpr (fun i => contDiff_pi.mpr (he i))
    have hmat : affineMatrix 0 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [affineMatrix, complex_zero]
    have hd : ((a⁻¹).val * affineMatrix 0 * a.val * affineMatrix 0) 0 0 ≠ 0 := by
      rw [hmat, mul_one, mul_one, ← Units.val_mul, inv_mul_cancel]
      simp
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) F (0,0) := by
      exact (contDiffAt_matrixRatios _ hd).comp (0,0) hm.contDiffAt
    apply hf.congr_of_eventuallyEq
    have hn : ∀ᶠ z : Coordinates × Coordinates in 𝓝 (0,0),
        z.1 ∈ affineSource ∧ z.2 ∈ affineSource ∧
        ((a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2) 0 0 ≠ 0 := by
      have h0 : IsOpen {z : Coordinates × Coordinates |
          z.1 ∈ affineSource ∧ z.2 ∈ affineSource ∧
          ((a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2) 0 0 ≠ 0} :=
        by
          change IsOpen (Prod.fst ⁻¹' affineSource ∩ (Prod.snd ⁻¹' affineSource ∩
            {z | ((a⁻¹).val * affineMatrix z.1 * a.val * affineMatrix z.2) 0 0 ≠ 0}))
          exact (open_source.preimage continuous_fst).inter
            ((open_source.preimage continuous_snd).inter
              (isOpen_ne_fun (he 0 0).continuous continuous_const))
      exact h0.mem_nhds ⟨by simp, by simp, hd⟩
    filter_upwards [hn] with z hz
    have hg : (p.1 * p.2)⁻¹ * (p.1 * affinePoint z.1 * (p.2 * affinePoint z.2)) ∈
        affineTarget := by
      unfold affinePoint
      rw [dif_pos (show delta z.1 ≠ 0 from hz.1),
        dif_pos (show delta z.2 ≠ 0 from hz.2.1)]
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [← ha, ← map_inv, ← map_mul Matrix.ProjGenLinGroup.mk,
        ← map_mul Matrix.ProjGenLinGroup.mk, ← map_mul Matrix.ProjGenLinGroup.mk, target_mk]
      simpa only [Units.val_mul, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, unitOfInvertible,
        mul_assoc] using hz.2.2
    rw [affineChart_apply z.1 hz.1, affineChart_apply z.2 hz.2.1,
      translatedAffineChart_apply _ _ hg]
    change _ = matrixRatios _
    unfold affinePoint
    rw [dif_pos (show delta z.1 ≠ 0 from hz.1),
      dif_pos (show delta z.2 ≠ 0 from hz.2.1)]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    rw [← ha, ← map_inv, ← map_mul Matrix.ProjGenLinGroup.mk,
      ← map_mul Matrix.ProjGenLinGroup.mk, ← map_mul Matrix.ProjGenLinGroup.mk, matrixRatios_mk]
    rfl
  have hi : ContMDiff (𝓘(ℝ, Coordinates)) (𝓘(ℝ, Coordinates))
      (↑(⊤ : ℕ∞) : ℕ∞ω) (fun g : Group => g⁻¹) := by
    intro p
    rw [contMDiffAt_iff]
    refine ⟨continuous_inv.continuousAt, ?_⟩
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      ModelWithCorners.range_eq_univ]
    rw [Set.range_id]
    change ContDiffWithinAt ℝ (↑(⊤ : ℕ∞) : ℕ∞ω)
      (fun z : Coordinates => translatedAffineChart p⁻¹ (p * affineChart z)⁻¹)
      Set.univ (translatedAffineChart p p)
    have hz : translatedAffineChart p p = 0 := by
      change affineChart.symm (p⁻¹ * p) = 0
      rw [inv_mul_cancel, ← affineChart_zero]
      exact affineChart.left_inv (by simp)
    rw [hz, contDiffWithinAt_univ]
    let a : Matrix.GeneralLinearGroup (Fin 2) ℂ := p.out
    have ha : Matrix.ProjGenLinGroup.mk a = p := Quotient.out_eq _
    let F (z : Coordinates) := matrixRatios (a.val * affineAdjugate z * (a⁻¹).val)
    have he (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Coordinates => (a.val * affineAdjugate z * (a⁻¹).val) i j) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      have hm (i j : Fin 2) :=
        (contDiff_pi.mp ((contDiff_pi.mp contDiff_affineAdjugate) i)) j
      fun_prop
    have hm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Coordinates => a.val * affineAdjugate z * (a⁻¹).val) :=
      contDiff_pi.mpr (fun i => contDiff_pi.mpr (he i))
    have hmat : affineAdjugate 0 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [affineAdjugate, complex_zero]
    have hd : (a.val * affineAdjugate 0 * (a⁻¹).val) 0 0 ≠ 0 := by
      rw [hmat, mul_one, ← Units.val_mul, mul_inv_cancel]
      simp
    have hf : ContDiffAt ℝ (⊤ : ℕ∞) F 0 := by
      exact (contDiffAt_matrixRatios _ hd).comp 0 hm.contDiffAt
    apply hf.congr_of_eventuallyEq
    have hn : ∀ᶠ z : Coordinates in 𝓝 0, z ∈ affineSource ∧
        (a.val * affineAdjugate z * (a⁻¹).val) 0 0 ≠ 0 :=
      (open_source.inter (isOpen_ne_fun (he 0 0).continuous continuous_const)).mem_nhds
        ⟨zero_mem_affineSource, hd⟩
    filter_upwards [hn] with z hz
    let b := Matrix.GeneralLinearGroup.mkOfDetNeZero (affineAdjugate z)
      (by rw [affineAdjugate_det]; exact hz.1)
    have hb : Matrix.ProjGenLinGroup.mk b = (affinePoint z)⁻¹ :=
      affineAdjugate_class z hz.1
    have heq : p * (p * affinePoint z)⁻¹ = Matrix.ProjGenLinGroup.mk (a * b * a⁻¹) := by
      rw [map_mul, map_mul, map_inv, ha, hb, mul_inv_rev, mul_assoc]
    have ht : (p⁻¹)⁻¹ * (p * affinePoint z)⁻¹ ∈ affineTarget := by
      rw [inv_inv, heq, target_mk]
      change (a.val * affineAdjugate z * (a⁻¹).val) 0 0 ≠ 0
      exact hz.2
    rw [affineChart_apply z hz.1, translatedAffineChart_apply _ _ ht,
      inv_inv, heq, matrixRatios_mk]
    rfl
  refine ⟨?_, fun _ => rfl⟩
  exact { toIsManifold := affine_isManifold
          contMDiff_mul := hm
          contMDiff_inv := hi }

namespace AffineHaarFrame

theorem leftFrame_det (x : Coordinates) : (leftFrame x).det = delta x ^ 2 := by
  simp [leftFrame, Matrix.det_fin_three, delta]
  ring

theorem leftFrame_det_ne_zero (x : Coordinates) (hx : x ∈ affineSource) :
    (leftFrame x).det ≠ 0 := by
  rw [leftFrame_det]
  exact pow_ne_zero _ hx

theorem leftFrame_real_det (x : Coordinates) :
    ((leftFrameLinear x).restrictScalars ℝ).det = ‖delta x‖ ^ 4 := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have h : (leftFrameLinear x).det = delta x ^ 2 := by
    rw [leftFrameLinear, LinearMap.det_toLin', leftFrame_det]
  rw [h, Complex.normSq_eq_norm_sq, norm_pow]
  ring

def complexLeft (x : Coordinates) (z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  let d := 1 + complexCoordinates x 0
  let b := complexCoordinates x 1
  let c := complexCoordinates x 2
  ![(c * z 1 + d * (1 + z 0)) / (1 + b * z 2) - 1,
    (z 1 + b * (1 + z 0)) / (1 + b * z 2),
    (c + d * z 2) / (1 + b * z 2)]

theorem complexLeft_affineMultiply (x y : Coordinates) :
    complexCoordinates (affineMultiply (x, y)) = complexLeft x (complexCoordinates y) := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [affineMultiply, matrixRatios, complexCoordinates, complexLeft,
      Matrix.mul_apply, Fin.sum_univ_two, affineMatrix]

theorem complexLeft_hasFDerivAt (x : Coordinates) :
    HasFDerivAt (complexLeft x) (leftFrameCLM x) 0 := by
  let P (i : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have hp (i : Fin 3) : HasFDerivAt (fun z : Fin 3 → ℂ => z i) (P i) 0 :=
    (P i).hasFDerivAt
  let d := 1 + complexCoordinates x 0
  let b := complexCoordinates x 1
  let c := complexCoordinates x 2
  have hden : HasFDerivAt (fun z : Fin 3 → ℂ => 1 + b * z 2) (b • P 2) 0 := by
    simpa using (hp 2).const_mul b |>.const_add 1
  have hi : HasFDerivAt (fun z : Fin 3 → ℂ => (1 + b * z 2)⁻¹) (-b • P 2) 0 := by
    have hi0 : HasFDerivAt (fun z : ℂ => z⁻¹)
        (-ContinuousLinearMap.mulLeftRight ℂ ℂ 1 1) (1 + b * (0 : Fin 3 → ℂ) 2) := by
      simpa using (hasFDerivAt_inv' (𝕜 := ℂ) (R := ℂ) (x := 1) (by norm_num))
    convert hi0.comp 0 hden using 1 <;>
      ext z <;> simp [P, ContinuousLinearMap.mulLeftRight_apply]
  have hu := ((hp 1).const_mul c |>.add ((hp 0).const_add 1 |>.const_mul d)).mul hi |>.sub_const 1
  have hb := ((hp 1).add ((hp 0).const_add 1 |>.const_mul b)).mul hi
  have hc := ((hp 2).const_mul d |>.const_add c).mul hi
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · convert hu using 1 <;> ext z <;>
      simp [complexLeft, div_eq_mul_inv, leftFrameCLM, leftFrameLinear,
        leftFrame, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, P, d, b, c] <;> ring
  · convert hb using 1 <;> ext z <;>
      simp [complexLeft, div_eq_mul_inv, leftFrameCLM, leftFrameLinear,
        leftFrame, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, P, d, b, c] <;> ring
  · convert hc using 1 <;> ext z <;>
      simp [complexLeft, div_eq_mul_inv, leftFrameCLM, leftFrameLinear,
        leftFrame, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, P, d, b, c, delta] <;> ring

def realFrame (x : Coordinates) : Coordinates →L[ℝ] Coordinates :=
  coordinatesCLE.symm.toContinuousLinearMap.comp
    (((leftFrameCLM x).restrictScalars ℝ).comp coordinatesCLE.toContinuousLinearMap)

theorem realFrame_det (x : Coordinates) : (realFrame x).toLinearMap.det = ‖delta x‖ ^ 4 := by
  change (coordinatesEquiv.symm.toLinearMap.comp
    (((leftFrameLinear x).restrictScalars ℝ).comp coordinatesEquiv.toLinearMap)).det = _
  simpa using (LinearMap.det_conj ((leftFrameLinear x).restrictScalars ℝ)
    coordinatesEquiv.symm).trans (leftFrame_real_det x)

theorem affineMultiply_hasFDerivAt (x : Coordinates) :
    HasFDerivAt (fun y => affineMultiply (x, y)) (realFrame x) 0 := by
  have hzero : coordinatesCLE (0 : Coordinates) = 0 := map_zero coordinatesCLE
  have hc : HasFDerivAt (complexLeft x) ((leftFrameCLM x).restrictScalars ℝ)
      (coordinatesCLE 0) := by
    rw [hzero]
    exact (complexLeft_hasFDerivAt x).restrictScalars ℝ
  have h := (coordinatesCLE.symm.toContinuousLinearMap.hasFDerivAt).comp 0
    (hc.comp 0 coordinatesCLE.toContinuousLinearMap.hasFDerivAt)
  have he : (fun y => coordinatesCLE.symm (complexLeft x (coordinatesCLE y))) =
      (fun y => affineMultiply (x, y)) := by
    funext y
    apply coordinatesEquiv.injective
    change coordinatesEquiv (coordinatesEquiv.symm _) = _
    rw [coordinatesEquiv.apply_symm_apply]
    exact (complexLeft_affineMultiply x y).symm
  change HasFDerivAt (fun y => coordinatesCLE.symm (complexLeft x (coordinatesCLE y)))
    (realFrame x) 0 at h
  rwa [he] at h

end AffineHaarFrame

set_option backward.isDefEq.respectTransparency false in

theorem affine_haar_density (μ : Measure Group) [μ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      Measure.map affineChart.symm (μ.restrict affineTarget) =
        (volume.withDensity (fun x : Coordinates =>
          ENNReal.ofReal (c / ‖delta x‖ ^ 4))).restrict affineSource := by
  rcases affine_lie_structure with ⟨C, L, hc⟩
  letI := C
  letI := L
  obtain ⟨ν, hν, hd⟩ := AffineLie.normalized_frame_haar
    affineChart affineChart_normalized hc AffineHaarFrame.realFrame
    AffineHaarFrame.affineMultiply_hasFDerivAt AffineHaarFrame.realFrame_det
  letI := hν
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
    change LocallyCompactSpace (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : LocallyCompactSpace Group := by
    change LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
    change SecondCountableTopology (Fin 2 → Fin 2 → ℂ)
    infer_instance
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology Group := by
    change SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸ Subgroup.center _)
    infer_instance
  have hw : Measurable (fun x : Coordinates => 1 / ‖delta x‖ ^ 4) := by
    exact measurable_const.div (contDiff_delta.continuous.measurable.norm.pow_const 4)
  obtain ⟨c, hcpos, he⟩ := AffineLie.haar_chart_density_comparison
    affineChart (fun x => 1 / ‖delta x‖ ^ 4) hw μ ν hd
  refine ⟨c, hcpos, ?_⟩
  simpa only [affineChart_source, affineChart_target, mul_one_div] using he

end DedekindZetaZeroFree.PGLComplex

end
end
