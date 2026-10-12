module

public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceCharacter
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexIntertwinerImageAndHarmonicExtraction

@[expose] public section

noncomputable section
open NumberField
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPReferenceChange.StandardComplexImage
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (w : InfinitePlace F)

abbrev Cover := KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w)
abbrev Group := KPPGLLocalCover.CubicPGL2 F A.zeta12 A.primitive_zeta12 (Sum.inl w)

def coordinate : KPHilbert.Completion F (Sum.inl w) ≃+* ℂ :=
  InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F A.zeta12 A.primitive_zeta12 w)

def frequency : ℂˣ := Units.mk0 ((4 * Real.pi : ℝ) : ℂ) (by
  exact Complex.ofReal_ne_zero.mpr (by positivity))

@[simp] theorem frequency_coe : (frequency : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := rfl

theorem trace_character (x : KPHilbert.Completion F (Sum.inl w)) :
    archTraceCharacter w x = character (frequency : ℂ) (coordinate A w x) := by
  rw [archTraceCharacter_of_isComplex w
    (KPHilbert.infinite_isComplex F A.zeta12 A.primitive_zeta12 w)]
  change Circle.exp (2 * Real.pi * (2 * (coordinate A w x).re)) =
    Circle.exp ((((4 * Real.pi : ℝ) : ℂ) * coordinate A w x).re)
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def epsilonHom : Cover A w →* rootsOfUnity 3 F where
  toFun g := g.epsilon
  map_one' := rfl
  map_mul' g h := by
    rw [KPLocalCover.mul_epsilon,
      KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]

def rawCentralCharacter : Cover A w →* ℂˣ :=
  (KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12).comp
    (epsilonHom A w)

 theorem splitScalars_central_kernel :
    KPPGLLocalCover.splitScalarSubgroup F A.zeta12 A.primitive_zeta12 (Sum.inl w) ≤
      (rawCentralCharacter A w).ker := by
  rintro g ⟨z, rfl⟩
  change KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12
    (KPScalarSplitCentral.scalarHom F A.zeta12 A.primitive_zeta12 (Sum.inl w) z).epsilon = 1
  change KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12 1 = 1
  exact map_one _

def centralCharacter : Group A w →* ℂˣ :=
  QuotientGroup.lift _ (rawCentralCharacter A w) (splitScalars_central_kernel A w)

@[simp] theorem centralCharacter_quotient (g : Cover A w) :
    centralCharacter A w (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12
      (Sum.inl w) g) =
    KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12 g.epsilon := rfl

def rawMatrix : Cover A w →* ComplexPGL2 :=
  Matrix.ProjGenLinGroup.mk.comp
    ((Matrix.GeneralLinearGroup.map (coordinate A w).toRingHom).comp
      (KPLocalCover.projection F A.zeta12 A.primitive_zeta12 (Sum.inl w)))

 theorem splitScalars_matrix_kernel :
    KPPGLLocalCover.splitScalarSubgroup F A.zeta12 A.primitive_zeta12 (Sum.inl w) ≤
      (rawMatrix A w).ker := by
  rintro g ⟨z, rfl⟩
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (coordinate A w).toRingHom
      (KPLocalCover.projection F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        (KPScalarSplitCentral.scalarHom F A.zeta12 A.primitive_zeta12 (Sum.inl w) z))) = 1
  rw [KPScalarSplitCentral.projection_scalarHom]
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def matrix : Group A w →* ComplexPGL2 :=
  QuotientGroup.lift _ (rawMatrix A w) (splitScalars_matrix_kernel A w)

@[simp] theorem matrix_quotient (g : Cover A w) :
    matrix A w (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w) g) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
        (coordinate A w).toRingHom g.g) := rfl

def action (g : Group A w) (h : Theta frequency) : Theta frequency :=
  (centralCharacter A w g : ℂ) • imageAction frequency (matrix A w g) h

private theorem image_smul (β : ℂˣ) (g : ComplexPGL2) (a : ℂ) (h : Theta β) :
    imageAction β g (a • h) = a • imageAction β g h := by
  induction g using Quotient.inductionOn with
  | _ g =>
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl

@[simp] theorem action_one (h : Theta frequency) : action A w 1 h = h := by
  unfold action
  simp only [map_one, Units.val_one, one_smul]
  apply Subtype.ext
  exact pi_one _ _

theorem action_mul (g h : Group A w) (f : Theta frequency) :
    action A w (g * h) f = action A w g (action A w h f) := by
  unfold action
  rw [map_mul, map_mul, Units.val_mul, image_smul, smul_smul]
  congr 1
  apply Subtype.ext
  exact pi_mul _ _ _ _

def splitMatrix : ComplexGL2 →* Group A w where
  toFun g := KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
    (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
      (Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom g))
  map_one' := by
    change KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
      (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        ((Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom) 1)) = 1
    rw [map_one]
    exact map_one _
  map_mul' g h := by
    change KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
      (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        ((Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom) (g * h))) = _
    rw [map_mul, ← map_mul]
    apply congrArg (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w))
    change (KPLocalCover.CubicGL2Raw.mk _ 1 : Cover A w) = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · exact map_mul _ _ _
    · rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
      simp

@[simp] theorem centralCharacter_splitMatrix (g : ComplexGL2) :
    centralCharacter A w (splitMatrix A w g) = 1 := by
  change KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12 1 = 1
  exact map_one _

private theorem map_coordinate_inverse (g : ComplexGL2) :
    Matrix.GeneralLinearGroup.map (coordinate A w).toRingHom
      (Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom g) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change coordinate A w ((coordinate A w).symm (g i j)) = g i j
  exact RingEquiv.apply_symm_apply _ _

@[simp] theorem matrix_splitMatrix (g : ComplexGL2) :
    matrix A w (splitMatrix A w g) = Matrix.ProjGenLinGroup.mk g := by
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (coordinate A w).toRingHom
      (Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom g)) = _
  rw [map_coordinate_inverse]

@[simp] theorem action_splitMatrix (g : ComplexGL2) (h : Theta frequency) :
    action A w (splitMatrix A w g) h =
      imageAction frequency (Matrix.ProjGenLinGroup.mk g) h := by
  unfold action
  rw [centralCharacter_splitMatrix, matrix_splitMatrix, Units.val_one, one_smul]

theorem standard_upper (x : KPHilbert.Completion F (Sum.inl w)) :
    splitMatrix A w (upperUnipotent (coordinate A w x)) =
      KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        (KPStandardLocalRootLifts.N F A.zeta12 A.primitive_zeta12 (Sum.inl w) x) := by
  change KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
    (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
      (Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom
        (upperUnipotent (coordinate A w x)))) = _
  apply congrArg (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w))
  apply congrArg (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w))
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, KubotaRankTwo.n]

theorem standard_diagonal (y : (KPHilbert.Completion F (Sum.inl w))ˣ) :
    splitMatrix A w (diagonal (Units.map (coordinate A w).toMonoidHom y)) =
      KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
        (KPStandardLocalRootLifts.A F A.zeta12 A.primitive_zeta12 (Sum.inl w) y) := by
  change KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w)
    (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
      (Matrix.GeneralLinearGroup.map (coordinate A w).symm.toRingHom
        (diagonal (Units.map (coordinate A w).toMonoidHom y)))) = _
  apply congrArg (KPPGLLocalCover.coverQuotient F A.zeta12 A.primitive_zeta12 (Sum.inl w))
  apply congrArg (KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w))
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, KubotaRankTwo.d]

def compactLift : ComplexSU2 →* Group A w := (splitMatrix A w).comp complexSU2Embedding

@[simp] theorem compact_scalar_one (k : ComplexSU2) :
    centralCharacter A w (compactLift A w k) = 1 := centralCharacter_splitMatrix A w _

@[simp] theorem compact_matrix (k : ComplexSU2) :
    matrix A w (compactLift A w k) = Matrix.ProjGenLinGroup.mk (complexSU2Embedding k) :=
  matrix_splitMatrix A w _

end DedekindZetaZeroFree.KPReferenceChange.StandardComplexImage

end
