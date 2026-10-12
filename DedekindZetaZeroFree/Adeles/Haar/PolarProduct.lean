module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxisSheetDisintegration
public import DedekindZetaZeroFree.Theta.Profiles.FiniteAdditiveLevelsAndAnnihilators

@[expose] public section

namespace DedekindZetaZeroFree.ThetaPositiveSheetMellin
noncomputable section
open MeasureTheory NumberField
open scoped Classical ENNReal
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

instance archMeasurableSpace (w : InfinitePlace F) : MeasurableSpace w.Completionˣ :=
  borel _

instance finiteMeasurableSpace (A : SArithmeticData F) (v : A.Sf) :
    MeasurableSpace (ThetaFiniteCutoff.LocalUnits A v) := borel _

instance archBorelSpace (w : InfinitePlace F) : BorelSpace w.Completionˣ := ⟨rfl⟩

instance finiteBorelSpace (A : SArithmeticData F) (v : A.Sf) :
    BorelSpace (ThetaFiniteCutoff.LocalUnits A v) := ⟨rfl⟩

def polarUnit (A : SArithmeticData F) (w : InfinitePlace F)
    (p : ThetaProfileHaarSheets.PositiveAxis × Circle) : w.Completionˣ :=
  ThetaProfileHaarSheets.sqrtUnit A w p.1 *
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (A.complex_place w)).symm.toMonoidHom p.2.toUnits

def archHaar (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) : Measure w.Completionˣ :=
  Measure.map (polarUnit A w) (ThetaProfileHaarSheets.positiveHaar.prod ν)

def productHaar (A : SArithmeticData F)
    (μ : ∀ v : A.Sf, Measure (ThetaFiniteCutoff.LocalUnits A v))
    (ν : InfinitePlace F → Measure Circle) : Measure A.G :=
  @Measure.map _ A.G
    (Prod.instMeasurableSpace) (ThetaProfileHaarSheets.groupMeasurableSpace A)
    (fun p => p)
    ((Measure.pi (fun w => archHaar A w (ν w))).prod (Measure.pi μ))

abbrev PA := ThetaProfileHaarSheets.PositiveAxis
 instance instLocallyCompactSpacePolarHaarPositiveAxis : LocallyCompactSpace PA := isOpen_Ioi.locallyCompactSpace
 instance instIsTopologicalGroupPolarHaarPositiveAxis : IsTopologicalGroup PA where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.inv₀ (fun x => x.property.ne')
 def complexPolar (p : PA × Circle) : ℂˣ :=
  Units.mk0 ((Real.sqrt (p.1 : ℝ) : ℂ) * p.2) (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.1.property).ne') p.2.coe_ne_zero)
 def polarInverse (z : ℂˣ) : PA × Circle :=
  (⟨‖(z : ℂ)‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)⟩,
    ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
      apply mem_sphere_zero_iff_norm.mpr
      simp [norm_div, norm_pos_iff.mpr z.ne_zero, z.ne_zero]⟩)
 theorem complexPolar_left_inv (p : PA × Circle) :
    polarInverse (complexPolar p) = p := by
  rcases p with ⟨⟨t, ht⟩, w⟩
  have hs := Real.sqrt_pos.mpr ht
  apply Prod.ext
  · apply Subtype.ext
    simp [polarInverse, complexPolar, norm_mul, abs_of_pos hs, Real.sq_sqrt ht.le]
  · apply Circle.ext
    simp [polarInverse, complexPolar, norm_mul, abs_of_pos hs]
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne']
 theorem complexPolar_right_inv (z : ℂˣ) :
    complexPolar (polarInverse z) = z := by
  apply Units.ext
  simp [complexPolar, polarInverse, Real.sqrt_sq (norm_nonneg _)]
  field_simp
 theorem complexPolar_mul (p q : PA × Circle) :
    complexPolar (p * q) = complexPolar p * complexPolar q := by
  apply Units.ext
  have h : ((p.1 * q.1 : PA) : ℝ) = (p.1 : ℝ) * (q.1 : ℝ) := rfl
  simp only [complexPolar, Units.val_mk0, Units.val_mul, Prod.fst_mul, Prod.snd_mul,
    h, Circle.coe_mul, Real.sqrt_mul p.1.property.le, Complex.ofReal_mul]
  ring
 theorem complexPolar_continuous : Continuous complexPolar := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_subtype_val.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)
 theorem polarInverse_continuous : Continuous polarInverse := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact Units.continuous_val.norm.pow 2
  · apply Continuous.subtype_mk
    exact Units.continuous_val.div
      (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))
 def complexPolarEquiv : (PA × Circle) ≃ₜ* ℂˣ where
  toFun := complexPolar
  invFun := polarInverse
  left_inv := complexPolar_left_inv
  right_inv := complexPolar_right_inv
  map_mul' := complexPolar_mul
  continuous_toFun := complexPolar_continuous
  continuous_invFun := polarInverse_continuous
 def completionUnitsEquiv (A : SArithmeticData F) (w : InfinitePlace F) :
    ℂˣ ≃ₜ* w.Completionˣ where
  toMulEquiv := Units.mapEquiv
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm.toMulEquiv
  continuous_toFun := Units.continuous_map
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).symm.continuous
  continuous_invFun := Units.continuous_map
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).continuous
def polarEquiv (A : SArithmeticData F) (w : InfinitePlace F) :
    (PA × Circle) ≃ₜ* w.Completionˣ :=
  complexPolarEquiv.trans (completionUnitsEquiv A w)
theorem polarEquiv_eq (A : SArithmeticData F) (w : InfinitePlace F)
    (p : PA × Circle) : polarEquiv A w p = polarUnit A w p := by
  apply Units.ext
  simp [polarEquiv, completionUnitsEquiv, complexPolarEquiv, complexPolar,
    polarUnit, ThetaProfileHaarSheets.sqrtUnit, Units.mapEquiv, Units.map,
    map_mul]

instance archHaar_isHaarMeasure (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [ν.IsHaarMeasure] : (archHaar A w ν).IsHaarMeasure := by
  have h : polarUnit A w = polarEquiv A w := funext (fun p => (polarEquiv_eq A w p).symm)
  unfold archHaar
  rw [h]
  exact (polarEquiv A w).isHaarMeasure_map _

theorem groupMeasurableSpace_eq_prod (A : SArithmeticData F) :
    ThetaProfileHaarSheets.groupMeasurableSpace A = Prod.instMeasurableSpace := by
  haveI hc : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w => by
    rcases InfinitePlace.isReal_or_isComplex w with h | h
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal h).toHomeomorph.isInducing
        |>.secondCountableTopology
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex h).toHomeomorph.isInducing
        |>.secondCountableTopology
  haveI hu : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ := fun w => by
    haveI := hc w
    exact (unitsHomeomorphNeZero (G₀ := w.Completion)).isInducing.secondCountableTopology
  haveI hf : ∀ v : A.Sf, SecondCountableTopology (ThetaFiniteCutoff.LocalUnits A v) := fun v => by
    exact (unitsHomeomorphNeZero (G₀ := v.val.adicCompletion F)).isInducing.secondCountableTopology
  letI : MeasurableSpace A.G := Prod.instMeasurableSpace
  exact (Prod.borelSpace (α := (w : InfinitePlace F) → w.Completionˣ)
    (β := (v : A.Sf) → ThetaFiniteCutoff.LocalUnits A v)).measurable_eq.symm

instance productHaar_isHaarMeasure (A : SArithmeticData F)
    (μ : ∀ v : A.Sf, Measure (ThetaFiniteCutoff.LocalUnits A v))
    (ν : InfinitePlace F → Measure Circle)
    [∀ v, (μ v).IsHaarMeasure] [∀ w, (ν w).IsHaarMeasure] :
    (productHaar A μ ν).IsHaarMeasure := by
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ v : A.Sf, TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    fun v => TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI : ∀ v : A.Sf, SecondCountableTopology (ThetaFiniteCutoff.LocalUnits A v) :=
    fun v => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ w : InfinitePlace F, LocallyCompactSpace w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : ∀ w : InfinitePlace F, SigmaFinite (archHaar A w (ν w)) := fun w => inferInstance
  haveI : ∀ v : A.Sf, SigmaFinite (μ v) := fun v => inferInstance
  have hm : (Prod.instMeasurableSpace : MeasurableSpace A.G) =
      ThetaProfileHaarSheets.groupMeasurableSpace A := by
    exact BorelSpace.measurable_eq
  unfold productHaar
  rw [← hm, Measure.map_id']
  infer_instance

end
end DedekindZetaZeroFree.ThetaPositiveSheetMellin
