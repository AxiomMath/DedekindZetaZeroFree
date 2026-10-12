module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxisSheetDisintegration
public import DedekindZetaZeroFree.Adeles.Quotients.MultiplicativeBalancedTilingAndIntegration

@[expose] public section

open MeasureTheory NumberField
open scoped ENNReal Topology Pointwise

namespace DedekindZetaZeroFree.ThetaSheetExactUnfolding

noncomputable section
set_option autoImplicit false

open ThetaProfileHaarSheets

variable {F : Type} [Field F] [NumberField F]

 theorem norm_mul' (A : SArithmeticData F) (y z : A.G) :
    A.norm (y * z) = A.norm y * A.norm z := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

 theorem norm_inv' (A : SArithmeticData F) (y : A.G) :
    A.norm y⁻¹ = (A.norm y)⁻¹ := by
  simp only [SArithmeticData.norm, Prod.fst_inv, Prod.snd_inv, Pi.inv_apply,
    Units.val_inv_eq_inv_val, norm_inv, inv_pow, Finset.prod_inv_distrib, mul_inv]

 theorem norm_div' (A : SArithmeticData F) (y z : A.G) :
    A.norm (y / z) = A.norm y / A.norm z := by
  simp only [div_eq_mul_inv, norm_mul', norm_inv']

 instance groupSecondCountable (A : SArithmeticData F) : SecondCountableTopology A.G := by
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI : ∀ v : A.Sf, SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    fun v => Units.isEmbedding_val₀.secondCountableTopology
  infer_instance

 instance kernelSecondCountable (A : SArithmeticData F) : SecondCountableTopology A.G1 :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance sheetMulAction (A : SArithmeticData F) (x : PositiveAxis) :
    MulAction A.Gamma1 (Sheet A x) where
  smul γ y := ⟨γ.val.val * y.val, by
    rw [norm_mul', show A.norm γ.val.val = 1 from γ.val.property, y.property, one_mul]⟩
  one_smul := by
    intro y
    exact Subtype.ext (one_mul y.val)
  mul_smul := by
    intro γ δ y
    exact Subtype.ext (mul_assoc γ.val.val δ.val.val y.val)

theorem exists_sheetFundamentalDomain (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (x : PositiveAxis) :
    ∃ Ω : Set (Sheet A x),
      MeasurableSet Ω ∧ IsCompact (closure Ω) ∧
      (∀ y : Sheet A x, ∃! γ : A.Gamma1, γ • y ∈ Ω) ∧
      IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x) := by
  obtain ⟨K, D, _, _, hD, hDc, _, htiling⟩ :=
    A.exists_multiplicative_quotient_balanced_tiling
  let e := sheetTranslation A v₀ x
  let Ω := e '' D
  have hD' : MeasurableSet D := by
    convert hD using 1 <;> exact (BorelSpace.measurable_eq (α := A.G1))
  have hΩ : MeasurableSet Ω := e.measurableEmbedding.measurableSet_image.mpr hD'
  have hΩc : IsCompact (closure Ω) := by
    rw [show closure Ω = e '' closure D from e.image_closure D |>.symm]
    exact hDc.image e.continuous
  have he (γ : A.Gamma1) (z : A.G1) : e (γ.val * z) = γ • e z := by
    apply Subtype.ext
    change normSection A v₀ x * (γ.val.val * z.val) =
      γ.val.val * (normSection A v₀ x * z.val)
    ac_rfl
  have ht : ∀ y : Sheet A x, ∃! γ : A.Gamma1, γ • y ∈ Ω := by
    intro y
    obtain ⟨γ, hγ, hu⟩ := htiling (e.symm y)
    have hm (δ : A.Gamma1) : δ • y ∈ Ω ↔ δ.val * e.symm y ∈ D := by
      rw [← e.apply_symm_apply y, ← he]
      simpa only [Ω, e.symm_apply_apply] using (e.injective.mem_set_image (s := D) (a := δ.val * e.symm y))
    exact ⟨γ, (hm γ).mpr hγ, fun δ hδ => hu δ ((hm δ).mp hδ)⟩
  exact ⟨Ω, hΩ, hΩc, ht, IsFundamentalDomain.mk' hΩ.nullMeasurableSet ht⟩

abbrev SheetQuotient (A : SArithmeticData F) (x : PositiveAxis) :=
  Quotient (MulAction.orbitRel A.Gamma1 (Sheet A x))

def sheetProjection (A : SArithmeticData F) (x : PositiveAxis) :
    Sheet A x → SheetQuotient A x :=
  Quotient.mk (MulAction.orbitRel A.Gamma1 (Sheet A x))

 instance sheetContinuousConstSMul (A : SArithmeticData F) (x : PositiveAxis) :
    ContinuousConstSMul A.Gamma1 (Sheet A x) where
  continuous_const_smul γ := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

 instance sheetInvariant (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : PositiveAxis) :
    SMulInvariantMeasure A.Gamma1 (Sheet A x) (sheetHaar A v₀ μG x) := by
  have he (γ : A.Gamma1) (z : A.G1) :
      sheetTranslation A v₀ x (γ • z) = γ • sheetTranslation A v₀ x z := by
    apply Subtype.ext
    change normSection A v₀ x * (γ.val.val * z.val) =
      γ.val.val * (normSection A v₀ x * z.val)
    ac_rfl
  exact smulInvariantMeasure_map (kernelHaar A v₀ μG) (sheetTranslation A v₀ x)
    he (sheetTranslation A v₀ x).measurable

theorem exists_unique_sheetQuotientHaar (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (x : PositiveAxis) :
    ∃! ν : Measure (SheetQuotient A x),
      QuotientMeasureEqMeasurePreimage (sheetHaar A v₀ μG x) ν := by
  obtain ⟨Ω, _, _, _, hΩ⟩ := exists_sheetFundamentalDomain A v₀ μG x
  let ν := Measure.map (sheetProjection A x) ((sheetHaar A v₀ μG x).restrict Ω)
  have hv : QuotientMeasureEqMeasurePreimage (sheetHaar A v₀ μG x) ν :=
    hΩ.quotientMeasureEqMeasurePreimage_quotientMeasure
  refine ⟨ν, hv, ?_⟩
  intro ν' hv'
  letI := hv'
  exact hΩ.projection_respects_measure ν'

def sheetQuotientHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : PositiveAxis) :
    Measure (SheetQuotient A x) :=
  Classical.choose (exists_unique_sheetQuotientHaar A v₀ μG x)

theorem sheetQuotientHaar_eq (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : PositiveAxis)
    (Ω : Set (Sheet A x))
    (hΩ : IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x)) :
    sheetQuotientHaar A v₀ μG x =
      Measure.map (sheetProjection A x) ((sheetHaar A v₀ μG x).restrict Ω) := by
  letI : QuotientMeasureEqMeasurePreimage (sheetHaar A v₀ μG x)
      (sheetQuotientHaar A v₀ μG x) :=
    (Classical.choose_spec (exists_unique_sheetQuotientHaar A v₀ μG x)).1
  exact hΩ.projection_respects_measure (sheetQuotientHaar A v₀ μG x)

theorem sheetProjection_measurePreserving (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (x : PositiveAxis) (Ω : Set (Sheet A x))
    (hΩ : IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x)) :
    MeasurePreserving (sheetProjection A x)
      ((sheetHaar A v₀ μG x).restrict Ω) (sheetQuotientHaar A v₀ μG x) := by
  exact ⟨measurable_quotient_mk' (s := MulAction.orbitRel A.Gamma1 (Sheet A x)), (sheetQuotientHaar_eq A v₀ μG x Ω hΩ).symm⟩

def q (A : SArithmeticData F) (a : Fˣ) : PositiveAxis :=
  ⟨A.norm (A.diagonal a), norm_positive A (A.diagonal a)⟩

def sheetMul (A : SArithmeticData F) (a : Fˣ) (x : PositiveAxis) :
    Sheet A x ≃ₜ Sheet A (q A a * x) where
  toFun y := ⟨A.diagonal a * y.val, by
    change A.norm (A.diagonal a * y.val) = A.norm (A.diagonal a) * x.val
    rw [norm_mul', y.property]⟩
  invFun v := ⟨(A.diagonal a)⁻¹ * v.val, by
    rw [norm_mul', norm_inv', v.property]
    change (A.norm (A.diagonal a))⁻¹ * (A.norm (A.diagonal a) * x.val) = x.val
    simp [← mul_assoc, ne_of_gt (norm_positive A (A.diagonal a))]⟩
  left_inv := by
    intro y
    exact Subtype.ext (inv_mul_cancel_left _ _)
  right_inv := by
    intro v
    exact Subtype.ext (mul_inv_cancel_left _ _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

def sheetDiv (A : SArithmeticData F) (a : Fˣ) (x : PositiveAxis) :
    Sheet A x ≃ₜ Sheet A (q A a / x) where
  toFun y := ⟨A.diagonal a / y.val, by
    change A.norm (A.diagonal a / y.val) = A.norm (A.diagonal a) / x.val
    rw [norm_div', y.property]⟩
  invFun v := ⟨A.diagonal a / v.val, by
    rw [norm_div', v.property]
    change A.norm (A.diagonal a) / (A.norm (A.diagonal a) / x.val) = x.val
    field_simp [ne_of_gt (norm_positive A (A.diagonal a))]⟩
  left_inv := by
    intro y
    exact Subtype.ext (div_div_cancel _ _)
  right_inv := by
    intro v
    exact Subtype.ext (div_div_cancel _ _)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.div' continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.div' continuous_subtype_val

theorem sheetDiv_val (A : SArithmeticData F) (a : Fˣ) (x : PositiveAxis)
    (y : Sheet A x) : (sheetDiv A a x y).val = A.diagonal a / y.val := rfl

theorem sheetMul_measurePreserving (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (a : Fˣ) (x : PositiveAxis) :
    MeasurePreserving (sheetMul A a x)
      (sheetHaar A v₀ μG x) (sheetHaar A v₀ μG (q A a * x)) := by
  let e := sheetTranslation A v₀ x
  let e' := sheetTranslation A v₀ (q A a * x)
  let c : A.G1 := ⟨(normSection A v₀ (q A a * x))⁻¹ *
      A.diagonal a * normSection A v₀ x, by
    change A.norm _ = 1
    rw [norm_mul', norm_mul', norm_inv', norm_normSection, norm_normSection]
    change (A.norm (A.diagonal a) * x.val)⁻¹ * A.norm (A.diagonal a) * x.val = 1
    field_simp [ne_of_gt (norm_positive A (A.diagonal a)), ne_of_gt x.property]⟩
  have he : (sheetMul A a x) ∘ e = e' ∘ (fun z : A.G1 => c * z) := by
    funext z
    apply Subtype.ext
    change A.diagonal a * (normSection A v₀ x * z.val) =
      normSection A v₀ (q A a * x) * (c.val * z.val)
    dsimp [c]
    simp [mul_assoc]
  refine ⟨(sheetMul A a x).measurable, ?_⟩
  change Measure.map (sheetMul A a x) (Measure.map e (kernelHaar A v₀ μG)) =
    Measure.map e' (kernelHaar A v₀ μG)
  rw [Measure.map_map (sheetMul A a x).measurable e.measurable, he,
    ← Measure.map_map e'.measurable (continuous_const_mul c).measurable,
    (measurePreserving_mul_left (kernelHaar A v₀ μG) c).map_eq]

theorem sheetDiv_measurePreserving (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (μG : Measure A.G) [μG.IsHaarMeasure]
    (a : Fˣ) (x : PositiveAxis) :
    MeasurePreserving (sheetDiv A a x)
      (sheetHaar A v₀ μG x) (sheetHaar A v₀ μG (q A a / x)) := by
  let e := sheetTranslation A v₀ x
  let e' := sheetTranslation A v₀ (q A a / x)
  let c : A.G1 := ⟨(normSection A v₀ (q A a / x))⁻¹ *
      (A.diagonal a / normSection A v₀ x), by
    change A.norm _ = 1
    rw [norm_mul', norm_inv', norm_normSection, norm_div', norm_normSection]
    change (A.norm (A.diagonal a) / x.val)⁻¹ * (A.norm (A.diagonal a) / x.val) = 1
    exact inv_mul_cancel₀ (div_ne_zero (ne_of_gt (norm_positive A (A.diagonal a)))
      (ne_of_gt x.property))⟩
  have he : (sheetDiv A a x) ∘ e = e' ∘ (fun z : A.G1 => c / z) := by
    funext z
    apply Subtype.ext
    change A.diagonal a / (normSection A v₀ x * z.val) =
      normSection A v₀ (q A a / x) * (c.val / z.val)
    dsimp [c]
    simp only [div_eq_mul_inv, mul_inv_rev]
    rw [mul_assoc, mul_inv_cancel_left]
    ac_rfl
  refine ⟨(sheetDiv A a x).measurable, ?_⟩
  change Measure.map (sheetDiv A a x) (Measure.map e (kernelHaar A v₀ μG)) =
    Measure.map e' (kernelHaar A v₀ μG)
  have hp := Measure.measurePreserving_div_left (kernelHaar A v₀ μG) c
  rw [Measure.map_map (sheetDiv A a x).measurable e.measurable, he,
    ← Measure.map_map e'.measurable hp.measurable, hp.map_eq]

private theorem integral_sheet_unfold (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : PositiveAxis)
    (Ω : Set (Sheet A x))
    (hΩ : IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x))
    (g : Sheet A x → ℂ) (hg : Integrable g (sheetHaar A v₀ μG x)) :
    Summable (fun γ : A.Gamma1 => ∫ y in Ω, g (γ • y) ∂sheetHaar A v₀ μG x) ∧
    (∑' γ : A.Gamma1, ∫ y in Ω, g (γ • y) ∂sheetHaar A v₀ μG x) =
      ∫ y, g y ∂sheetHaar A v₀ μG x := by
  have hs : Integrable g (Measure.sum (fun γ : A.Gamma1 =>
      (sheetHaar A v₀ μG x).restrict (γ • Ω))) := by
    rw [hΩ.sum_restrict_of_ac (Measure.AbsolutelyContinuous.refl _)]
    exact hg
  constructor
  · have hsum := (hasSum_integral_measure hs).summable
    apply hsum.congr
    intro γ
    exact (measurePreserving_smul γ (sheetHaar A v₀ μG x)).setIntegral_image_emb
      (measurableEmbedding_const_smul γ) g Ω
  · exact (hΩ.integral_eq_tsum'' g hg).symm

theorem integral_mul_unfold (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (a : Fˣ) (x : PositiveAxis)
    (Ω : Set (Sheet A x))
    (hΩ : IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x))
    (f : A.G → ℂ)
    (hf : Integrable (fun v : Sheet A (q A a * x) => f v.val)
      (sheetHaar A v₀ μG (q A a * x))) :
    Summable (fun γ : A.Gamma1 =>
      ∫ y in Ω, f (γ.val.val * A.diagonal a * y.val) ∂sheetHaar A v₀ μG x) ∧
    (∑' γ : A.Gamma1,
      ∫ y in Ω, f (γ.val.val * A.diagonal a * y.val) ∂sheetHaar A v₀ μG x) =
      ∫ v : Sheet A (q A a * x), f v.val ∂sheetHaar A v₀ μG (q A a * x) := by
  let g : Sheet A x → ℂ := fun y => f (sheetMul A a x y).val
  have hp := sheetMul_measurePreserving A v₀ μG a x
  have hg : Integrable g (sheetHaar A v₀ μG x) := by
    exact (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  obtain ⟨hs, he⟩ := integral_sheet_unfold A v₀ μG x Ω hΩ g hg
  have heq (γ : A.Gamma1) (y : Sheet A x) :
      g (γ • y) = f (γ.val.val * A.diagonal a * y.val) := by
    dsimp [g]
    congr 1
    change A.diagonal a * (γ.val.val * y.val) = _
    ac_rfl
  simp_rw [heq] at hs he
  exact ⟨hs, he.trans (hp.integral_comp (sheetMul A a x).measurableEmbedding (fun v => f v.val))⟩

theorem integral_div_unfold (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (a : Fˣ) (x : PositiveAxis)
    (Ω : Set (Sheet A x))
    (hΩ : IsFundamentalDomain A.Gamma1 Ω (sheetHaar A v₀ μG x))
    (f : A.G → ℂ)
    (hf : Integrable (fun v : Sheet A (q A a / x) => f v.val)
      (sheetHaar A v₀ μG (q A a / x))) :
    Summable (fun γ : A.Gamma1 =>
      ∫ y in Ω, f (γ.val.val * A.diagonal a / y.val) ∂sheetHaar A v₀ μG x) ∧
    (∑' γ : A.Gamma1,
      ∫ y in Ω, f (γ.val.val * A.diagonal a / y.val) ∂sheetHaar A v₀ μG x) =
      ∫ v : Sheet A (q A a / x), f v.val ∂sheetHaar A v₀ μG (q A a / x) := by
  let g : Sheet A x → ℂ := fun y => f (sheetDiv A a x y).val
  have hp := sheetDiv_measurePreserving A v₀ μG a x
  have hg : Integrable g (sheetHaar A v₀ μG x) := by
    exact (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  obtain ⟨hs, he⟩ := integral_sheet_unfold A v₀ μG x Ω hΩ g hg
  have heq (γ : A.Gamma1) (y : Sheet A x) :
      g (γ⁻¹ • y) = f (γ.val.val * A.diagonal a / y.val) := by
    dsimp [g]
    congr 1
    change A.diagonal a / (γ.val.val⁻¹ * y.val) = _
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl
  have hs' := hs.comp_injective (Equiv.inv A.Gamma1).injective
  have he' := ((Equiv.inv A.Gamma1).tsum_eq
    (fun γ => ∫ y in Ω, g (γ • y) ∂sheetHaar A v₀ μG x)).trans he
  simp only [Function.comp_def, Equiv.inv_apply] at hs'
  simp only [Equiv.inv_apply] at he'
  simp_rw [heq] at hs' he'
  exact ⟨hs', he'.trans (hp.integral_comp (sheetDiv A a x).measurableEmbedding (fun v => f v.val))⟩

end
end DedekindZetaZeroFree.ThetaSheetExactUnfolding
