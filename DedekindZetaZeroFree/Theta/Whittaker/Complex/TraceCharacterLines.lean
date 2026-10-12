module

public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.Theta.Whittaker.Uniqueness.ComplexTorusTranslates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField ENNReal
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxActualImage KPCplxCharacterHaar
open KPCplxWhittakerUnique
open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming coreInImage → KPWildComplexWhittakerDictionary.coreInImage
open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming coreRestriction → KPWildComplexWhittakerDictionary.coreRestriction
open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming coreRestriction_injective → KPWildComplexWhittakerDictionary.coreRestriction_injective
open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming restrictedWhittakerSpace → KPWildComplexWhittakerDictionary.restrictedWhittakerSpace
open _root_.DedekindZetaZeroFree.KPWildComplexWhittakerDictionary renaming restrictedWhittakerSpace_eq_span → KPWildComplexWhittakerDictionary.restrictedWhittakerSpace_eq_span

def traceFrequency : ℂˣ := Units.mk0 ((4 * Real.pi : ℝ) : ℂ)
  (Complex.ofReal_ne_zero.mpr (by positivity))

theorem traceFrequency_haar : characterHaar traceFrequency =
    (2 : ℝ≥0∞) • euclideanArea := by
  have hs : characterScale traceFrequency = 4 * Real.pi := by
    simp only [characterScale, traceFrequency, Units.val_mk0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4 * Real.pi)]
  rw [characterHaar, hs]
  have hd : 4 * Real.pi / (2 * Real.pi) = (2 : ℝ) := by
    field_simp
    <;> ring
  rw [hd]
  norm_num

def traceCharacter : AddChar ℂ Circle := character (traceFrequency : ℂ)

theorem traceCharacter_continuous : Continuous traceCharacter := by
  change Continuous (fun z : ℂ => Circle.exp (((traceFrequency : ℂ) * z).re))
  fun_prop

theorem traceCharacter_ne_one : traceCharacter ≠ 1 := by
  intro he
  have hx := DFunLike.congr_fun he ((Real.pi : ℂ) / (traceFrequency : ℂ))
  have harg : ((traceFrequency : ℂ) * ((Real.pi : ℂ) / (traceFrequency : ℂ))).re = Real.pi := by
    rw [mul_div_cancel₀ _ traceFrequency.ne_zero]
    rfl
  change Circle.exp (((traceFrequency : ℂ) * ((Real.pi : ℂ) / (traceFrequency : ℂ))).re) = 1 at hx
  rw [harg] at hx
  exact Circle.exp_pi_ne_one hx

abbrev harmonicInclusion : complexCore →ₗ[ℂ] Theta traceFrequency :=
  KPWildComplexWhittakerDictionary.coreInImage traceFrequency

abbrev restriction : (Theta traceFrequency →L[ℂ] ℂ) →ₗ[ℂ] (complexCore →ₗ[ℂ] ℂ) :=
  KPWildComplexWhittakerDictionary.coreRestriction traceFrequency

theorem restriction_injective : Function.Injective restriction :=
  KPWildComplexWhittakerDictionary.coreRestriction_injective traceFrequency

def traceLine : Submodule ℂ (complexCore →ₗ[ℂ] ℂ) :=
  KPWildComplexWhittakerDictionary.restrictedWhittakerSpace traceFrequency traceCharacter

theorem traceLine_rank : Module.rank ℂ traceLine = 1 := by
  obtain ⟨L, hL, hmem, hspan⟩ :=
    KPWildComplexWhittakerDictionary.restrictedWhittakerSpace_eq_span traceFrequency
      traceCharacter traceCharacter_continuous traceCharacter_ne_one
  have hn : restriction L ≠ 0 := by
    intro he
    apply hL
    apply restriction_injective
    simpa only [map_zero] using he
  rw [traceLine, hspan]
  exact Module.rank_eq_one_iff_finrank_eq_one.mpr (finrank_span_singleton hn)

theorem mem_traceLine_of_extension (l : complexCore →ₗ[ℂ] ℂ)
    (L : Theta traceFrequency →L[ℂ] ℂ)
    (hL : L ∈ whittakerSpace traceFrequency traceCharacter)
    (he : ∀ v : complexCore, L (harmonicInclusion v) = l v) : l ∈ traceLine := by
  refine Submodule.mem_map.mpr ⟨L, hL, ?_⟩
  ext v
  exact he v

open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem slice_rank_of_extensions (D : TensorHC R N) (w : NumberField.InfinitePlace F)
    (hext : ∀ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ j : s.val, actualLocal R D.finiteData j) (hw : Sum.inl w ∈ s.val),
      ∃ L : Theta traceFrequency →L[ℂ] ℂ,
        L ∈ whittakerSpace traceFrequency traceCharacter ∧
        ∀ v : complexCore, L (harmonicInclusion v) =
          (coreStageMultilinear (actualLocal R D.finiteData) D.references D.bad
            (D.literalPeriod 1) s).toLinearMap x ⟨Sum.inl w, hw⟩ v) :
    Module.rank ℂ (D.sliceLine (Sum.inl w)) ≤ 1 := by
  have hle : D.sliceLine (Sum.inl w) ≤ traceLine := by
    apply Submodule.span_le.mpr
    rintro l ⟨s, x, hw, rfl⟩
    obtain ⟨L, hL, he⟩ := hext s x hw
    exact mem_traceLine_of_extension _ L hL he
  exact (Submodule.rank_mono hle).trans_eq traceLine_rank

def localLinesOfExtensions (D : TensorFiniteLines R N)
    (hext : ∀ (w : NumberField.InfinitePlace F)
      (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ j : s.val, actualLocal R D.finiteData j) (hw : Sum.inl w ∈ s.val),
      ∃ L : Theta traceFrequency →L[ℂ] ℂ,
        L ∈ whittakerSpace traceFrequency traceCharacter ∧
        ∀ v : complexCore, L (harmonicInclusion v) =
          (coreStageMultilinear (actualLocal R D.finiteData) D.references D.bad
            (D.toTensorHC.literalPeriod 1) s).toLinearMap x ⟨Sum.inl w, hw⟩ v) :
    TensorLocalLines R N where
  toTensorFiniteLines := D
  complex_rank := fun w => slice_rank_of_extensions D.toTensorHC w (hext w)

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
