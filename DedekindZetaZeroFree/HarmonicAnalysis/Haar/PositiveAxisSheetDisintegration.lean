module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArchimedeanNormFiberCoordinates
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ProductMeasureFiberIntegration

@[expose] public section

open MeasureTheory NumberField
open scoped ENNReal

namespace DedekindZetaZeroFree
namespace ThetaProfileHaarSheets

noncomputable section
set_option autoImplicit false

abbrev PositiveAxis := {x : ℝ // 0 < x}

def positiveHaar : Measure PositiveAxis :=
  Measure.comap Subtype.val
    (volume.withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹))

theorem positiveHaar_map_val :
    Measure.map Subtype.val positiveHaar =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal x⁻¹)).restrict (Set.Ioi 0) := by
  exact NormSheetsPositiveAxis.density_and_haar.1

instance positiveHaar_isHaarMeasure : positiveHaar.IsHaarMeasure := by
  exact NormSheetsPositiveAxis.density_and_haar.2

variable {F : Type} [Field F] [NumberField F]

instance groupMeasurableSpace (A : SArithmeticData F) : MeasurableSpace A.G :=
  borel A.G

instance groupBorelSpace (A : SArithmeticData F) : BorelSpace A.G := ⟨rfl⟩

def sqrtUnit (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : PositiveAxis) : v₀.Completionˣ :=
  Units.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (A.complex_place v₀)).symm.toMonoidHom
    (Units.mk0 (Real.sqrt (x : ℝ) : ℂ) (by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 x.property))))

def normSection (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : PositiveAxis) : A.G := by
  classical
  exact (Pi.mulSingle v₀ (sqrtUnit A v₀ x), 1)

theorem normSection_at_other_place (A : SArithmeticData F)
    (v₀ v : InfinitePlace F) (hv : v ≠ v₀) (x : PositiveAxis) :
    (normSection A v₀ x).1 v = 1 := by
  exact NormSheetsCoordinates.section_at_other_place A v₀ v hv x

theorem normSection_at_finite_place (A : SArithmeticData F)
    (v₀ : InfinitePlace F) (x : PositiveAxis) (v : A.Sf) :
    (normSection A v₀ x).2 v = 1 := rfl

theorem norm_normSection (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : PositiveAxis) : A.norm (normSection A v₀ x) = (x : ℝ) := by
  exact (NormSheetsCoordinates.section_laws A v₀).1 x

theorem norm_positive (A : SArithmeticData F) (y : A.G) : 0 < A.norm y := by
  exact NormSheetsCoordinates.norm_positive A y

def normSplit (A : SArithmeticData F) (v₀ : InfinitePlace F) :
    (PositiveAxis × A.G1) ≃ₜ* A.G where
  toFun p := normSection A v₀ p.1 * p.2.val
  invFun y :=
    (⟨A.norm y, norm_positive A y⟩,
      ⟨(normSection A v₀ ⟨A.norm y, norm_positive A y⟩)⁻¹ * y, by
          exact NormSheetsCoordinates.inverse_section_mem A v₀ _ y rfl⟩)
  left_inv := (NormSheetsCoordinates.split A v₀).left_inv
  right_inv := (NormSheetsCoordinates.split A v₀).right_inv
  map_mul' := (NormSheetsCoordinates.split A v₀).map_mul'
  continuous_toFun := (NormSheetsCoordinates.split A v₀).continuous_toFun
  continuous_invFun := (NormSheetsCoordinates.split A v₀).continuous_invFun

theorem exists_unique_kernelHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] :
    ∃! ν : Measure A.G1, ν.IsHaarMeasure ∧
      Measure.map (normSplit A v₀) (positiveHaar.prod ν) = μG := by
  letI : LocallyCompactSpace A.G1 := (NormSheetsCoordinates.normOne_geometry A).1
  letI : SecondCountableTopology A.G1 := (NormSheetsCoordinates.normOne_geometry A).2
  exact NormSheetsProductHaar.exists_unique_product_haar (normSplit A v₀) positiveHaar μG

def kernelHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] : Measure A.G1 :=
  Classical.choose (exists_unique_kernelHaar A v₀ μG)

instance kernelHaar_isHaarMeasure (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] :
    (kernelHaar A v₀ μG).IsHaarMeasure := by
  exact (Classical.choose_spec (exists_unique_kernelHaar A v₀ μG)).1.1

theorem map_product_kernelHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] :
    Measure.map (normSplit A v₀) (positiveHaar.prod (kernelHaar A v₀ μG)) = μG := by
  exact (Classical.choose_spec (exists_unique_kernelHaar A v₀ μG)).1.2

abbrev Sheet (A : SArithmeticData F) (x : PositiveAxis) :=
  {y : A.G // A.norm y = (x : ℝ)}

def sheetTranslation (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : PositiveAxis) : A.G1 ≃ₜ Sheet A x where
  toFun z := ⟨normSection A v₀ x * z.val, by
    change A.norm (NormSheetsCoordinates.normSectionRaw A v₀ x * z.val) = (x : ℝ)
    rw [NormSheetsCoordinates.norm_mul, (NormSheetsCoordinates.section_laws A v₀).1,
      z.property, mul_one]⟩
  invFun y := ⟨(normSection A v₀ x)⁻¹ * y.val, by
    exact NormSheetsCoordinates.inverse_section_mem A v₀ x y.val y.property⟩
  left_inv := (NormSheetsCoordinates.translation A v₀ x).left_inv
  right_inv := (NormSheetsCoordinates.translation A v₀ x).right_inv
  continuous_toFun := (NormSheetsCoordinates.translation A v₀ x).continuous_toFun
  continuous_invFun := (NormSheetsCoordinates.translation A v₀ x).continuous_invFun

def sheetHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (x : PositiveAxis) : Measure (Sheet A x) :=
  Measure.map (sheetTranslation A v₀ x) (kernelHaar A v₀ μG)

theorem integral_disintegration (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (g : A.G → ℂ) (hg : Integrable g μG) :
    (∀ᵐ x ∂positiveHaar, Integrable (fun y : Sheet A x => g y.val)
      (sheetHaar A v₀ μG x)) ∧
    Integrable (fun x : PositiveAxis =>
      ∫ y : Sheet A x, g y.val ∂sheetHaar A v₀ μG x) positiveHaar ∧
    (∫ y, g y ∂μG) =
      ∫ x : PositiveAxis, (∫ y : Sheet A x, g y.val ∂sheetHaar A v₀ μG x)
        ∂positiveHaar := by
  letI : LocallyCompactSpace A.G1 := (NormSheetsCoordinates.normOne_geometry A).1
  letI : SecondCountableTopology A.G1 := (NormSheetsCoordinates.normOne_geometry A).2
  exact NormSheetsProductHaar.integral_fibers (Sheet A)
    (normSplit A v₀).toHomeomorph.toMeasurableEquiv
    (fun x => (sheetTranslation A v₀ x).toMeasurableEquiv)
    (fun _ y => y.val) (fun _ _ => rfl)
    positiveHaar (kernelHaar A v₀ μG) μG (map_product_kernelHaar A v₀ μG) g hg

end
end ThetaProfileHaarSheets
end DedekindZetaZeroFree
