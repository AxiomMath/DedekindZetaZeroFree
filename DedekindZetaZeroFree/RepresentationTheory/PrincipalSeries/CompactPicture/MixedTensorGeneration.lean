module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.IndependentSlicesAndUniformBands
public import DedekindZetaZeroFree.Algebra.TensorProducts.SeparatingEvaluations
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.TensorSectionSamplingGeneration

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPLiteralScalarMixedTensorGeneration
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices KPLiteralScalarArchUniformBands
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming harmonicBand_finite → harmonicBand_finite
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming finite_interpolation → finite_interpolation

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι]

def familyTranslate (k : ι → ComplexSU2) :
    (Y → multiPrincipalSeries positiveParameter ι) →ₗ[ℂ]
      (Y → multiPrincipalSeries positiveParameter ι) :=
  LinearMap.pi (fun y => (multiTranslate positiveParameter k).comp (LinearMap.proj y))

def familyOrbit (h : Y → multiPrincipalSeries positiveParameter ι) :
    Submodule ℂ (Y → multiPrincipalSeries positiveParameter ι) :=
  Submodule.span ℂ (Set.range (fun k => familyTranslate k h))

open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming multiTranslate_mul → multiTranslate_mul
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchUniformBands renaming harmonicBand_mono → harmonicBand_mono

end DedekindZetaZeroFree.KPLiteralScalarMixedTensorGeneration

end
