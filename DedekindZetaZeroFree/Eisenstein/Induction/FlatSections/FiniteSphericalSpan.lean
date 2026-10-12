module

public import DedekindZetaZeroFree.Eisenstein.Residues.SpanAutomorphy
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.ProjectedFlatExpansion
public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SharedSource
open MomentSources
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_add → kfinite_add
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_smul → kfinite_smul
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

def flatScalarStage (Q : AdmissibleFlatSources R) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun v => (Q.flat v).val 0))

end DedekindZetaZeroFree.SharedSource

end
