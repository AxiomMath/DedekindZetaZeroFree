module

public import DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPWildActualCompactKernel
open KPLocalExceptionalConstruction
  KPWildPartialPeriodFactorization KPGlobalResidualConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance rawImageAdd (U : Submodule ℂ (KPGlobalTorusFunctionData.G F ζ hζ → ℂ)) :
    AddCommGroup U := Submodule.addCommGroup U

end DedekindZetaZeroFree.KPWildActualCompactKernel

end
