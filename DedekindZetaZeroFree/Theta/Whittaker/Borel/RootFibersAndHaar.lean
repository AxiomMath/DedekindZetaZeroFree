module

public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import DedekindZetaZeroFree.Adeles.Quotients.AdditiveCompactness
public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology
public import DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPWildRawSourceConstruction

def sourceFiber (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) →ₗ[ℂ]
      (KPCompactFourier.AdditiveQuotient F → ℂ) where
  toFun θ x := θ (KPGlobalTorusFunctionData.N F ζ hζ
    (KPCompactFourier.representative F x) * b.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DedekindZetaZeroFree.KPWildRawSourceConstruction

namespace DedekindZetaZeroFree.KPWildKernelSource

def rawBorelRootFiber (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ)
    (x : KPCompactFourier.AdditiveQuotient F) : ℂ :=
  θ (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F x) * b.val)

end DedekindZetaZeroFree.KPWildKernelSource

end
