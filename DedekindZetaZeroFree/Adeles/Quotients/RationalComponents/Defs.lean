module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.SphericalHaarDisintegrationData
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.HyperbolicPushforward
public import DedekindZetaZeroFree.Adeles.Quotients.ProductHaarSliceTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPActualComponentHaarSources

open KPMsFixedHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Gi (i : Fin A.componentCount) :=
  KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)

def rationalEquiv : KPCuspArithmetic.PGL2 F ≃*
    KPRationalAdelicSplitting.RationalPGL2 F :=
  QuotientGroup.quotientMulEquivOfEq Matrix.GeneralLinearGroup.center_eq_range_scalar

def Ga (i : Fin A.componentCount) :
    Subgroup (KPSmoothActualFlowData.GInfinity F) :=
  (Gi F ζ hζ hF U A i).map
    ((KPSmoothLocalQuotientCharts.archProjection F ζ hζ).comp
      ((KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp
        (rationalEquiv F).toMonoidHom))

def B (i : Fin A.componentCount) :=
  KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U (A.representative i)

def C (i : Fin A.componentCount) :=
  Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))

def m (p : KPSmoothActualFlowData.GInfinity F ×
    KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ p.1 * p.2.val

end DedekindZetaZeroFree.KPActualComponentHaarSources

end
