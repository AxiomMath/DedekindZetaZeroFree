module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.LineBundleLocalization

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.CoreChartLocalizers

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

theorem quotient_hausdorff (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    T2Space (X F ζ hζ U) := by
  letI := KPFiniteAdelicCuspEnds.canonicalAction_continuousConstSMul F
  letI (i : Fin A.componentCount) : ContinuousConstSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.SymmetricSpace F) :=
    ⟨fun γ => continuous_const_smul (γ : KPCuspArithmetic.PGL2 F)⟩
  letI (i : Fin A.componentCount) : ProperlyDiscontinuousSMul
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.SymmetricSpace F) :=
    KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.arithmeticStabilizer_properlyDiscontinuous_of_compact
      F hF _ (KPCuspGenuineMonodromy.finiteBase_level_compact F ζ hζ U) _
  exact A.components.symm.isEmbedding.t2Space

end DedekindZetaZeroFree.CoreChartLocalizers

end
