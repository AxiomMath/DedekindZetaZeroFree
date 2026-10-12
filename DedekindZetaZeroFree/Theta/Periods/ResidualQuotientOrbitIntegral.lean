module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open KPGlobalResidualConstruction MeasureTheory NumberField
open scoped Topology
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]

def characterCircle (ψ : ContinuousAddChar (KPAdditiveQuotient F)) : C(Y F, Circle) :=
  ⟨fun x => ⟨ψ.toFun x, by simpa [Submonoid.unitSphere] using ψ.unitary x⟩,
    ψ.continuous_toFun.subtype_mk (fun x => by simpa [Submonoid.unitSphere] using ψ.unitary x)⟩

end DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw

end
