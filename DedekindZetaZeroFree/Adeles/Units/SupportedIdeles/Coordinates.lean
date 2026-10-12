module

public import DedekindZetaZeroFree.Adeles.Units.SupportedIdeles.Topology

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SupportedChartDefinitions

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

def H : Subgroup (IdeleGroup.normOneSubgroup (K := F)) :=
  (IdeleGroup.supportedAt (K := F) (A.Sf : Set (HeightOneSpectrum (𝓞 F)))).subgroupOf
    (IdeleGroup.normOneSubgroup (K := F))

abbrev C :=
  (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ A.Sf}) →
    (v.val.adicCompletionIntegers F).units

def sCoordinatesRaw (a : IdeleGroup F) : A.G :=
  (fun w => ContinuousMulEquiv.piUnits a.1 w,
   fun v => a.2 v.val)

def exteriorCoordinates (a : (SupportedChartDefinitions.H A)) : (SupportedChartDefinitions.C A) :=
  fun v => ⟨a.1.1.2 v.val,
    (IdeleGroup.mem_supportedAt_iff
      (A.Sf : Set (HeightOneSpectrum (𝓞 F))) a.1.1).mp a.2 v.val v.prop⟩

end
end SupportedChartDefinitions
end DedekindZetaZeroFree
