module

public import DedekindZetaZeroFree.Adeles.Units.SupportedIdeles.CoordinateHomeomorphism

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

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

theorem sCoordinatesRaw_norm (a : IdeleGroup F)
    (ha : a ∈ IdeleGroup.supportedAt (K := F)
      (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    A.norm (A.sCoordinatesRaw a) =
      (((IdeleGroup.absoluteNorm a : ℝ≥0) : ℝ))⁻¹ :=
  SupportedChartNorm.supported_norm A a ha

def exteriorCoordinates (a : A.H) : A.C :=
  fun v => ⟨a.1.1.2 v.val,
    (IdeleGroup.mem_supportedAt_iff
      (A.Sf : Set (HeightOneSpectrum (𝓞 F))) a.1.1).mp a.2 v.val v.prop⟩

theorem exists_supportedChart :
    ∃ e : A.H ≃ₜ* (A.G1 × A.C),
      ∀ a : A.H, (e a).1.val = A.sCoordinatesRaw a.1.1 ∧
        (e a).2 = A.exteriorCoordinates a := by
  exact ⟨SupportedChartConstruction.chart A, fun _ => ⟨rfl, rfl⟩⟩

theorem isOpen_H : IsOpen (A.H : Set (IdeleGroup.normOneSubgroup (K := F))) := by
  exact (IdeleGroup.isOpen_supportedAt A.Sf).preimage continuous_subtype_val

instance compactSpace_C : CompactSpace A.C :=
  SupportedChartTopology.compact_exterior A.Sf

instance locallyCompactSpace_G1 : LocallyCompactSpace A.G1 :=
  SupportedChartTopology.locallyCompact_G1 A

instance t2Space_G1 : T2Space A.G1 :=
  SupportedChartTopology.hausdorff_G1 A

instance commGroup_G1 : CommGroup A.G1 := inferInstance

instance isTopologicalGroup_G1 : IsTopologicalGroup A.G1 :=
  SupportedChartTopology.topologicalGroup_G1 A

end
end SArithmeticData
end DedekindZetaZeroFree
