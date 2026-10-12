module

public import ClassFieldTheory.All
public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SupportedChartTopology
noncomputable section
variable {F : Type} [Field F] [NumberField F]

theorem continuous_norm (A : SArithmeticData F) : Continuous A.norm := by
  unfold SArithmeticData.norm
  fun_prop

theorem isClosed_G1 (A : SArithmeticData F) : IsClosed (A.G1 : Set A.G) :=
  isClosed_eq (continuous_norm A) continuous_const

theorem locallyCompact_G1 (A : SArithmeticData F) : LocallyCompactSpace A.G1 := by
  have : LocallyCompactSpace A.G := by infer_instance
  exact (isClosed_G1 A).locallyCompactSpace

theorem hausdorff_G1 (A : SArithmeticData F) : T2Space A.G1 := by infer_instance

theorem topologicalGroup_G1 (A : SArithmeticData F) : IsTopologicalGroup A.G1 := by
  infer_instance

theorem compact_exterior (S : Finset (HeightOneSpectrum (𝓞 F))) :
    CompactSpace ((v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) →
      (v.val.adicCompletionIntegers F).units) := by
  letI (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
      CompactSpace (v.val.adicCompletionIntegers F).units :=
    isCompact_iff_compactSpace.mp (isCompact_finiteLocalUnits F v.val)
  infer_instance
end
end DedekindZetaZeroFree.SupportedChartTopology
