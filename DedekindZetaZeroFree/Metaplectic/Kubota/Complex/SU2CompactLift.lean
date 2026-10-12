module

public import DedekindZetaZeroFree.Metaplectic.Kubota.ComplexCharactersHaarAndSU2Splitting
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.L2Operator
namespace DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource
open KPCplxCharacterHaar

theorem complexSU2Embedding_continuous : Continuous complexSU2Embedding := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  exact continuous_subtype_val

end DedekindZetaZeroFree.KPActualReflectionData.StandardLocalSource

end
