module

public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability

theorem localField_secondCountable
    (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
    haveI : ProperSpace K :=
      .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    infer_instance

end DedekindZetaZeroFree.KPJointRegulator.MellinBetaIntegrability
