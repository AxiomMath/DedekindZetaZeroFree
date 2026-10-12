module

public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

theorem sArchModel_comparison (F : Type*) [Field F] [NumberField F] :
    Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) ∧
      Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ∧
      ∀ x : F,
        NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
            ((algebraMap F (NumberField.InfiniteAdeleRing F)) x) =
          NumberField.mixedEmbedding F x := by
  classical
  let e : NumberField.InfiniteAdeleRing F ≃ₜ NumberField.mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd (fun v : NumberField.InfinitePlace F => v.IsReal)
      (fun v => v.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun v =>
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun v =>
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
            (Equiv.subtypeEquivRight fun _ =>
              NumberField.InfinitePlace.not_isReal_iff_isComplex))))
  refine ⟨?_, ?_, ?_⟩
  · exact e.continuous
  · exact e.symm.continuous
  · intro x
    exact (NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

end DedekindZetaZeroFree

end
