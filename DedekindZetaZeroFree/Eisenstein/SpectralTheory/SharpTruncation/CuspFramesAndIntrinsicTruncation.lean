module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.Definitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
open KPMsGreenFlux
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem archProjection_compare (g : Cover F ζ hζ) (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ g)) =
    Matrix.ProjGenLinGroup.map _ (Matrix.ProjGenLinGroup.mk
      (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
        (KPAdelicCoverRestrictedProduct.projection F ζ hζ g)))
  rw [Matrix.ProjGenLinGroup.map_mk, Matrix.GeneralLinearGroup.map_comp]
  rfl

private theorem projective_equiv_injective {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) : Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2) e.toRingHom) := by
  intro x y h
  have h' := congrArg (Matrix.ProjGenLinGroup.map e.symm.toRingHom) h
  simp only [← MonoidHom.comp_apply, ← Matrix.ProjGenLinGroup.map_comp] at h'
  simpa using h'

private theorem complex_kernel_mem {g : Cover F ζ hζ}
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g = 1) :
    g ∈ KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  funext w
  apply projective_equiv_injective
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w))
  rw [← archProjection_compare g w, hg]
  exact (map_one _).symm

 theorem finiteSubgroup_eq :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ = KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  obtain ⟨e, he, hi, hs, hker, hrest⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  rw [← hker]
  ext g
  constructor
  · intro hg
    exact complex_kernel_mem hg
  · intro hg
    rw [MonoidHom.mem_ker]
    funext w
    rw [archProjection_compare g w]
    have h : KPCuspGenuineMonodromy.archProjection F ζ hζ g = 1 := hg
    rw [h]
    exact map_one _

end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
