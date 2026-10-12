module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.FiniteAdelicParabolicExtension

 def mixedChart (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    NumberField.mixedEmbedding.mixedSpace F ≃ₗ[ℝ] KPCuspChart.Horizontal F := by
  letI : IsEmpty {w : NumberField.InfinitePlace F // w.IsReal} :=
    Fintype.card_eq_zero_iff.mp hF
  let e := Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}
  exact
    { toFun := fun x i => x.2 (e.symm i)
      invFun := fun x => (0, fun w => x (e w))
      left_inv := by
        intro x
        apply Prod.ext
        · ext w; exact isEmptyElim w
        · ext w; simp
      right_inv := by intro x; ext i; simp
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }

private theorem mixedChart_embedding (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (x : F) :
    mixedChart F hF (NumberField.mixedEmbedding F x) = KPCuspChart.embedding F x := by
  ext i
  simp [mixedChart, KPCuspChart.embedding, KPCusp.complexPlace]

theorem fractionalIdeal_complexPlace_lattice
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (hJ : J ≠ 0) :
    ∃ hd : DiscreteTopology
      (KPCuspChart.translationLattice F
        (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup).toIntSubmodule,
      letI := hd
      IsZLattice ℝ
        (KPCuspChart.translationLattice F
          (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup).toIntSubmodule := by
  let u : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)ˣ :=
    Units.mk0 J hJ
  let e := (mixedChart F hF).toContinuousLinearEquiv
  have heq : (KPCuspChart.translationLattice F
        (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup).toIntSubmodule =
      ZLattice.comap ℝ (NumberField.mixedEmbedding.idealLattice F u)
        e.symm.toLinearMap := by
    ext x
    change x ∈ (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup.map
        (KPCuspChart.embedding F) ↔
      e.symm x ∈ NumberField.mixedEmbedding.idealLattice F u
    rw [NumberField.mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      apply e.injective
      simpa [e] using mixedChart_embedding F hF y
    · rintro ⟨y, hy, he⟩
      refine ⟨y, hy, ?_⟩
      have hh := congrArg e he
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (mixedChart_embedding F hF y).symm.trans hh
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

end DedekindZetaZeroFree.FiniteAdelicParabolicExtension

end
