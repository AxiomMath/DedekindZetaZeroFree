module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

noncomputable section
open scoped Classical Matrix
open MeasureTheory
namespace DedekindZetaZeroFree.KPCuspChart

 def mixedChart (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) :
    NumberField.mixedEmbedding.mixedSpace F ≃ₗ[ℝ] Horizontal F := by
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
    mixedChart F hF (NumberField.mixedEmbedding F x) = embedding F x := by
  ext i
  simp [mixedChart, embedding, KPCusp.complexPlace]

theorem arithmetic_extension_lattice
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ D : ExtensionData F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ),
      ∃ hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (translationLattice F D.L).toIntSubmodule := by
  obtain ⟨hupper, J, L, E, ι, ρ, hJ, hL, hindex, hlattice, hE, hEindex,
    hinj, hsurj, hexact, hunipotent, hratio⟩ :=
    kp_cusp_arithmetic_parabolic_stabilizers F M hM Γ hΓ hcomm q σ hσ
  let D : ExtensionData F (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) :=
    { L := L
      E := E
      inclusion := ι
      ratio := ρ
      integralUnits := hE
      unitIndex := hEindex
      injective := hinj
      surjective := hsurj
      exact := hexact
      upper := hupper
      unipotentFormula := hunipotent
      ratioFormula := hratio }
  obtain ⟨hdisc, hz⟩ := hlattice
  letI := hdisc
  letI := hz
  let e := (mixedChart F hF).toContinuousLinearEquiv
  have heq : (translationLattice F L).toIntSubmodule =
      ZLattice.comap ℝ
        (L.map (NumberField.mixedEmbedding F).toAddMonoidHom).toIntSubmodule
        e.symm.toLinearMap := by
    ext x
    change x ∈ L.map (embedding F) ↔
      e.symm x ∈ L.map (NumberField.mixedEmbedding F).toAddMonoidHom
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
  refine ⟨D, ?_⟩
  change ∃ hdisc : DiscreteTopology (translationLattice F L).toIntSubmodule,
    letI := hdisc
    IsZLattice ℝ (translationLattice F L).toIntSubmodule
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

end DedekindZetaZeroFree.KPCuspChart

end
