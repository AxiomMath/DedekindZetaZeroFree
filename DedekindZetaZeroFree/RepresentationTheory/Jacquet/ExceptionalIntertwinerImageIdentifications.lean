module

public import DedekindZetaZeroFree.Algebra.CompositionLengthBySubmoduleOrder
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompositionLengthOfIrreducibleExtensions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalMinusConservativity
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalMinusBruhatExactSequence
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ReverseIntertwinerRangeEvaluation

@[expose] public section

section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.RankoneSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
noncomputable section
set_option autoImplicit false
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem jacquetMap_injective_of_smooth (A : LocalBorelData (K := K) (G := G) T)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (hσ : SmoothRepresentation σ) :
    Function.Injective (jacquetMap A f) := by
  have hs : KPCoinvariants.IsSmooth (σ.comp (root A)) := by
    apply KPCoinvariants.restrict_smooth σ _ (root A)
    · exact continuous_subtype_val.comp A.upperRoot_continuous
    · intro v
      obtain ⟨J, hJ⟩ := hσ v
      exact Subgroup.isOpen_mono (show J.toSubgroup ≤ σ.stabilizer v from hJ) J.isOpen
  apply KPCoinvariants.TransversalAverages.coinvariants_map_injective_of_annihilating_averages
    (ρ.comp (root A)) (σ.comp (root A)) _ hf
  intro v hv
  have he : KPCoinvariants.twistedRepresentation (σ.comp (root A)) 1 =
      σ.comp (root A) := by ext n w; simp [KPCoinvariants.twistedRepresentation]
  obtain ⟨J, L, R, _, _, _, _, _, _, hR, _, _, hk⟩ :=
    KPCoinvariants.killsRelation (σ.comp (root A)) hs 1 (by fun_prop)
      (IsLocallyConstant.of_constant _ (by intros; simp)) v (by simpa [he] using hv)
  exact ⟨R, hR, by simpa [KPCoinvariants.psiAverage] using hk⟩

theorem jacquetMap_surjective (A : LocalBorelData (K := K) (G := G) T)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Surjective (jacquetMap A f) := by
  intro w
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective (σ.comp (root A)) w
  obtain ⟨u, rfl⟩ := hf v
  exact ⟨Representation.Coinvariants.mk (ρ.comp (root A)) u, rfl⟩

theorem jacquet_image_equiv (A : LocalBorelData (K := K) (G := G) T)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hσ : SmoothRepresentation σ) :
    Nonempty ((jacquetRepresentation A f.range.toRepresentation).Equiv
      (jacquetMap A f).range.toRepresentation) := by
  let q : ρ.IntertwiningMap f.range.toRepresentation :=
    { toLinearMap := f.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        change f (ρ g v) = σ g (f v)
        exact congrArg (fun l : V →ₗ[ℂ] W => l v) (f.isIntertwining' g) }
  let i : f.range.toRepresentation.IntertwiningMap σ :=
    { toLinearMap := f.range.toSubmodule.subtype
      isIntertwining' g := rfl }
  let j := jacquetMap A i
  have hj : Function.Injective j := jacquetMap_injective_of_smooth A i Subtype.val_injective hσ
  have hq : Function.Surjective (jacquetMap A q) := jacquetMap_surjective A q (by
    rintro ⟨v, u, rfl⟩
    exact ⟨u, rfl⟩)
  have hcomp : ∀ v, j ((jacquetMap A q) v) = (jacquetMap A f) v := by
    intro v
    obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective (ρ.comp (root A)) v
    rfl
  let m : (jacquetRepresentation A f.range.toRepresentation).IntertwiningMap
      (jacquetMap A f).range.toRepresentation :=
    { toLinearMap := j.toLinearMap.codRestrict (jacquetMap A f).range.toSubmodule (by
        intro v
        obtain ⟨u, rfl⟩ := hq v
        exact ⟨u, (hcomp u).symm⟩)
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact congrArg (fun l => l v) (j.isIntertwining' g) }
  refine ⟨m.ofBijective ⟨?_, ?_⟩⟩
  · intro v w h
    exact hj (congrArg Subtype.val h)
  · rintro ⟨v, u, rfl⟩
    exact ⟨(jacquetMap A q) u, Subtype.ext (hcomp u)⟩

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.RankoneSteps

end
