module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ForwardIntegralOperator

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair.ActualImageAlgebra
universe uG uV uW uU
variable {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (A : ρ.IntertwiningMap σ)

abbrev imageRepresentation := A.range.toRepresentation

abbrev imageModule := A.range.toSubmodule

def quotientMap : ρ.IntertwiningMap (imageRepresentation A) where
  toLinearMap := A.toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun l : V →ₗ[ℂ] W => l v) (A.isIntertwining' g)

theorem quotientMap_surjective : Function.Surjective (quotientMap A) := by
  rintro ⟨w, v, rfl⟩
  exact ⟨v, rfl⟩

def NonzeroIrreducible : Prop :=
  Nontrivial (imageModule A) ∧ (imageRepresentation A).IsIrreducible

end DedekindZetaZeroFree.KPRankOneShellRepair.ActualImageAlgebra

namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

abbrev actualCanonicalImage := (actualCanonicalForwardMap F ζ hζ q S P μ hμ).range

abbrev actualCanonicalImageRepresentation := (actualCanonicalImage F ζ hζ q S P μ hμ).toRepresentation

abbrev actualCanonicalImageModule := (actualCanonicalImage F ζ hζ q S P μ hμ).toSubmodule

instance actualCanonicalImage_addCommGroup :
    AddCommGroup (actualCanonicalImageModule F ζ hζ q S P μ hμ) := by
  letI : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance
  exact Submodule.addCommGroup _

theorem actualCanonicalImage_smooth :
    SmoothRepresentation (actualCanonicalImageRepresentation F ζ hζ q S P μ hμ) := by
  intro v
  obtain ⟨J, hJ⟩ := principalSeries_smooth S.borel P .minus 0 v.val
  exact ⟨J, fun j hj => Subtype.ext (hJ j hj)⟩

theorem actualCanonicalImage_ordinary_genuine
    (e : rootsOfUnity 3 F) (v : actualCanonicalImageModule F ζ hζ q S P μ hμ) :
    actualCanonicalImageRepresentation F ζ hζ q S P μ hμ
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) v =
      (ordinaryIota F ζ hζ e : ℂ) • v := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change v.val.val (x * KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = _
  have hc := KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q)
    (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
  rw [(Subgroup.mem_center_iff.mp hc) x, ← (S.openCell P).central_eq e, v.val.property.1]
  change inducingScalar S.borel 0 (S.borel.torus ((S.openCell P).centralTorus e)) •
    borelAction S.borel P .minus (S.borel.torus ((S.openCell P).centralTorus e))
      (v.val.val x) = _
  have hs : inducingScalar S.borel 0 (S.borel.torus ((S.openCell P).centralTorus e)) = 1 := by
    simp [inducingScalar, deltaHalf, S.borel.retract_torus,
      (S.openCell P).central_coordinate, normPower, localAbs_one]
  rw [hs, one_smul, (S.openCell P).genuine, S.openCell_ordinary]
  rfl

end DedekindZetaZeroFree.KPRankOneShellRepair

end
