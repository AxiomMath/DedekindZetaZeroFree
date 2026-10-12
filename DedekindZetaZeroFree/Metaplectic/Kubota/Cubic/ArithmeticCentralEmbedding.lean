module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData
public import DedekindZetaZeroFree.Metaplectic.Kubota.PGLCentralTransitions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem canonicalProjection_eq (P : Polarization S.heisenberg) :
    S.borel.projection = KPLocalSmoothRepresentation.projection F ζ hζ q := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | _ g => exact (S.openCell P).projection_eq g

theorem canonicalKernel_eq (P : Polarization S.heisenberg) :
    S.borel.projection.ker =
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
  rw [canonicalProjection_eq F ζ hζ q S P]
  rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
  ext g
  change KPLocalSmoothRepresentation.ordinaryPGLMap F q
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g) = 1 ↔
      KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g = 1
  exact (map_eq_one_iff _
    (KPWildCompactProjectorKirillov.ClopenGluing.ordinaryPGLMap_injective F q))

theorem canonicalKernel_le_center (P : Polarization S.heisenberg) :
    S.borel.projection.ker ≤ Subgroup.center (ActualCover F ζ hζ q) := by
  rw [canonicalKernel_eq F ζ hζ q S P]
  exact KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q)

theorem canonicalKernel_finite (P : Polarization S.heisenberg) :
    Finite S.borel.projection.ker := by
  classical
  let f : rootsOfUnity 3 F → S.borel.projection.ker := fun e =>
    ⟨KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e, by
      rw [canonicalKernel_eq F ζ hζ q S P]
      exact ⟨e, rfl⟩⟩
  apply Finite.of_surjective f
  intro g
  have hg : g.val ∈ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range := by
    rw [← canonicalKernel_eq F ζ hζ q S P]
    exact g.property
  obtain ⟨e, he⟩ := hg
  exact ⟨e, Subtype.ext he⟩

end DedekindZetaZeroFree.KPRankOneShellRepair

end
