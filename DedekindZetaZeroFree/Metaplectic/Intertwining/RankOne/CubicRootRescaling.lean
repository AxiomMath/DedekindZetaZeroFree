module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailInducingActionAndCubeClasses

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actualRootAction_cube_rescale (P : Polarization S.heisenberg)
    (ε : Sign) (s : ℂ) (u v : (LocalField F q)ˣ) (V : InducedModule P) :
    actualRootAction F ζ hζ q S P ε s (u ^ 3 * v) V =
      (deltaHalf S.borel (rootCubeLift S.borel u) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) u) •
          actualRootAction F ζ hζ q S P ε s v V := by
  have ht : S.borel.torus ((S.openCell P).rootTorus (u ^ 3 * v)) =
      S.borel.torus ((S.openCell P).rootTorus (u ^ 3)) *
        S.borel.torus ((S.openCell P).rootTorus v) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, (S.openCell P).torus_eq, KPRankOneOpenCellKernel.hLift]
    have hb : KPHilbert.B3 F ζ hζ (Sum.inr q) ((u ^ 3) ^ 2) (v ^ 2) = 1 := by
      rw [← pow_mul, Nat.mul_comm 3 2, pow_mul]
      exact ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 (u ^ 2) (v ^ 2)).1
    rw [KPPGLLocalCover.A_mul, hb, one_pow, map_one, one_mul, mul_pow]
  unfold actualRootAction
  rw [ht, map_mul]
  change actualRootAction F ζ hζ q S P ε s (u ^ 3)
    (actualRootAction F ζ hζ q S P ε s v V) = _
  exact actualRootAction_cube F ζ hζ q S P ε s u _

end DedekindZetaZeroFree.KPRankOneShellRepair

end
