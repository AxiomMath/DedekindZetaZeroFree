module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailBruhatIdentity

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

def actualRootAction (P : Polarization S.heisenberg) (ε : Sign) (s : ℂ)
    (v : (LocalField F q)ˣ) : InducedModule P →ₗ[ℂ] InducedModule P :=
  inducingAction S.borel P (sourceSign ε) (sourceParameter ε s)
    (S.borel.torus ((S.openCell P).rootTorus v))

theorem actual_tail_inducing (P : Polarization S.heisenberg) (ε : Sign) (s : ℂ)
    (f : sectionSpace S.borel P (sourceSign ε) (sourceParameter ε s))
    (v : (LocalField F q)ˣ) (g : ActualCover F ζ hζ q) :
    f.val (kernelW (LocalField F q) S.borel ε *
      (S.borel.upperRoot (Multiplicative.ofAdd (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) :
        ActualCover F ζ hζ q) * g) =
    (ordinaryIota F ζ hζ (actualTailPhase F ζ hζ q v) : ℂ) •
      actualRootAction F ζ hζ q S P ε s v
        (f.val (actualLowerRoot F ζ hζ q (v : LocalField F q) * g)) := by
  rw [actual_tail_bruhat F ζ hζ q S P ε v]
  rw [← (S.openCell P).central_eq, ← (S.openCell P).torus_eq,
    ← (S.openCell P).upper_eq]
  simp only [mul_assoc]
  rw [f.property.1, f.property.1, f.property.1, upperRoot_trivial]
  have hc : inducingAction S.borel P (sourceSign ε) (sourceParameter ε s)
      (S.borel.torus ((S.openCell P).centralTorus (actualTailPhase F ζ hζ q v))) =
      (ordinaryIota F ζ hζ (actualTailPhase F ζ hζ q v) : ℂ) • LinearMap.id := by
    apply LinearMap.ext
    intro V
    have he := (S.openCell P).genuine (sourceSign ε) (actualTailPhase F ζ hζ q v) V
    rw [S.openCell_ordinary P] at he
    simpa [inducingAction, inducingScalar, deltaHalf, S.borel.retract_torus,
      (S.openCell P).central_coordinate, normPower, localAbs_one] using he
  rw [hc]
  rfl

theorem actualRootAction_cube (P : Polarization S.heisenberg) (ε : Sign) (s : ℂ)
    (u : (LocalField F q)ˣ) (V : InducedModule P) :
    actualRootAction F ζ hζ q S P ε s (u ^ 3) V =
      (deltaHalf S.borel (rootCubeLift S.borel u) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) u) • V := by
  have ht : S.borel.torus ((S.openCell P).rootTorus (u ^ 3)) = rootCubeLift S.borel u := by
    apply Subtype.ext
    rw [(S.openCell P).torus_eq]
    change KPRankOneOpenCellKernel.hLift F ζ hζ q (u ^ 3) =
      (S.borel.torus (S.borel.cubeLift (u ^ 2)) : ActualCover F ζ hζ q)
    rw [S.torus_full, S.cube_actual]
    simp only [KPRankOneOpenCellKernel.hLift, ← pow_mul]
  unfold actualRootAction
  rw [ht]
  exact rootCharacter_inducingAction S.borel P _ _ u V

end DedekindZetaZeroFree.KPRankOneShellRepair

end
