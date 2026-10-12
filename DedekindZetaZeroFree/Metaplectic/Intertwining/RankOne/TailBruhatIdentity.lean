module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Cubic.ArithmeticCentralEmbedding

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOpenCellKernel
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

def actualLowerRoot (v : KPLocalExceptionalConstruction.LocalField F q) : ActualCover F ζ hζ q :=
  (signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q v * signedWeyl F ζ hζ q

def actualTailPhase (v : (KPLocalExceptionalConstruction.LocalField F q)ˣ) : rootsOfUnity 3 F := kappa F ζ hζ q v 0

theorem actualSignedWeyl_inv :
    (signedWeyl F ζ hζ q)⁻¹ = signedWeyl F ζ hζ q := by
  have h : signedWeyl F ζ hζ q ^ 2 = 1 := by
    simpa only [signedWeyl, signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW] using
      KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

theorem actualKernelW_eq (P : Polarization S.heisenberg) (ε : Sign) :
    kernelW (KPLocalExceptionalConstruction.LocalField F q) S.borel ε = (signedWeyl F ζ hζ q)⁻¹ := by
  cases ε <;> simp [kernelW, (S.openCell P).weyl_eq, actualSignedWeyl_inv]

theorem actualLowerRoot_eq (P : Polarization S.heisenberg) (v : KPLocalExceptionalConstruction.LocalField F q) :
    actualLowerRoot F ζ hζ q v = lowerRootCoordinate (KPLocalExceptionalConstruction.LocalField F q) S.borel v := by
  simp [actualLowerRoot, lowerRootCoordinate, (S.openCell P).weyl_eq, (S.openCell P).upper_eq]

theorem actual_tail_bruhat (P : Polarization S.heisenberg) (ε : Sign)
    (v : (KPLocalExceptionalConstruction.LocalField F q)ˣ) :
    kernelW (KPLocalExceptionalConstruction.LocalField F q) S.borel ε *
      (S.borel.upperRoot (Multiplicative.ofAdd (-((v⁻¹ : (KPLocalExceptionalConstruction.LocalField F q)ˣ) : KPLocalExceptionalConstruction.LocalField F q))) :
        ActualCover F ζ hζ q) =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (actualTailPhase F ζ hζ q v) *
      hLift F ζ hζ q v * nLift F ζ hζ q ((v⁻¹ : (KPLocalExceptionalConstruction.LocalField F q)ˣ) : KPLocalExceptionalConstruction.LocalField F q) *
      actualLowerRoot F ζ hζ q (v : KPLocalExceptionalConstruction.LocalField F q) := by
  rw [actualKernelW_eq F ζ hζ q S P ε, (S.openCell P).upper_eq]
  have hb := lifted_bruhat_identity F ζ hζ q v 0
  have h := congrArg (fun a => a * signedWeyl F ζ hζ q) hb
  have hn : nLift F ζ hζ q 0 = 1 := by
    rw [← (S.openCell P).upper_eq]
    exact congrArg Subtype.val S.borel.upperRoot.map_one
  rw [hn, mul_one, inv_mul_cancel_right] at h
  simpa [actualTailPhase, actualLowerRoot, mul_assoc] using h

end DedekindZetaZeroFree.KPRankOneShellRepair

end
