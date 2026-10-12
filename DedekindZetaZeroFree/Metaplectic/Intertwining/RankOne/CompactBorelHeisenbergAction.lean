module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailBruhatIdentity
public import DedekindZetaZeroFree.Metaplectic.Torus.WeylCoordinateInversion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

include P in

theorem torus_root (t : actualTorus F ζ hζ q) (x : LocalField F q) :
    (S.borel.torus t : ActualCover F ζ hζ q) *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) *
      (S.borel.torus t : ActualCover F ζ hζ q)⁻¹ =
      (S.borel.upperRoot (Multiplicative.ofAdd ((S.borel.coordinate t : LocalField F q) * x)) : ActualCover F ζ hζ q) := by
  letI := canonicalKernel_finite F ζ hζ q S P
  let n : Multiplicative (LocalField F q) →* ActualCover F ζ hζ q :=
    S.borel.B.subtype.comp S.borel.upperRoot
  have ht : S.borel.projection (S.borel.torus t : ActualCover F ζ hζ q) ∈
      KPRankOneInductionRaw.diagonalTorus F q := by
    refine ⟨KubotaRankTwo.d (LocalField F q) (S.borel.coordinate t) 1, ?_, ?_, ?_⟩
    · exact (S.borel.torus_projection t).symm
    · simp
    · simp
  have htB : S.borel.projection (S.borel.torus t : ActualCover F ζ hζ q) ∈
      KPRankOneInductionRaw.upperBorel F q :=
    ⟨KubotaRankTwo.d (LocalField F q) (S.borel.coordinate t) 1, (S.borel.torus_projection t).symm, by simp⟩
  have hr : KPRankOneInductionRaw.borelRatio F q
      ⟨S.borel.projection (S.borel.torus t : ActualCover F ζ hζ q), htB⟩ = S.borel.coordinate t := by
    apply Units.ext
    simpa using KPRankOneInductionRaw.borelRatio_eq F q _
      (KubotaRankTwo.d (LocalField F q) (S.borel.coordinate t) 1)
      (S.borel.torus_projection t).symm (by simp)
  have h := FiniteCentralBorel.torusLift_conjugates_root F q S.borel.projection
    (canonicalKernel_le_center F ζ hζ q S P) n
    (fun y => S.borel.upperRoot_projection y) (S.borel.torus t) ht htB x
  simpa [n, hr] using h

include P in

theorem weyl_involutive (t : actualTorus F ζ hζ q) : S.borel.weyl (S.borel.weyl t) = t := by
  apply S.borel.torus_injective
  apply Subtype.ext
  rw [S.borel.weyl_from_lift, S.borel.weyl_from_lift, (S.openCell P).weyl_eq]
  nth_rw 2 [← actualSignedWeyl_inv F ζ hζ q]
  simp [mul_assoc]
  nth_rw 1 [← actualSignedWeyl_inv F ζ hζ q]
  exact inv_mul_cancel _

include P in

theorem kernel_torus (ε : Sign) (t : actualTorus F ζ hζ q) :
    kernelW (LocalField F q) S.borel ε * (S.borel.torus t : ActualCover F ζ hζ q) =
      (S.borel.torus (S.borel.weyl t) : ActualCover F ζ hζ q) * kernelW (LocalField F q) S.borel ε := by
  rw [S.borel.weyl_from_lift, actualKernelW_eq F ζ hζ q S P ε, (S.openCell P).weyl_eq]
  simp [mul_assoc]

include P in

theorem root_torus (t : actualTorus F ζ hζ q) (x : LocalField F q) :
    (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * S.borel.torus t =
      (S.borel.torus t : ActualCover F ζ hζ q) *
        S.borel.upperRoot (Multiplicative.ofAdd (((S.borel.coordinate t)⁻¹ : (LocalField F q)ˣ) * x)) := by
  have H := torus_root F ζ hζ q S P t⁻¹ x
  have H' := congrArg (fun z => (S.borel.torus t : ActualCover F ζ hζ q) * z) H
  simpa [map_inv, mul_assoc] using H'

include P in

theorem kernel_borel (ε : Sign) (b : S.borel.B) (t : Multiplicative (LocalField F q))
    (ht : b = S.borel.torus (S.borel.retract b) * S.borel.upperRoot t) (x : LocalField F q) :
    kernelW (LocalField F q) S.borel ε *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * b =
    (S.borel.torus (S.borel.weyl (S.borel.retract b)) : ActualCover F ζ hζ q) *
      (kernelW (LocalField F q) S.borel ε *
        S.borel.upperRoot (Multiplicative.ofAdd
          ((((S.borel.coordinate (S.borel.retract b))⁻¹ : (LocalField F q)ˣ) : LocalField F q) * x + Multiplicative.toAdd t))) := by
  have ht' := congrArg Subtype.val ht
  rw [ht']
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, mul_assoc (kernelW (LocalField F q) S.borel ε),
    root_torus F ζ hζ q S P, ← mul_assoc, kernel_torus F ζ hζ q S P]
  simp only [mul_assoc]
  rw [← Subgroup.coe_mul, ← map_mul]
  rfl

theorem source_weyl_action (ε : Sign) (s : ℂ) (b : S.borel.B)
    (hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup)
    (v : InducedModule P) :
    inducingAction S.borel P (sourceSign ε) s
      (S.borel.torus (S.borel.weyl (S.borel.retract b))) v =
      inducingAction S.borel P (targetSign ε) 0 b v := by
  have hn := S.iwasawa.intersection_norm b hb
  have hi : localAbs (LocalField F q)
      ((S.borel.coordinate (S.borel.retract b))⁻¹) = 1 := by
    have HH := localAbs_mul (LocalField F q)
      (S.borel.coordinate (S.borel.retract b)) (S.borel.coordinate (S.borel.retract b))⁻¹
    simpa [hn, localAbs_one] using HH.symm
  cases ε <;>
    simp [inducingAction, inducingScalar, deltaHalf, normPower, S.borel.retract_torus,
      KPRankOneReversePairGeneric.GraphTwist.coordinate_weyl_inverse,
      hn, hi, borelAction, weylConjugate, sourceSign, targetSign,
      weyl_involutive F ζ hζ q S P]
  · rfl
  · change (tau P) (S.borel.weyl (S.borel.weyl (S.borel.retract b))) v = _
    rw [weyl_involutive F ζ hζ q S P]

end DedekindZetaZeroFree.KPRankOneShellRepair.CompactBorel

end
