module

public import DedekindZetaZeroFree.Metaplectic.Kubota.BorelAndSignedWeylLifts
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ChamberIntegrals.FiniteVectorFubini

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.LocalSignedChamber
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
set_option backward.isDefEq.respectTransparency false
open _root_.DedekindZetaZeroFree.KPStandardLocalRootLifts renaming B_one_left → B_one_left

theorem signedW_eq_diagonal_unsigned :
    KPStandardLocalRootLifts.signedW F ζ hζ (Sum.inr q) =
      KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) *
        KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) := by
  have he : KubotaRankTwo.d (LocalField F q) (-1) 1 *
      KPStandardLocalRootLifts.weylSwap (LocalField F q) = KubotaRankTwo.w (LocalField F q) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.d, KubotaRankTwo.w,
      KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [KPStandardLocalRootLifts.signedW, KPStandardLocalRootLifts.A,
    KPStandardLocalRootLifts.W, KPLocalCover.sectionMap_mul, he]
  have hs : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (-1) 1)
      (KPStandardLocalRootLifts.weylSwap (LocalField F q)) = 1 := by
    simp only [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau,
      KubotaRankTwo.X, KubotaRankTwo.x, KubotaRankTwo.d,
      KPStandardLocalRootLifts.weylSwap, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
    norm_num [KubotaRankTwo.det, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two,
      B_one_left]
    change KPHilbert.B3 F ζ hζ (Sum.inr q) (-1) (-1) ^ 2 = 1
    rw [KubotaDefectSymbolAlgebra.neg_one_left _ _ _
      (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1
      (fun a b => by
        apply Subtype.ext
        exact (KPHilbert.B3 F ζ hζ (Sum.inr q) a b).property) (-1)]
    simp
  rw [hs, map_one, one_mul]

private theorem localAbs_neg_one : localAbs (LocalField F q) (-1) = 1 := by
  have hm := localAbs_mul (LocalField F q) (-1) (-1)
  have hp := localAbs_pos (LocalField F q) (-1)
  simp only [neg_mul_neg, one_mul, localAbs_one] at hm
  nlinarith

theorem cube_diagonal_trivial (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : Polarization S.heisenberg) (s : ℂ) (v : InducedModule P) :
    inducingAction S.borel P .plus s (S.borel.torus (S.borel.cubeLift (-1))) v = v := by
  change (inducingScalar S.borel s (S.borel.torus (S.borel.cubeLift (-1)))) •
    (borelAction S.borel P .plus (S.borel.torus (S.borel.cubeLift (-1)))) v = v
  have hpow : (-1 : (LocalField F q)ˣ)^3 = -1 := by norm_num
  have hn : ∀ s : ℂ, normPower (LocalField F q) ((-1 : (LocalField F q)ˣ)^3) s = 1 := by
    intro s
    rw [hpow]
    simp [normPower, localAbs_neg_one F q]
  simp only [inducingScalar, deltaHalf, S.borel.retract_torus, S.borel.cube_coordinate]
  rw [hn, hn, one_mul, one_smul]
  simp only [borelAction, MonoidHom.comp_apply, S.borel.retract_torus]
  change (tau P) ((S.borel.cubeLift (-1) : S.heisenberg.C) : actualTorus F ζ hζ q) v = v
  rw [tau_hasCentralCharacter S.heisenberg P]
  change (S.heisenberg.ω (S.borel.cubeLift (-1)) : ℂ) • v = v
  rw [S.borel.exceptional_cube, hn, one_smul]

theorem section_unsigned_eq_signed (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : Polarization S.heisenberg) (s : ℂ) (f : sectionSpace S.borel P .plus s)
    (g : ActualCover F ζ hζ q) :
    f.val (KPPGLLocalCover.W F ζ hζ (Sum.inr q) * g) =
      f.val (S.borel.liftedW⁻¹ * g) := by
  have hw : S.borel.liftedW⁻¹ = KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) := by
    rw [KPForwardHomRepair.canonicalSignedWeyl_eq F ζ hζ q S P,
      KPRankOneShellRepair.actualSignedWeyl_inv]
    exact congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
      (KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed F ζ hζ q)
  have hd : (S.borel.torus (S.borel.cubeLift (-1)) : ActualCover F ζ hζ q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1) := by
    rw [S.torus_full, S.cube_actual]
    congr 1
    norm_num
  have hws : KPPGLLocalCover.signedW F ζ hζ (Sum.inr q) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (-1) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) := by
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) _ = _
    rw [signedW_eq_diagonal_unsigned, map_mul]
    rfl
  rw [hw, hws, ← hd, mul_assoc]
  exact (f.property.1 _ _).trans (cube_diagonal_trivial F ζ hζ q S P s _ ) |>.symm
end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.LocalSignedChamber

end
