module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData

@[expose] public section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw KPActualScalarBinding
noncomputable section
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q)
local notation "H₀" => KPExceptionalRaw.actualTorus F ζ hζ q

private theorem weyl_sheet (e : rootsOfUnity 3 F) :
    S.borel.weylCenter (S.central e) = S.central e := by
  apply Subtype.ext
  apply Subtype.ext
  rw [S.borel.weylCenter_coe, ← S.torus_full, S.borel.weyl_from_lift,
    S.torus_full, S.central_actual]
  have hc := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e,rfl⟩)
    S.borel.liftedW
  rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem center_sheet (ε : Sign) (e : rootsOfUnity 3 F)
    (V : CenterModule S.heisenberg) :
    centerTorus F ζ hζ q S.heisenberg S.borel ε (S.central e) V =
      (KPExceptionalRaw.ordinaryIota F ζ hζ e : ℂ) • V := by
  apply Subtype.ext
  funext h
  have hc : (h * (S.central e : H₀)) = (S.central e : H₀) * h := by
    exact Subgroup.mem_center_iff.mp (S.heisenberg.central (S.central e).property) h
  cases ε
  · change V.val (h * (S.central e : H₀)) = _
    rw [hc, V.property]
    change (S.heisenberg.ω (S.central e) : ℂ) * V.val h = _
    rw [S.central_character]
    rfl
  · change V.val (h * S.borel.weyl (S.central e)) = _
    rw [← S.borel.weylCenter_coe, weyl_sheet, hc, V.property]
    change (S.heisenberg.ω (S.central e) : ℂ) * V.val h = _
    rw [S.central_character]
    rfl

variable (P : Polarization S.heisenberg)
private theorem centralTorus_eq (e : rootsOfUnity 3 F) :
    (S.openCell P).centralTorus e = (S.central e : H₀) := by
  apply Subtype.ext
  rw [← S.torus_full, (S.openCell P).central_eq, S.central_actual]

private theorem center_genuine (ε : Sign) (e : rootsOfUnity 3 F)
    (V : CenterModule S.heisenberg) :
    centerTorus F ζ hζ q S.heisenberg S.borel ε ((S.openCell P).centralTorus e) V =
      ((S.openCell P).eta e : ℂ) • V := by
  rw [centralTorus_eq, S.openCell_ordinary]
  exact center_sheet F ζ hζ q S ε e V

private theorem modulus_sq (v : (LocalField F q)ˣ) :
    normPower (LocalField F q) (v ^ 2) (1 / 2) =
      (localAbs (LocalField F q) v : ℂ) := by
  rw [normPower, show localAbs (LocalField F q) (v ^ 2) =
    localAbs (LocalField F q) v ^ 2 by simp [pow_two, localAbs_mul], Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [show (1 / 2 : ℂ) * ((2 : ℝ) * Real.log (localAbs (LocalField F q) v) : ℝ) =
    (Real.log (localAbs (LocalField F q) v) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp, Real.exp_log (localAbs_pos _ _)]

private theorem weyl_inv : (signedWeyl F ζ hζ q)⁻¹ = signedWeyl F ζ hζ q := by
  have hs : signedWeyl F ζ hζ q ^ 2 = 1 := by
    simpa only [signedWeyl, signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW]
      using KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)

theorem actual_reverse_chart (r : ℂˣ)
    (f : centerSectionSpace F ζ hζ q S.heisenberg S.borel .minus (-additiveParameter F q r))
    (v : (LocalField F q)ˣ) :
    f.val (signedWeyl F ζ hζ q * nLift F ζ hζ q (-(v⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
      openCoordinate F ζ hζ q 0) =
    (localAbs (LocalField F q) v : ℂ) •
      ((KPExceptionalRaw.ordinaryIota F ζ hζ (kappa F ζ hζ q v 0) : ℂ) •
        reverseRoot F ζ hζ q S.heisenberg S.borel P (S.openCell P) r v
          (f.val (openCoordinate F ζ hζ q (v : LocalField F q)))) := by
  rw [← S.openCell_ordinary P]
  rw [← weyl_inv F ζ hζ q]
  change f.val ((signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q _ *
    ((signedWeyl F ζ hζ q)⁻¹ * nLift F ζ hζ q 0)) = _
  rw [← mul_assoc, lifted_bruhat_identity]
  rw [← (S.openCell P).central_eq, ← (S.openCell P).torus_eq, ← (S.openCell P).upper_eq]
  simp only [mul_assoc]
  rw [f.property.1, f.property.1, f.property.1]
  have hu (x : LocalField F q) (V : CenterModule S.heisenberg) :
      centerInducingAction F ζ hζ q S.heisenberg S.borel .minus (-additiveParameter F q r)
        (S.borel.upperRoot (Multiplicative.ofAdd x)) V = V := by
    simp [centerInducingAction, inducingScalar, deltaHalf, S.borel.retract_upperRoot,
      normPower, localAbs_one]
  rw [hu]
  change inducingScalar S.borel (-additiveParameter F q r) (S.borel.torus ((S.openCell P).centralTorus _)) •
    centerTorus F ζ hζ q S.heisenberg S.borel .minus (S.borel.retract (S.borel.torus ((S.openCell P).centralTorus _)))
      (inducingScalar S.borel (-additiveParameter F q r) (S.borel.torus ((S.openCell P).rootTorus v)) •
        centerTorus F ζ hζ q S.heisenberg S.borel .minus (S.borel.retract (S.borel.torus ((S.openCell P).rootTorus v)))
          (f.val (openCoordinate F ζ hζ q (0 + (v : LocalField F q))))) = _
  simp only [S.borel.retract_torus, zero_add]
  rw [center_genuine F ζ hζ q S P]
  simp only [inducingScalar, deltaHalf, S.borel.retract_torus, (S.openCell P).central_coordinate,
    (S.openCell P).coordinate_eq, normPower, localAbs_one, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul, one_smul]
  change ((S.openCell P).eta (kappa F ζ hζ q v 0) : ℂ) •
    ((normPower (LocalField F q) (v ^ 2) (1 / 2) *
      normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r)) • _) = _
  rw [modulus_sq]
  simp only [reverseRoot, smul_smul]
  rw [mul_left_comm]
  simp only [LinearMap.smul_apply, smul_smul, mul_assoc]

end
end DedekindZetaZeroFree.KPActualResidueSources
