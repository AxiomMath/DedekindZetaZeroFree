module

public import DedekindZetaZeroFree.Theta.Digits.SignedExteriorCoefficients

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma packet_branch_rational {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (x : Fˣ) :
    P.branch v (R.A.diagonal x) = Characters.L R v x := by
  rw [P.branch_global]
  have h := (Characters.compatible R).2 (R.probe.unitReps.representative v) x
  rw [R.probe.unitReps.represents] at h
  exact h.symm

lemma correction_pairing_eq (κ τ : R.A.V) :
    R.probe.correction.H κ τ = (R.A.H_S6 κ τ : Fˣ) := by
  induction κ using QuotientGroup.induction_on with
  | H x =>
    induction τ using QuotientGroup.induction_on with
    | H y =>
      exact (R.probe.correction.H_actual x y).trans
        (congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ))
          (R.A.H_S6_on_representatives x y)).symm

lemma rational_gamma_class (γ : ThetaReflectionData.rationalGamma R.A) :
    QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal γ.val) = 1 :=
  ThetaReflectionData.rationalGamma_le_class_ker R.A γ.property

lemma packet_branch_gamma {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (γ : ThetaReflectionData.rationalGamma R.A) :
    P.branch v (R.A.diagonal γ.val) = 1 := by
  rw [P.branch_global]
  have hunit : γ.val ∈ R.A.U := by
    obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
    rw [← he]
    exact R.A.U.pow_mem hu 6
  have hθ := R.probe.correction.theta_unit ⟨γ.val, hunit⟩
  have hH : R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val)
      (R.A.diagonal γ.val) = 1 := by
    rw [← R.A.H_S6_on_representatives, rational_gamma_class, map_one]
  simp only [SArithmeticData.correctionLS, hθ, hH, OneMemClass.coe_one,
    Units.val_one, map_one, Circle.coe_one, mul_one]

lemma packet_branch_ne_zero {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : P.branch v y ≠ 0 := by
  have h : P.branch v y * P.branch v y⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact fun hz => by rw [hz, zero_mul] at h; exact zero_ne_one h

lemma frequencyClass_out (ξ : ThetaReflectionData.Frequency R.A) :
    ThetaReflectionData.rationalClass R.A (Quotient.out ξ) =
      ThetaReflectionData.frequencyClass R.A ξ := by
  simpa only [ThetaReflectionData.frequencyClass_mk] using
    congrArg (ThetaReflectionData.frequencyClass R.A) (Quotient.out_eq ξ)

lemma frequencyNorm_out (ξ : ThetaReflectionData.Frequency R.A) :
    R.A.norm (R.A.diagonal (Quotient.out ξ)) =
      ThetaReflectionData.frequencyNorm R.A ξ := by
  simpa only [ThetaReflectionData.frequencyNorm_mk] using
    congrArg (ThetaReflectionData.frequencyNorm R.A) (Quotient.out_eq ξ)

def reverseSheetWord {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (x : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹ *
    (R.σ ((R.probe.correction.H
      (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal (γ.val * x)))
      (QuotientGroup.mk' R.A.sixthPowers y⁻¹) : Fˣ) : F) ^ 2)⁻¹ *
    fourier R Q.dq (T.theta v)
      (diagonal R (R.A.diagonal (γ.val * x) / y) *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)

theorem reverseSheetWord_eq {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (x : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) :
    reverseSheetWord R T P v x γ y = (Characters.L R v x)⁻¹ *
      T.sheetIntegrand P v (ThetaReflectionData.rationalClass R.A x)
        (R.A.diagonal (γ.val * x) / y) := by
  let k : R.A.G →* R.A.V := QuotientGroup.mk' R.A.sixthPowers
  let a := R.A.diagonal x
  let z := R.A.diagonal (γ.val * x) / y
  have hz : z = R.A.diagonal γ.val * a / y := by
    dsimp [z, a]; rw [map_mul]
  have hkγ : k (R.A.diagonal γ.val) = 1 := rational_gamma_class R γ
  have hkz : k z = k a / k y := by
    rw [hz, map_div, map_mul, hkγ]
    exact congrArg (fun b : R.A.V => b / k y) (one_mul (k a))
  have hka : k (R.A.diagonal (γ.val * x)) = k a := by
    rw [map_mul R.A.diagonal, map_mul k, hkγ]
    exact one_mul (k a)
  have hmask : (if k y ∈ R.probe.correction.B then (1 : ℂ) else 0) =
      (if k a * (k z)⁻¹ ∈ R.probe.correction.B then 1 else 0) := by
    have he : k a * (k z)⁻¹ = k y := by
      rw [hkz, inv_div (k a) (k y)]
      change k a * (k y / k a) = k y
      rw [div_eq_mul_inv, mul_left_comm (k a) (k y), mul_inv_cancel, mul_one]
    rw [he]
  have hpair : R.probe.correction.H (k (R.A.diagonal (γ.val * x))) (k y⁻¹) =
      R.probe.correction.H (k a) (k z) := by
    rw [hka, correction_pairing_eq, correction_pairing_eq, map_inv k, hkz,
      map_div, R.A.H_S6_alternating, one_div, map_inv]
  have hbranch : (P.branch v y)⁻¹ = (P.branch v a)⁻¹ * P.branch v z := by
    rw [hz, map_div, map_mul, packet_branch_gamma, one_mul, div_eq_mul_inv,
      ← mul_assoc, inv_mul_cancel₀ (packet_branch_ne_zero R P v a), one_mul]
  unfold reverseSheetWord Realization.sheetIntegrand
  change (if k y ∈ R.probe.correction.B then (1 : ℂ) else 0) * (P.branch v y)⁻¹ *
    (R.σ ((R.probe.correction.H (k (R.A.diagonal (γ.val * x))) (k y⁻¹) : Fˣ) : F) ^ 2)⁻¹ *
    fourier R Q.dq (T.theta v) (diagonal R z * _) = _
  rw [hmask, hpair, hbranch, show P.branch v a = Characters.L R v x from
    packet_branch_rational R P v x]
  change _ = (Characters.L R v x)⁻¹ *
    ((if k a * (k z)⁻¹ ∈ R.probe.correction.B then 1 else 0) *
      (R.σ ((R.probe.correction.H (k a) (k z) : Fˣ) : F) ^ 2)⁻¹ *
      P.branch v z * fourier R Q.dq (T.theta v) (diagonal R z * _))
  ring

end DedekindZetaZeroFree.OrbitExpansion

end
