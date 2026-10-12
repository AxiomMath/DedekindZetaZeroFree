module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorValuationSupport
public import DedekindZetaZeroFree.Theta.Unfolding.AbsoluteOrbitSmoothing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical
open _root_.DedekindZetaZeroFree.ThetaBranch renaming ord_mul → ThetaBranch.ord_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming ord_zpow → ThetaBranch.ord_zpow
open _root_.DedekindZetaZeroFree.ThetaBranch renaming unit_ord → ThetaBranch.unit_ord
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_mul → ThetaBranch.reduction_mul
open _root_.DedekindZetaZeroFree.ThetaBranch renaming reduction_pow → ThetaBranch.reduction_pow
open _root_.DedekindZetaZeroFree.ThetaBranch renaming char_order → ThetaBranch.char_order
open _root_.DedekindZetaZeroFree.ThetaBranch renaming char_pow_six → ThetaBranch.char_pow_six
private alias ord_mul := ThetaBranch.ord_mul
private alias ord_zpow := ThetaBranch.ord_zpow
private alias unit_ord := ThetaBranch.unit_ord
private alias reduction_pow := ThetaBranch.reduction_pow
private alias char_order := ThetaBranch.char_order
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def forwardMask (m : ThetaReflectionData.Row R.A) (a : Fˣ) : ℂ :=
  ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
    let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
      (ThetaDigitAverage.rowExponent R.A m.val p.val) (ThetaBranch.unitResidue p.val a)

lemma gamma_integral (γ : ThetaReflectionData.rationalGamma R.A) : γ.val ∈ R.A.U := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  rw [← he]
  exact R.A.U.pow_mem hu 6

lemma gamma_valuation (γ : ThetaReflectionData.rationalGamma R.A)
    (p : ThetaBranch.ExteriorPrime R.A) : p.val.valuation F (γ.val : F) = 1 :=
  gamma_integral R γ p.val p.property

lemma sphericalFactor_gamma (p : ThetaBranch.ExteriorPrime R.A) (a : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) :
    ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (a * γ.val) =
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p a := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  let u' : R.A.U := ⟨u, hu⟩
  change u ^ 6 = γ.val at he
  rw [← he]
  have ho : ThetaBranch.order p.val (a * u ^ 6) = ThetaBranch.order p.val a := by
    rw [ThetaBranch.ord_mul, ← zpow_natCast, ThetaBranch.ord_zpow, unit_ord R.A p u', mul_zero, add_zero]
  have hl : ThetaBranch.localUnit R.A R.probe.allowed p (a * u ^ 6) =
      ThetaBranch.localUnit R.A R.probe.allowed p a * u ^ 6 := by
    simp only [ThetaBranch.localUnit, ho, div_eq_mul_inv]; ac_rfl
  have hr : ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p (a * u ^ 6)) =
      ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p a) *
        ThetaBranch.unitResidue p.val u ^ 6 := by
    rw [hl, ThetaBranch.reduction_mul, reduction_pow p.val u (unit_ord R.A p u')]
    · exact ThetaBranch.localUnit_order R.A R.probe.allowed p a
    · rw [← zpow_natCast, ord_zpow, unit_ord R.A p u', mul_zero]
  have hc : ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p (a * u ^ 6)) =
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p a) := by
    simp only [ThetaBranch.symbol, hr, map_mul, map_pow]
    rw [ThetaBranch.char_pow_six _ (char_order R.A R.σ p) _
      (ThetaBranch.unitResidue_ne_zero _ _ (unit_ord R.A p u')), mul_one]
  simp only [ThetaBranch.sphericalFactor, ho, hc]

lemma forwardExterior_gamma {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (a : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    forwardExterior R C (a * γ.val) = forwardExterior R C a := by
  unfold forwardExterior
  apply finprod_congr
  intro p
  simp_rw [C.exterior.rational_exact]
  exact sphericalFactor_gamma R p a γ

lemma forwardMask_gamma (m : ThetaReflectionData.Row R.A) (a : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) :
    forwardMask R m (a * γ.val) = forwardMask R m a := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  let u' : R.A.U := ⟨u, hu⟩
  change u ^ 6 = γ.val at he
  rw [← he]
  apply Finset.prod_congr rfl
  intro p hp
  let p' : ThetaBranch.ExteriorPrime R.A := ⟨p.val,
    ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩
  change sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ p') _ _ = _
  by_cases ha : ThetaBranch.order p.val a = 0
  · have hu0 : ThetaBranch.order p.val (u ^ 6) = 0 := by
      rw [← zpow_natCast, ord_zpow, unit_ord R.A p' u', mul_zero]
    rw [ThetaBranch.reduction_mul p.val a (u ^ 6) ha hu0,
      reduction_pow p.val u (unit_ord R.A p' u')]
    have hn := ThetaBranch.unitResidue_ne_zero p.val a ha
    have hun := ThetaBranch.unitResidue_ne_zero p.val u (unit_ord R.A p' u')
    simp only [sexticUnitPower, isUnit_iff_ne_zero, hn, hun, pow_ne_zero,
      mul_ne_zero, ↓reduceIte, map_mul, map_pow]
    rw [ThetaBranch.char_pow_six _ (char_order R.A R.σ p') _ hun, mul_one]
    rw [if_pos (mul_ne_zero hn (pow_ne_zero 6 hun)), if_pos hn]
  · have haa : ThetaBranch.order p.val (a * u ^ 6) ≠ 0 := by
      rw [ord_mul, ← zpow_natCast, ord_zpow]
      change ThetaBranch.order p.val a + (6 : ℤ) * ThetaBranch.order p'.val u'.val ≠ 0
      rw [unit_ord R.A p' u', mul_zero, add_zero]
      exact ha
    simp only [ThetaBranch.unitResidue, dif_neg ha, dif_neg haa,
      sexticUnitPower, isUnit_iff_ne_zero, ne_eq, not_true_eq_false, ↓reduceIte]

lemma orbitSheet_forward_factor {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : OrbitIndex R) (l : PositiveAxis) (y : Sheet R.A l)
    (ha : (orbitFrequency R i : F) ∈ R.A.R) :
    orbitSheet R C v m true i l y =
      (forwardMask R m (orbitFrequency R i) * forwardExterior R C (orbitFrequency R i)) *
        forwardSheetWord R C.packet v (Quotient.out i.1) i.2 y.val := by
  have hi (p : KPFinitePlace F) (hp : p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property) :
      p.valuation F (orbitFrequency R i : F) ≤ 1 :=
    ha p ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hp).1
  have hv : orbitFrequencyValue R C.sources C.realization v i (diagonal R y.val) =
      OrbitFrequencies.rationalValue R C.realization v (orbitFrequency R i) (diagonal R y.val) := rfl
  unfold orbitSheet
  rw [forward_digit_mask R C v m i y.val hi, hv, fourier_rational_finprod]
  unfold forwardSheetWord
  rw [R.probe.correction.H_actual]
  change _ = _ * (_ * _ * (R.σ ((R.A.H_S (R.A.diagonal (i.2.val * Quotient.out i.1)) y.val : Fˣ) : F) ^ 2)⁻¹ * _)
  rw [mul_comm i.2.val, ← orbitFrequency]
  unfold forwardMask
  ring

lemma orbitSheet_forward_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : OrbitIndex R) (l : PositiveAxis) (y : Sheet R.A l)
    (ha : (orbitFrequency R i : F) ∉ R.A.R) : orbitSheet R C v m true i l y = 0 := by
  unfold orbitSheet
  rw [forward_digits_nonintegral R C v m i y.val ha, mul_zero]

lemma forwardSheetWord_nonallowed {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (x : Fˣ)
    (hx : ThetaReflectionData.rationalClass R.A x ∉ R.probe.correction.B)
    (γ : ThetaReflectionData.rationalGamma R.A) (y : R.A.G) :
    forwardSheetWord R P v x γ y = 0 := by
  let z := R.A.diagonal (γ.val * x) * y
  by_cases hc : ∀ p : R.A.Sf, z.2 p ∈ P.cutoff p
  · have hz := cutoff_class_one R P z hc
    have hkγ := rational_gamma_class R γ
    have hp : ThetaReflectionData.rationalClass R.A x *
        QuotientGroup.mk' R.A.sixthPowers y = 1 := by
      dsimp only [z] at hz
      rw [map_mul, map_mul R.A.diagonal, map_mul, hkγ] at hz
      change (1 : R.A.V) * ThetaReflectionData.rationalClass R.A x *
        QuotientGroup.mk' R.A.sixthPowers y = 1 at hz
      rwa [@one_mul R.A.V _ (ThetaReflectionData.rationalClass R.A x)] at hz
    have hy : QuotientGroup.mk' R.A.sixthPowers y ∉ R.probe.correction.B := by
      intro h
      apply hx
      have he : ThetaReflectionData.rationalClass R.A x =
          (QuotientGroup.mk' R.A.sixthPowers y)⁻¹ :=
        @eq_inv_of_mul_eq_one_left R.A.V _ _ _ hp
      rw [he]
      exact R.probe.correction.B.inv_mem h
    unfold forwardSheetWord
    rw [if_neg hy]
    simp only [zero_mul]
  · have hf : P.forwardProfile v z = 0 := by
      simp only [Packet.forwardProfile, if_neg hc, zero_mul]
    change _ * P.forwardProfile v z = 0
    rw [hf, mul_zero]

lemma orbitFrequency_integral_iff (ξ : ThetaReflectionData.Frequency R.A)
    (γ : ThetaReflectionData.rationalGamma R.A) :
    (orbitFrequency R (ξ, γ) : F) ∈ R.A.R ↔ (Quotient.out ξ : Fˣ).val ∈ R.A.R := by
  constructor
  · intro h p hp
    have hg := gamma_valuation R γ ⟨p, hp⟩
    have hv := h p hp
    simpa only [orbitFrequency, Units.val_mul, map_mul, hg, mul_one] using hv
  · intro h p hp
    have hg := gamma_valuation R γ ⟨p, hp⟩
    simpa only [orbitFrequency, Units.val_mul, map_mul, hg, mul_one] using h p hp

lemma orbitIntegral_forward_factor {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (γ : ThetaReflectionData.rationalGamma R.A)
    (l : PositiveAxis) (ha : (Quotient.out ξ : Fˣ).val ∈ R.A.R) :
    letI := C.transport.groupHaar_isHaar;
    orbitIntegral R C v m true (ξ, γ) l =
      (forwardMask R m (Quotient.out ξ) * forwardExterior R C (Quotient.out ξ)) *
        (∫ y : Sheet R.A l, forwardSheetWord R C.packet v (Quotient.out ξ) γ y.val
          ∂pregroupingSheetHaar R.A C.packet.v₀ C.transport.groupHaar l) := by
  letI := C.transport.groupHaar_isHaar
  unfold orbitIntegral
  simp_rw [orbitSheet_forward_factor R C v m (ξ, γ) l _
    ((orbitFrequency_integral_iff R ξ γ).mpr ha)]
  simp_rw [orbitFrequency, forwardMask_gamma, forwardExterior_gamma]
  exact integral_const_mul _ _

lemma orbitIntegral_forward_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (γ : ThetaReflectionData.rationalGamma R.A)
    (l : PositiveAxis) (ha : (Quotient.out ξ : Fˣ).val ∉ R.A.R) :
    orbitIntegral R C v m true (ξ, γ) l = 0 := by
  letI := C.transport.groupHaar_isHaar
  unfold orbitIntegral
  simp_rw [orbitSheet_forward_nonintegral R C v m (ξ, γ) l _
    (fun h => ha ((orbitFrequency_integral_iff R ξ γ).mp h))]
  exact integral_zero _ _

lemma groupedOrbitTerm_forward_allowed {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (hx : AbsoluteExtraction R C) (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (Z : ℝ) (hZ : 0 < Z)
    (ha : (Quotient.out ξ : Fˣ).val ∈ R.A.R)
    (hb : ThetaReflectionData.rationalClass R.A (Quotient.out ξ) ∈ R.probe.correction.B) :
    groupedOrbitTerm R C v m true Z hZ ξ =
      (forwardMask R m (Quotient.out ξ) * forwardExterior R C (Quotient.out ξ) *
        Characters.L R v (Quotient.out ξ)) *
        (thetaReflectionGaussian ((q R.A (Quotient.out ξ)).val / Z) : ℂ) := by
  letI := C.transport.groupHaar_isHaar
  rw [groupedOrbitTerm_eq_integral R C hx]
  simp_rw [orbitIntegral_forward_factor R C v m ξ _ _ ha, tsum_mul_left]
  have he (l : PositiveAxis) := (forward_sheet_orbit R C v (Quotient.out ξ) hb l
    (pregroupingSheet R.A C.packet.v₀ l)
    (pregroupingSheet_fundamental R.A C.packet.v₀ C.transport.groupHaar l)).2
  simp_rw [pregroupingSheetHaar, he]
  have hm (t : PositiveAxis) : C.packet.kernel t.val *
      ((forwardMask R m (Quotient.out ξ) * forwardExterior R C (Quotient.out ξ)) *
        (Characters.L R v (Quotient.out ξ) *
          (C.packet.positiveSheet (q R.A (Quotient.out ξ) *
            ⟨t.val / Z, div_pos t.property hZ⟩) : ℂ))) =
      (forwardMask R m (Quotient.out ξ) * forwardExterior R C (Quotient.out ξ) *
        Characters.L R v (Quotient.out ξ)) *
        (C.packet.kernel t.val * (C.packet.positiveSheet (q R.A (Quotient.out ξ) *
          ⟨t.val / Z, div_pos t.property hZ⟩) : ℂ)) := by ring
  simp_rw [hm]
  rw [integral_const_mul, (forward_sheet_smoothing R C (Quotient.out ξ) Z hZ).2]

lemma groupedOrbitTerm_forward_nonintegral {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (Z : ℝ) (hZ : 0 < Z)
    (ha : (Quotient.out ξ : Fˣ).val ∉ R.A.R) :
    groupedOrbitTerm R C v m true Z hZ ξ = 0 := by
  unfold groupedOrbitTerm orbitTerm
  simp_rw [orbitIntegral_forward_nonintegral R C v m ξ _ _ ha, mul_zero]
  simp

lemma groupedOrbitTerm_forward_nonallowed {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (ξ : ThetaReflectionData.Frequency R.A) (Z : ℝ) (hZ : 0 < Z)
    (ha : (Quotient.out ξ : Fˣ).val ∈ R.A.R)
    (hb : ThetaReflectionData.rationalClass R.A (Quotient.out ξ) ∉ R.probe.correction.B) :
    groupedOrbitTerm R C v m true Z hZ ξ = 0 := by
  letI := C.transport.groupHaar_isHaar
  unfold groupedOrbitTerm orbitTerm
  simp_rw [orbitIntegral_forward_factor R C v m ξ _ _ ha,
    forwardSheetWord_nonallowed R C.packet v (Quotient.out ξ) hb]
  simp

end DedekindZetaZeroFree.OrbitExpansion

end
