module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorCompactInvariance

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma rationalValue_left_root {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (a : Fˣ) (g : Group R) (t : KPAdeles F) :
    OrbitFrequencies.rationalValue R C.realization v a
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 t * g) =
      (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * t) : ℂ) *
        OrbitFrequencies.rationalValue R C.realization v a g := by
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
    (algebraMap F (KPAdeles F) (a : F) * t)
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have he : (algebraMap F (KPAdeles F) (a : F) * t) *
      algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = t := by
    rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (algebraMap F (KPAdeles F) (a : F) * t) * A =
      A * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        ((algebraMap F (KPAdeles F) (a : F) * t) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
  rw [he] at hc
  rw [OrbitFrequencies.rationalValue_eq_fourier R C.realization, ← mul_assoc, ← hc, mul_assoc]
  letI := C.sources.quotientHaar
  rw [ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R C.sources.dq (C.realization.theta v)
    (ExteriorWhittakerValues.StoredWhittaker.core_rational_root R C.factorization (C.factorization.selected v) |>
      fun h => by simpa only [C.factorization.selected_eq] using h) _ (A * g) (C.factorization.period_integrable v (A * g))]
  have hχ := adelicTraceQuotientCharacter_mk F (algebraMap F (KPAdeles F) (a : F) * t)
  refine congrArg₂ (fun z : Circle => fun c : ℂ => (z : ℂ) * c) hχ ?_
  exact (OrbitFrequencies.rationalValue_eq_fourier R C.realization v a g).symm

lemma diagonal_commute_digit_root (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Commute (diagonal R y)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d)) := by
  unfold digitParameter
  have hsum : ∀ (s : Finset (ThetaDigitAverage.rowPrimes R.A m.val m.property))
      (f : (ThetaDigitAverage.rowPrimes R.A m.val m.property) → KPAdeles F),
      (∀ p ∈ s, Commute (diagonal R y)
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (f p))) →
      Commute (diagonal R y)
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (∑ p ∈ s, f p)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      have hz : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
        (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
      rw [hz]
      exact Commute.one_right (diagonal R y)
    | @insert p s hp ih =>
      intro h
      rw [Finset.sum_insert hp, KPGlobalTorusFunctionData.N_add]
      exact (h p (Finset.mem_insert_self _ _)).mul_right
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))
  apply hsum
  intro p hp
  exact diagonal_commute_exterior_root R y
    ⟨p.val, ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1⟩ _

lemma forward_digit_average {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : ThetaExpansion.SignedExpansion.OrbitIndex R) (y : R.A.G) :
    (∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
        (signedArgument R m true y d)) =
    (∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      digitWeight R m d * (adelicTraceCharacter F
        (algebraMap F (KPAdeles F) ((Quotient.out i.1) * i.2.val : Fˣ) * digitParameter R m d) : ℂ)) *
      orbitFrequencyValue R C.sources C.realization v i (diagonal R y) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hv (g : Group R) : orbitFrequencyValue R C.sources C.realization v i g =
      OrbitFrequencies.rationalValue R C.realization v ((Quotient.out i.1) * i.2.val) g := rfl
  rw [hv, signedArgument]
  simp only [Bool.true_eq, ↓reduceIte, one_mul]
  have hc := congrArg (fun g : Group R => OrbitFrequencies.rationalValue R C.realization v
    ((Quotient.out i.1) * i.2.val) g) (diagonal_commute_digit_root R y m d).eq
  have he := hc.trans (rationalValue_left_root R C v _ _ _)
  exact (congrArg (fun z : ℂ => digitWeight R m d * z) he).trans
    ((mul_assoc _ _ _).symm.trans (congrArg (fun z : ℂ =>
      (digitWeight R m d * (adelicTraceCharacter F
        (algebraMap F (KPAdeles F) ((Quotient.out i.1) * i.2.val : Fˣ) * digitParameter R m d) : ℂ)) * z)
      (hv _).symm))

lemma forward_digit_mask {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (i : ThetaExpansion.SignedExpansion.OrbitIndex R) (y : R.A.G)
    (ha : ∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property,
      p.valuation F ((Quotient.out i.1) * i.2.val : Fˣ) ≤ 1) :
    (∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
        (signedArgument R m true y d)) =
    (∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
      let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
      sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
        (ThetaDigitAverage.rowExponent R.A m.val p.val)
        (ThetaBranch.unitResidue p.val ((Quotient.out i.1) * i.2.val))) *
      orbitFrequencyValue R C.sources C.realization v i (diagonal R y) := by
  rw [forward_digit_average R C, C.descent.mask_frequency m _ ha]

end DedekindZetaZeroFree.OrbitExpansion

end
