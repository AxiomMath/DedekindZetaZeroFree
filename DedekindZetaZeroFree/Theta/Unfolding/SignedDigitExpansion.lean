module

public import DedekindZetaZeroFree.Theta.Unfolding.FactorizationAndMellinNormalizationData
public import DedekindZetaZeroFree.Adeles.Quotients.FundamentalDomainIntegrals

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical Topology ENNReal
open NumberField MeasureTheory
open ThetaProfileHaarSheets ThetaSheetExactUnfolding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def digitWeight (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) : ℂ :=
  ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
    let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    sexticFourierMask (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
      (Characters.psi R ⟨p.val, hp⟩) (ThetaDigitAverage.rowExponent R.A m.val p.val) (d p)

def digitParameter (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) : KPAdeles F :=
  ∑ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
    let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
    KPRationalAdelicSplitting.localAdele F (Sum.inr p.val)
      (-algebraMap (𝓞 F) (p.val.adicCompletion F)
        ((ThetaDigitAverage.residueLifts (ThetaDigitAverage.rowPrimes R.A m.val m.property)).lift p (d p)) /
        algebraMap F (p.val.adicCompletion F)
          (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A ⟨p.val, hp⟩) : F))

def signedArgument (m : ThetaReflectionData.Row R.A) (positive : Bool) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) : Group R :=
  (if positive then 1 else KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) *
    diagonal R y * KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12 (digitParameter R m d)

def signedDigits (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool) (y : R.A.G) : ℂ :=
  ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    digitWeight R m d * T.theta v (signedArgument R m positive y d)
def upperDigits (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool) (y : R.A.G) : ℂ :=
  ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    digitWeight R m d * upper R Q.dq (T.theta v) (signedArgument R m positive y d)

def weightedDigits (Q : AdmissibleFlatSources R) (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹ * signedDigits R Q T v m positive y
def weightedUpper (Q : AdmissibleFlatSources R) (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹ * upperDigits R Q T v m positive y

def quotientUpper (Q : AdmissibleFlatSources R) (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool)
    (l : PositiveAxis) (z : SheetQuotient R.A l) : ℂ :=
  weightedUpper R Q T P v m positive (Quotient.out z).val
def quotientTheta (Q : AdmissibleFlatSources R) (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (positive : Bool)
    (l : PositiveAxis) (z : SheetQuotient R.A l) : ℂ :=
  weightedDigits R Q T P v m positive (Quotient.out z).val

def upperAverage (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (positive : Bool) (l : PositiveAxis) : ℂ := by
  letI := N.groupHaar_isHaar
  exact ∫ z, quotientUpper R Q T P v m positive l z
    ∂sheetQuotientHaar R.A P.v₀ N.groupHaar l

def mainTerm (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (positive : Bool) (Z : ℝ) : ℂ :=
  if hZ : 0 < Z then ∫ t : PositiveAxis, P.kernel t.val *
    upperAverage R N Q T P v m positive ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar else 0

def thetaAverage (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (positive : Bool) (l : PositiveAxis) : ℂ := by
  letI := N.groupHaar_isHaar
  exact ∫ z, quotientTheta R Q T P v m positive l z
    ∂sheetQuotientHaar R.A P.v₀ N.groupHaar l

def smoothedTheta (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (positive : Bool) (Z : ℝ) : ℂ :=
  if hZ : 0 < Z then ∫ t : PositiveAxis, P.kernel t.val *
    thetaAverage R N Q T P v m positive ⟨t.val / Z, div_pos t.property hZ⟩ ∂positiveHaar else 0

structure DigitsDescent (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) : Prop where

  mask_frequency : ∀ (m : ThetaReflectionData.Row R.A) (a : Fˣ),
    (∀ p ∈ ThetaDigitAverage.rowPrimes R.A m.val m.property, p.valuation F (a : F) ≤ 1) →
    (∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
      digitWeight R m d * (adelicTraceCharacter F
        (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ)) =
      ∏ p : ThetaDigitAverage.rowPrimes R.A m.val m.property,
        let hp := ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp p.property).1
        sexticUnitPower (ThetaBranch.residueCharacter R.A R.σ ⟨p.val, hp⟩)
          (ThetaDigitAverage.rowExponent R.A m.val p.val) (ThetaBranch.unitResidue p.val a)
  theta_descent : ∀ v m b (γ : R.A.Gamma) y,
    signedDigits R Q T v m b (γ.val * y) = signedDigits R Q T v m b y
  upper_descent : ∀ v m b (γ : R.A.Gamma) y,
    upperDigits R Q T v m b (γ.val * y) = upperDigits R Q T v m b y
  weighted_theta_descent : ∀ v m b (γ : R.A.Gamma) y,
    weightedDigits R Q T P v m b (γ.val * y) = weightedDigits R Q T P v m b y
  weighted_upper_descent : ∀ v m b (γ : R.A.Gamma) y,
    weightedUpper R Q T P v m b (γ.val * y) = weightedUpper R Q T P v m b y
  weyl : ∀ v m y, signedDigits R Q T v m true y = signedDigits R Q T v m false y
  theta_integrable : ∀ v m b l, letI := N.groupHaar_isHaar;
    Integrable (quotientTheta R Q T P v m b l) (sheetQuotientHaar R.A P.v₀ N.groupHaar l)
  upper_integrable : ∀ v m b l, letI := N.groupHaar_isHaar;
    Integrable (quotientUpper R Q T P v m b l) (sheetQuotientHaar R.A P.v₀ N.groupHaar l)
  smoothing_integrable : ∀ v m b Z (hZ : 0 < Z), Integrable
    (fun t : PositiveAxis => P.kernel t.val * upperAverage R N Q T P v m b
      ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar

theorem DigitsDescent.quotientTheta_projection {N : TraceHaarTransport R}
    {Q : AdmissibleFlatSources R} {T : Realization R Q} {P : Packet R Q}
    (D : DigitsDescent R N Q T P) (v : R.A.UnitQuotient)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) (y : Sheet R.A l) :
    quotientTheta R Q T P v m b l (sheetProjection R.A l y) =
      weightedDigits R Q T P v m b y.val := by
  unfold quotientTheta
  have h := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  rw [← hv]
  exact D.weighted_theta_descent v m b ⟨γ.val.val, γ.property⟩ _

structure SameResidueProfiles (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (P : Packet R Q) : Prop where
  smooth : ∀ v κ, ContDiff ℝ 2 (logProfile (T.H P v κ))
  bounds : ∀ B : ℝ, 0 < B → ∀ j : ℕ, j ≤ 2 → ∃ K : ℝ, 0 ≤ K ∧ ∀ v κ x, 0 < x →
    ‖iteratedDeriv j (logProfile (T.H P v κ)) (Real.log x)‖ ≤
      K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B))
  finite_classes : Finite R.A.V
  absolute_sheet_jets : ∀ v κ (j : ℕ), j ≤ 2 → ∀ x : ℝ, 0 < x →
    letI : MeasurableSpace R.A.G1 := borel _;
    Integrable (fun y : R.A.G1 => iteratedDeriv j (fun t : ℝ =>
      T.sheetIntegrand P v κ (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)))
        (Real.log x)) R.probe.domain.measure
  absolute_sheet_bounds : ∀ B : ℝ, 0 < B → ∀ j : ℕ, j ≤ 2 →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v κ x (hx : 0 < x),
      letI : MeasurableSpace R.A.G1 := borel _;
      (∫ y : R.A.G1, ‖iteratedDeriv j (fun t : ℝ =>
        T.sheetIntegrand P v κ (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)))
          (Real.log x)‖ ∂(R.probe.domain.measure)) ≤
        K * min (Real.rpow x (1 / 8)) (Real.rpow x (-B))
  absolute_smoothing_jets : ∀ v κ (j : ℕ), j ≤ 2 → ∀ x : ℝ, 0 < x →
    Integrable (fun t : PositiveAxis => P.kernel t.val * iteratedDeriv j
      (fun z : ℝ => T.sheet P v κ ⟨Real.exp z / t.val, div_pos (Real.exp_pos z) t.property⟩)
      (Real.log x)) positiveHaar

def frequencyIntegrand (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A)
    (g : Group R) (q : KPAdditiveQuotient F) : ℂ :=
  T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
    star (adelicTraceCharacter F
      (algebraMap F (KPAdeles F) ((Quotient.out ξ : Fˣ) : F) * Quotient.out q) : ℂ)

def frequencyValue (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (ξ : ThetaReflectionData.Frequency R.A) (g : Group R) : ℂ :=
  ∫ q, frequencyIntegrand R Q T v ξ g q ∂Q.dq

def orbitFrequencyIntegrand (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (g : Group R) (q : KPAdditiveQuotient F) : ℂ :=
  T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
    star (adelicTraceCharacter F (algebraMap F (KPAdeles F)
      (((Quotient.out i.1 : Fˣ) * i.2.val : Fˣ) : F) * Quotient.out q) : ℂ)
def orbitFrequencyValue (Q : AdmissibleFlatSources R) (T : Realization R Q)
    (v : R.A.UnitQuotient) (i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A)
    (g : Group R) : ℂ := ∫ q, orbitFrequencyIntegrand R Q T v i g q ∂Q.dq

structure ReverseAbsolute (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) : Prop where
  period_integrable : ∀ v ξ g, Integrable (frequencyIntegrand R Q T v ξ g) Q.dq
  orbit_period_integrable : ∀ v i g, Integrable (orbitFrequencyIntegrand R Q T v i g) Q.dq
  orbit_pregrouping : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z),
    letI := N.groupHaar_isHaar;
    Summable (fun i : ThetaReflectionData.Frequency R.A × ThetaReflectionData.rationalGamma R.A =>
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ∫ t : PositiveAxis, ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖P.kernel t.val * digitWeight R m d *
            orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)‖
          ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩
          ∂positiveHaar)
  pregrouping : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z),
    letI := N.groupHaar_isHaar;
    Summable (fun ξ : ThetaReflectionData.Frequency R.A =>
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        ∫ t : PositiveAxis, ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
          ‖P.kernel t.val * digitWeight R m d *
            frequencyValue R Q T v ξ (signedArgument R m b z.val d)‖
          ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩
          ∂positiveHaar)
  orbit_smoothing_integrable : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z),
    ∀ i d, letI := N.groupHaar_isHaar;
    Integrable (fun t : PositiveAxis =>
      ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
        ‖P.kernel t.val * digitWeight R m d * orbitFrequencyValue R Q T v i
          (signedArgument R m b z.val d)‖
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar
  orbit_sheet_integrable : ∀ v (m : ThetaReflectionData.Row R.A) b i d (l : PositiveAxis),
    letI := N.groupHaar_isHaar;
    Integrable (fun z : Sheet R.A l => ‖digitWeight R m d *
      orbitFrequencyValue R Q T v i (signedArgument R m b z.val d)‖)
      (pregroupingSheetHaar R.A P.v₀ N.groupHaar l)
  smoothing_integrable : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ) (hZ : 0 < Z),
    ∀ ξ d, letI := N.groupHaar_isHaar;
    Integrable (fun t : PositiveAxis =>
      ∫ z : Sheet R.A ⟨t.val / Z, div_pos t.property hZ⟩,
        ‖P.kernel t.val * digitWeight R m d * frequencyValue R Q T v ξ
          (signedArgument R m b z.val d)‖
        ∂pregroupingSheetHaar R.A P.v₀ N.groupHaar ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar
  joint_integrable : ∀ v (m : ThetaReflectionData.Row R.A) (b : Bool) (Z : ℝ), 0 < Z →
    ∀ (ξ : ThetaReflectionData.Frequency R.A)
      (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)),
    letI := N.groupHaar_isHaar;
    ∀ l : PositiveAxis, Integrable
      (fun z : Sheet R.A l => ‖digitWeight R m d *
        frequencyValue R Q T v ξ (signedArgument R m b z.val d)‖)
      (pregroupingSheetHaar R.A P.v₀ N.groupHaar l)

  orbit_product_integrable : ∀ v (m : ThetaReflectionData.Row R.A) b Z (hZ : 0 < Z) i d,
    letI := N.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * orbitFrequencyValue R Q T v i
        (signedArgument R m b (sheetTranslation R.A P.v₀
          ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
      (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier))
  product_integrable : ∀ v (m : ThetaReflectionData.Row R.A) b Z (hZ : 0 < Z) ξ d,
    letI := N.groupHaar_isHaar;
    Integrable (fun p : PositiveAxis × R.A.G1 =>
      P.kernel p.1.val * digitWeight R m d * frequencyValue R Q T v ξ
        (signedArgument R m b (sheetTranslation R.A P.v₀
          ⟨p.1.val / Z, div_pos p.1.property hZ⟩ p.2).val d))
      (positiveHaar.prod ((kernelHaar R.A P.v₀ N.groupHaar).restrict (pregroupingDomain R.A).carrier))

def BothUpperZero (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) : Prop :=
  ∀ v m b l, upperAverage R N Q T P v m b l = 0

structure SignedUnfolding (N : TraceHaarTransport R) (Q : AdmissibleFlatSources R)
    (T : Realization R Q) (P : Packet R Q) where
  Ur : Finset R.A.Rˣ
  units : ActualRowTransfer.UnitRepresentatives R.A Ur
  row_class : R.A.Rˣ → R.A.UnitQuotient
  forward_smoothing_integrable : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ → ∀ Z (hZ : 0 < Z),
    Integrable (fun t : PositiveAxis => P.kernel t.val *
      thetaAverage R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d)
        true ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar
  reverse_smoothing_integrable : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ → ∀ Z (hZ : 0 < Z),
    Integrable (fun t : PositiveAxis => P.kernel t.val *
      thetaAverage R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d)
        false ⟨t.val / Z, div_pos t.property hZ⟩) positiveHaar
  forward_unfolding : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ → ∀ Z, 0 < Z →
    ThetaReflectionData.forwardB R.A R.probe.coefficients
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) Z =
    smoothedTheta R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z -
      mainTerm R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) true Z
  reverse_unfolding : ∀ u ∈ Ur, ∀ h d : R.A.Exterior,
    Powerful h.val → Squarefree d.val → h.val ⊔ d.val = ⊤ → ∀ Z, 0 < Z →
    RMSeparatedExpansion.expansion R.A R.probe.allowed R.probe.unitReps R.σ
      (Characters.psi R) (Characters.L R (row_class u)) (T.H P (row_class u)) h d Z =
    smoothedTheta R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) false Z -
      mainTerm R N Q T P (row_class u) (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d) false Z

structure CertifiedPacket where
  aligned : RootAligned R
  transport : TraceHaarTransport R
  sources : AdmissibleFlatSources R
  realization : Realization R sources
  factorization : SourceFactorization R sources realization
  localHaarTransport : ∀ q, transport.finiteHaar q =
    ENNReal.ofReal (PoissonS.integerVolume F q) • (factorization.finiteData q).haar
  exterior : ExteriorCoefficients R sources realization factorization
  packet : Packet R sources
  forward : ForwardIdentity R sources realization packet
  constantTerm : ResidualConstantTerm R sources realization
  mellin : MellinGaussian R transport sources packet
  descent : DigitsDescent R transport sources realization packet
  profiles : SameResidueProfiles R sources realization packet
  absolute : ReverseAbsolute R transport sources realization packet
  upperZero : BothUpperZero R transport sources realization packet
  unfolding : SignedUnfolding R transport sources realization packet

end DedekindZetaZeroFree.MomentSources

end
