module

public import DedekindZetaZeroFree.Moments.Reflected.SeparatedMeanSquareBounds
public import DedekindZetaZeroFree.Adeles.Characters.RayCharacterCorrectionFactors

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

def asLocalPoint (A : SArithmeticData F) (t : A.G) : SLocalProduct F A.Sf :=
  A.localToAdditive t

def rowB (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (m : A.R) (Z : ℝ) : ℂ :=
  if hm : m = 0 then 0 else ThetaReflectionData.forwardB A D ⟨m, hm⟩ Z

def gaussRow (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s : A.Exterior) (m : A.R) : ℂ := by
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  exact (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ *
    FiniteTransform.gaussSum A.R.toSubring (D.generator s)
      (D.character (D.generator s)) D.additiveCharacter (-m)

def radialSection (A : SArithmeticData F) (T : ℝ) : A.G :=
  if hT : 0 < T then A.radialSection T hT else 1

structure DomainData (A : SArithmeticData F) where
  domain : Set A.G1
  measurable : @MeasurableSet A.G1 (borel A.G1) domain
  relativelyCompact : IsCompact (closure domain)
  fundamental : ∀ t : A.G1, ∃! γ : A.Gamma1, (γ : A.G1) * t ∈ domain
  measure : @Measure A.G1 (borel A.G1)
  haar : @Measure.IsHaarMeasure A.G1 _ _ (borel A.G1) measure

def integrand (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (P : DomainData A) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (X Y Z : ℝ) (t : A.G1) : ℂ :=
  (Y⁻¹ : ℂ) * ∑' s : A.Exterior,
    ((W1 (A.exteriorNorm s / Y) : ℂ) *
      (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹) *
      ∑' m : A.R,
        gaussRow A D s m *
          W0 (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹)) *
          rowB A D m Z

def probe (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (P : DomainData A) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (X Y Z : ℝ) : ℂ := by
  letI : MeasurableSpace A.G1 := borel A.G1
  exact ∫ t in P.domain, integrand A D P W0 W1 X Y Z t ∂P.measure

structure FrequencyRepresentatives (A : SArithmeticData F)
    (G : ThetaBranch.AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) where
  reps : Set (ThetaReflectionData.Row A)
  containsOne : (⟨(1 : A.R), one_ne_zero⟩ : ThetaReflectionData.Row A) ∈ reps
  sixthFree : ∀ u ∈ reps, ∀ p : ThetaBranch.ExteriorPrime A,
    0 ≤ ThetaBranch.order p.val (ThetaReflectionData.rowUnit A u) ∧
      ThetaBranch.order p.val (ThetaReflectionData.rowUnit A u) < 6
  unitClasses : ∀ ε : A.UnitQuotient, ∃ u ∈ reps, ∃ γ : A.U,
    ThetaReflectionData.rowUnit A u =
      (U.representative ε).val * γ.val ^ 6
  factorization : ∀ h : ThetaReflectionData.Row A,
    ∃! x : {u // u ∈ reps} × A.Exterior,
      ∃ γ : A.U, ThetaReflectionData.rowUnit A h =
        ThetaReflectionData.rowUnit A x.1.val * G.generator x.2 ^ 6 * γ.val ^ 6

def exteriorSexticRowCharacter (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (t : A.R) : ℂ :=
  if ht : t = 0 then
    if I.val = ⊤ then 1 else 0
  else
    ∏ p ∈ (ThetaBranch.support I.val).attach,
      (ThetaBranch.symbol A σ
        ⟨p.val, ThetaBranch.support_outside A I p.val p.property⟩
        (ThetaReflectionData.rowUnit A ⟨t, ht⟩)) ^
          (idealPrimeExponent p.val.asIdeal I.val)

structure PrincipalData (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces) where
  principal : η.IsPrincipal
  correction : A.GaussCorrectionOutput σ η hS
  principalIdele : correction.η_id = 1
  coefficients : ComparisonPoissonCoefficientData F A
  allowed : ThetaBranch.AllowedRecipe A
  sameComplement : allowed.B = correction.B
  sameGenerator : ∀ I, (allowed.generator I : F) = (coefficients.generator I : F)
  exteriorCharacters : ∀ (I : A.Exterior) (a t : A.R), A.Generates I a →
    coefficients.character a (FiniteTransform.residueMap A.R.toSubring a t) =
      exteriorSexticRowCharacter A σ I t
  theta_principal : ∀ m : ThetaReflectionData.Row A,
    coefficients.theta m.val =
      (A.correctionLS correction.Λ correction.G 1
        (A.diagonal (ThetaReflectionData.rowUnit A m)) : ℂ)
  gammaTwo_recipe : ThetaReflectionData.GammaTwoCompatibility A coefficients
  sixthUnitCharacters : ThetaReflectionData.SixthUnitCharacterCompatibility A coefficients
  unitReps : ThetaBranch.UnitRepresentatives A
  frequencies : FrequencyRepresentatives A allowed unitReps
  domain : DomainData A
  finiteTrace : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle
  continuousTrace : ∀ v, Continuous (finiteTrace v)
  traceCompatible : ProbeAdditive.TraceCompatible F A.Sf finiteTrace
  sameTrace : ∀ x : F, coefficients.additiveCharacter x =
    ProbeAdditive.phase F A.Sf finiteTrace (sLocalDiagonal F A.Sf x)
  additiveMeasure : @Measure (SLocalProduct F A.Sf) (borel _)
  additiveHaar : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _)
    additiveMeasure
  multiplicativeMeasure : @Measure (SLocalProduct F A.Sf)ˣ
    (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _))
  multiplicativeHaar : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
    (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) multiplicativeMeasure
  W0 : SLocalProduct F A.Sf → ℂ
  W1 : ProbeRealAnnularWeight
  annular : ProbeWeight.IsAnnularTensor F A.Sf W0
  compactSupport : HasCompactSupport W0
  supportUnits : tsupport W0 ⊆ {x | IsUnit x}
  nonzero : W0 ≠ 0
  zeroFrequency : ProbeWeight.fourier F A.Sf finiteTrace additiveMeasure W0 0 = 0
  nonzeroMellin : ProbeWeight.fourierMellin F A.Sf finiteTrace additiveMeasure
    multiplicativeMeasure W0 (1 / 6) ≠ 0

def principalProbe (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : {x : ℝ // 0 < x}) : ℂ :=
  probe A P.coefficients P.domain P.W0 P.W1 X.val Y.val Z.val

def separatedMellinSeries (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (u : A.R) (ξ w z : ℂ) : ℂ :=
  comparisonEulerPoissonSeries F A D u ξ w z

theorem separatedMellinSeries_eq_tsum (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (u : A.R) (ξ w z : ℂ) :
    separatedMellinSeries A D u ξ w z =
      ∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior,
        comparisonEulerPoissonSummand F A D u ξ w z i.1 i.2.1 i.2.2.1 i.2.2.2 := rfl

def principalSeparatedMellinSeries (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS)
    (u : {u // u ∈ P.frequencies.reps}) (ξ w z : ℂ) : ℂ :=
  separatedMellinSeries A P.coefficients u.val.val ξ w z

theorem rowB_nonzero (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (m : ThetaReflectionData.Row A)
    (Z : ℝ) : rowB A D m.val Z = ThetaReflectionData.forwardB A D m Z := by
  simp only [rowB, dif_neg m.property]

end
end NormalizedProbe
end DedekindZetaZeroFree
