module

public import DedekindZetaZeroFree.Moments.Comparison.FarDyadSummability
public import DedekindZetaZeroFree.LFunctions.Hecke.RayContinuationData
public import DedekindZetaZeroFree.CharacterSums.Gauss.ResidueRowFourierTransform
public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyDyadCounts
public import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles
public import DedekindZetaZeroFree.Moments.Principal.MellinContourDecomposition

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
open MeasureTheory Complex
set_option maxHeartbeats 1600000

structure ComparisonPoissonCoefficientData (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) where
  generator : A.Exterior → A.R
  generates : ∀ I, A.Generates I (generator I)
  finiteResidue : ∀ a : A.R, a ≠ 0 → Fintype (FiniteTransform.Residue A.R.toSubring a)
  character : (a : A.R) → MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ
  additiveCharacter : AddChar F ℂ
  gammaTwo : ExteriorSquarefreeIdeal A.cS → ℂ
  theta : A.R → ℂ

def comparisonPoissonFiniteCoefficient
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior) (h : A.R) : ℂ := by
  let a := D.generator c.val * D.generator n ^ 3
  have ha : a ≠ 0 := mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  letI := D.finiteResidue a ha
  exact FiniteTransform.finiteCoefficient A.R.toSubring (D.generator s) a h
    (D.character (D.generator s)) (D.character a) D.additiveCharacter

def comparisonEulerPoissonSummand
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.R)
    (ξ w z : ℂ) (c : ExteriorSquarefreeIdeal A.cS) (n s r : A.Exterior) : ℂ :=
  D.gammaTwo c * D.theta (D.generator c.val * D.generator n ^ 3) *
    comparisonPoissonFiniteCoefficient F A D c n s (u * D.generator r ^ 6) *
    comparisonRealPower (A.exteriorNorm c.val) (-1 / 2 - ξ) *
    comparisonRealPower (A.exteriorNorm n) (-1 - 3 * ξ) *
    comparisonRealPower (A.exteriorNorm s) (-w) *
    comparisonRealPower (A.exteriorNorm r) (-6 * z)

def comparisonEulerPoissonSeries
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.R) (ξ w z : ℂ) : ℂ :=
  ∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior,
    comparisonEulerPoissonSummand F A D u ξ w z i.1 i.2.1 i.2.2.1 i.2.2.2

structure ComparisonMellinWeights where
  M : ℂ → ℂ
  W1Hat : ℂ → ℂ

def comparisonPrincipalIncompleteL
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (s : ℂ) : ℂ :=
  P.L s * ∏ v ∈ A.Sf,
    (1 - η v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

def comparisonPrincipalResidue
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) : ℂ :=
  P.R 1 * ∏ v ∈ A.Sf,
    (1 - η v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-1))

def comparisonPrincipalSpectralTransform
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (Hη : ℂ → ℂ) (Z : ℝ) : ℂ :=
  comparisonVerticalIntegral 2 (fun s =>
    comparisonRealPower Z (comparisonC s) * Complex.exp ((s - 5 / 6) ^ 2) *
      Hη s / comparisonPrincipalIncompleteL F A η hη P s)

def comparisonPrincipalConstant
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (W : ComparisonMellinWeights) : ℂ :=
  (comparisonPrincipalResidue F A η hη P ^ 2 / 6) * W.M (1 / 6) * W.W1Hat 1

def comparisonMellinWeightsFromProbe
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight) :
    ComparisonMellinWeights :=
  { M := @ProbeWeight.fourierMellin F _ _ A.Sf e μ ν W0
    W1Hat := probeRealWeightMellin W1 }

theorem comparisonPrincipalSpectralTransform_eq_f
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (Hη : ℂ → ℂ) (Z : ℝ) :
    comparisonPrincipalSpectralTransform F A η hη P Hη Z =
      PrincipalZShift.f Z (comparisonPrincipalIncompleteL F A η hη P) Hη := by
  unfold comparisonPrincipalSpectralTransform PrincipalZShift.f
    PrincipalZShift.transformKernel
  congr 1
  funext s
  ring

theorem comparisonPrincipalConstant_eq_c₀
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (W : ComparisonMellinWeights) :
    comparisonPrincipalConstant F A η hη P W =
      PrincipalZShift.c₀ (comparisonPrincipalResidue F A η hη P) W.M W.W1Hat := rfl

theorem comparisonPrincipalConstant_ne_zero
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (η : RayClassCharacter F A.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F A.modulus η) (W : ComparisonMellinWeights)
    (hRS : comparisonPrincipalResidue F A η hη P ≠ 0)
    (hM : W.M (1 / 6) ≠ 0) (hW : W.W1Hat 1 ≠ 0) :
    comparisonPrincipalConstant F A η hη P W ≠ 0 := by
  rw [comparisonPrincipalConstant_eq_c₀]
  exact PrincipalZShift.c₀_ne_zero _ _ _ hRS hM hW

end
end DedekindZetaZeroFree
