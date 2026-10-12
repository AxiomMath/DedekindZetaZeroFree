module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
namespace TripleMellinRaw
noncomputable section
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) :=
  borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

def poissonLocalEquiv (A : SArithmeticData F) :
    PoissonS.Space F A.Sf ≃+ SLocalProduct F A.Sf :=
  (((NumberField.mixedEmbedding.euclidean.toMixed F).toAddEquiv.trans
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv).prodCongr
      (AddEquiv.refl _))

def poissonAdditiveMeasure (A : SArithmeticData F)
    (μ : (v : ↥A.Sf) → @Measure (v.val.adicCompletion F) (borel _)) :
    @Measure (SLocalProduct F A.Sf) (borel _) :=
  Measure.map (poissonLocalEquiv A) (PoissonS.productMeasure F A.Sf μ)

structure MellinNormalizationData (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) where
  finiteMeasure : (v : ↥A.Sf) → @Measure (v.val.adicCompletion F) (borel _)
  finiteHaar : ∀ v, @Measure.IsAddHaarMeasure (v.val.adicCompletion F) _ _
    (borel _) (finiteMeasure v)
  localNormalization : PoissonS.LocalNormalization F A.Sf finiteMeasure
  containsDifferent : PoissonS.ContainsDifferent F A.Sf
  sameAdditiveMeasure : P.additiveMeasure = poissonAdditiveMeasure A finiteMeasure
  sameFiniteTrace : ∀ v, P.finiteTrace v = ResidueTrace.localTraceCharacter v.val

  disintegration : @ProbeSheet.HaarDisintegration F _ _ A
    P.multiplicativeMeasure P.domain.measure

def principalMellinWeights (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) : ComparisonMellinWeights :=
  comparisonMellinWeightsFromProbe F A P.finiteTrace P.additiveMeasure
    P.multiplicativeMeasure P.W0 P.W1

def principalMellinFrequencySum (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (ξ w z : ℂ) : ℂ :=
  ∑' u : {u // u ∈ P.frequencies.reps},
    comparisonRealPower
      (FiniteTransform.exteriorNorm A.R.toSubring u.val.val : ℝ) (-z) *
      principalSeparatedMellinSeries A σ η hS P u ξ w z

def principalTripleMellinKernel (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ) (ξ w z : ℂ) : ℂ :=
  comparisonRealPower X (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) * comparisonRealPower Y (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * (principalMellinWeights A σ η hS P).M z *
    (principalMellinWeights A σ η hS P).W1Hat w *
    principalMellinFrequencySum A σ η hS P ξ w z

def principalTripleMellinHeights (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ) (t : Fin 3 → ℝ) : ℂ :=
  principalTripleMellinKernel A σ η hS P X Y Z
    (4 + (t 0 : ℂ) * Complex.I) (4 + (t 1 : ℂ) * Complex.I)
    (2 + (t 2 : ℂ) * Complex.I)

def tripleMellinNormalization : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 3

def principalTripleMellinIntegral (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ) : ℂ :=
  tripleMellinNormalization *
    ∫ t : Fin 3 → ℝ, principalTripleMellinHeights A σ η hS P X Y Z t

def iteratedTripleMellinIntegral (f : (Fin 3 → ℝ) → ℂ)
    (order : Equiv.Perm (Fin 3)) : ℂ :=
  tripleMellinNormalization *
    ∫ t0 : ℝ, ∫ t1 : ℝ, ∫ t2 : ℝ,
      f (fun i => (![t0, t1, t2] : Fin 3 → ℝ) (order.symm i))

end
end TripleMellinRaw
end NormalizedProbe
end DedekindZetaZeroFree
