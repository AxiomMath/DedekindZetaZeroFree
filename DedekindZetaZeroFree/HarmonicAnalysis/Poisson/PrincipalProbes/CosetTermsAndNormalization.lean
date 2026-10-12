module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries

@[expose] public section

namespace DedekindZetaZeroFree.ProbeCoset
noncomputable section
open scoped Classical NumberField
open MeasureTheory IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance localProductMeasurable
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    MeasurableSpace (SLocalProduct F S) := borel _

def modulus (A : SArithmeticData F) (a : A.R) : ℝ :=
  (FiniteTransform.exteriorNorm A.R.toSubring a : ℝ)

def originalTerm (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (s a : A.R) (hs : s ≠ 0)
    (X : ℝ) (t : A.G1) (m : A.R) : ℂ := by
  letI := D.finiteResidue s hs
  exact (Real.sqrt (modulus A s) : ℂ)⁻¹ *
    FiniteTransform.gaussSum A.R.toSubring s (D.character s) D.additiveCharacter (-m) *
    D.character a (FiniteTransform.residueMap A.R.toSubring a m) *
    W0 (sLocalDiagonal F A.Sf (m : F) *
      NormalizedProbe.asLocalPoint A
        (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹))

def frequencyPoint (A : SArithmeticData F) (s a : A.R)
    (X : ℝ) (t : A.G1) (h : A.R) : SLocalProduct F A.Sf :=
  NormalizedProbe.asLocalPoint A
      ((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X)) *
    sLocalDiagonal F A.Sf ((h : F) / ((s : F) * (a : F)))

def frequencyTerm (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (W0 : SLocalProduct F A.Sf → ℂ) (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (t : A.G1) (h : A.R) : ℂ := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  exact FiniteTransform.finiteCoefficient A.R.toSubring s a h
      (D.character s) (D.character a) D.additiveCharacter *
    ProbeWeight.fourier F A.Sf e μ W0 (frequencyPoint A s a X t h)

structure Normalization (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) where
  localMeasure : (v : ↥A.Sf) → Measure (v.val.adicCompletion F)
  localHaar : ∀ v, (localMeasure v).IsAddHaarMeasure
  localNormalization : PoissonS.LocalNormalization F A.Sf localMeasure
  traceConductor : PoissonS.TraceConductor F A.Sf P.finiteTrace
  containsDifferent : PoissonS.ContainsDifferent F A.Sf
  sameMeasure : P.additiveMeasure =
    Measure.map (PoissonS.localProductToSpace F A.Sf).symm
      (PoissonS.productMeasure F A.Sf localMeasure)

theorem modulus_pos (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    {a : A.R} (ha : a ≠ 0) : 0 < modulus A a := by
  letI := D.finiteResidue a ha
  rw [modulus, FiniteTransform.exteriorNorm, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_pos_iff.mpr inferInstance

end
end DedekindZetaZeroFree.ProbeCoset
