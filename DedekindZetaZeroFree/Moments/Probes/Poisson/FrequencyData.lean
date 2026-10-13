module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawFixed

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure RawPackage (R : PrincipalMellin.ActualRecipe S η) where

  C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad

  U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A

  P : Frequency R → Detector.PrimitiveFrequencyCharacter F

  M : Frequency R → Detector.PrimitiveFrequencyCharacter F

  plus : Frequency R → ℂ → ℂ

  minus : Frequency R → ℂ → ℂ
  correction_eq : R.probe.correction = C.correction
  U_u : ∀ u : Frequency R, (U u).u = u.val.val
  deletion_finite : ∀ u : Frequency R, (RawHeckeRows.rawDeletionSet (U u)).Finite
  plus_mask : ∀ (u : Frequency R) (I : R.A.Exterior),
    AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (P u) (RawHeckeRows.rawDeletionSet (U u)) I.val
  minus_mask : ∀ (u : Frequency R) (I : R.A.Exterior),
    AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (M u) (RawHeckeRows.rawDeletionSet (U u)) I.val
  plus_diff : ∀ u : Frequency R, ¬ (P u).character.IsPrincipal →
    DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re}
  minus_diff : ∀ u : Frequency R, ¬ (M u).character.IsPrincipal →
    DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re}
  plus_eq : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
    plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s
  minus_eq : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
    minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s

  nonprincipal : ∀ u : Frequency R, u ≠ principalFrequency R →
    ¬ (P u).character.IsPrincipal ∧ ¬ (M u).character.IsPrincipal

theorem RawPackage.exists_at_context (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    ∃ pkg : RawPackage R, pkg.C = C := by
  obtain ⟨_, U, _, hU⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨P, M, hfinite, hP, hM⟩ := RawHeckeRows.actual_raw_masked_inducers R C hC U hU
  have hSD (u : Frequency R) :
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆
        RawHeckeRows.rawDeletionSet (U u) :=
    Set.subset_union_left
  have hplus (u : Frequency R) :=
    RawHeckeRows.deleted_exterior_series_continuation R.A (P u)
      (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u)) (hP u)
  have hminus (u : Frequency R) :=
    RawHeckeRows.deleted_exterior_series_continuation R.A (M u)
      (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.minusExteriorCoefficient R.σ R.target (U u)) (hM u)
  choose plus hpDiff hpEq using hplus
  choose minus hmDiff hmEq using hminus
  exact ⟨{
    C := C, U := U, P := P, M := M, plus := plus, minus := minus
    correction_eq := hC, U_u := hU, deletion_finite := hfinite
    plus_mask := hP, minus_mask := hM, plus_diff := hpDiff, minus_diff := hmDiff
    plus_eq := hpEq, minus_eq := hmEq
    nonprincipal := fun u hu =>
      RawHeckeRows.actual_raw_inducers_nonprincipal R u (U u) (hU u) hu (P u) (M u)
        (hP u) (hM u) }, rfl⟩

theorem RawPackage.exists (R : PrincipalMellin.ActualRecipe S η) : Nonempty (RawPackage R) := by
  obtain ⟨C, _, hC, _⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨pkg, _⟩ := RawPackage.exists_at_context R C hC
  exact ⟨pkg⟩

namespace FixedData

variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

def pkg : RawPackage D.recipe :=
  (RawPackage.exists_at_context D.recipe D.context rfl).choose

theorem pkg_C : (pkg D).C = D.context :=
  (RawPackage.exists_at_context D.recipe D.context rfl).choose_spec

def freq (u : D.Row) : Frequency D.recipe :=
  ⟨⟨u.toFrequency.u, (DedekindZetaZeroFree.Quantitative.FixedData.Row.u_mem_reps u).choose⟩,
    (DedekindZetaZeroFree.Quantitative.FixedData.Row.u_mem_reps u).choose_spec⟩

theorem q_eq_frequencyNorm (u : D.Row) : D.q u = frequencyNorm D.recipe (freq D u) := rfl

def rawFrequency (u : Frequency D.recipe) : AllRowEuler.InitialSeparation.RawFrequency D.recipe.A :=
  (pkg D).U u

def primPlus (u : Frequency D.recipe) : Detector.PrimitiveFrequencyCharacter F := (pkg D).P u

def primMinus (u : Frequency D.recipe) : Detector.PrimitiveFrequencyCharacter F := (pkg D).M u

theorem rawFrequency_u (u : Frequency D.recipe) : (rawFrequency D u).u = u.val.val :=
  (pkg D).U_u u

theorem rawFrequency_norm (u : Frequency D.recipe) :
    (D.recipe.A.exteriorNorm (rawFrequency D u).ideal : ℝ) = frequencyNorm D.recipe u := by
  unfold frequencyNorm FiniteTransform.exteriorNorm
  rw [← rawFrequency_u D u]
  change (D.recipe.A.exteriorNorm (rawFrequency D u).ideal : ℝ) =
    (Nat.card (D.recipe.A.R ⧸ Ideal.span {(rawFrequency D u).u}) : ℝ)
  rw [(rawFrequency D u).generates.2, D.recipe.A.exteriorResidue_card]
  rfl

def rawFactor (u : Frequency D.recipe) (ξ w z : ℂ) : ℂ :=
  D.recipe.L (6 * z) * (pkg D).plus u w *
    AllRowEuler.InitialSeparation.correctionProduct D.context (rawFrequency D u) ξ w z /
    (pkg D).minus u ξ

def rawKernel (u : Frequency D.recipe) (ξ w z : ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) *
    Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w *
    (frequencyNorm D.recipe u : ℂ) ^ (-z) * rawFactor D u ξ w z

def Iz (u : Frequency D.recipe) (ξ w : ℂ) (v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral v (fun z => rawKernel D u ξ w z Z)

def Iwz (u : Frequency D.recipe) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w => Iz D u ξ w v Z)

def triple (u : Frequency D.recipe) (x y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral x (fun ξ => Iwz D u ξ y v Z)

def initialRowIntegral (u : Frequency D.recipe) (Z : ℝ) : ℂ := triple D u 4 4 2 Z

def rawExceptionalSet (ρ U : ℝ) : Set (Frequency D.recipe) :=
  {u | u ≠ principalFrequency D.recipe ∧ U ≤ frequencyNorm D.recipe u ∧
    frequencyNorm D.recipe u < 2 * U ∧
    ∃ s : ℂ, DetectorDef.IsLZero (primMinus D u) s ∧ DetectorDef.σ₀ ≤ s.re ∧
      |s.im| ≤ 4 * U ^ ρ}

theorem principal_unique {u v : Frequency D.recipe} (hu : u.val.val = 1)
    (hv : v.val.val = 1) : u = v :=
  Subtype.ext (Subtype.ext (hu.trans hv.symm))

theorem freq_principal (u : Frequency D.recipe) (hu : u.val.val = 1) :
    u = principalFrequency D.recipe :=
  principal_unique D hu rfl

theorem freq_row_principal (u : D.Row) (hu : DedekindZetaZeroFree.Quantitative.FixedData.Row.u u = 1) :
    freq D u = principalFrequency D.recipe :=
  freq_principal D _ hu

theorem prim_nonprincipal (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe) :
    ¬ (primPlus D u).character.IsPrincipal ∧ ¬ (primMinus D u).character.IsPrincipal :=
  (pkg D).nonprincipal u hu

end FixedData

end

end DedekindZetaZeroFree.Quantitative.RawFixed
