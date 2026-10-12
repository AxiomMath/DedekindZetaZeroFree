module

public import DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice
public import DedekindZetaZeroFree.Theta.Unfolding.UnitSlabRadialAngularIntegration
public import DedekindZetaZeroFree.Arithmetic.Ideals.IdealElementDecomposition

@[expose] public section

noncomputable section

open Classical MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

abbrev Angular := {v : InfinitePlace K // v ≠ w₀} → ℝ

def angularLift (u : Angular K) : mixedEmbedding.realSpace K :=
  fun v ↦ if h : v = w₀ then 0 else u ⟨v, h⟩

def radialLift (a : ℝ) : mixedEmbedding.realSpace K :=
  fun v ↦ if v = w₀ then a else 0

def angularCube : Set (Angular K) :=
  Set.univ.pi (fun _ ↦ Set.Ico (0 : ℝ) 1)

def mixedThetaCovolume (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
    Real.sqrt |(discr K : ℝ)|

def mixedThetaShape (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) : InfinitePlace K → ℝ :=
  expMapBasis (angularLift K u +
    radialLift K ((Real.log t - Real.log (mixedThetaCovolume K I)) /
      (Module.finrank ℚ K : ℝ)))

def mixedRadialTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (u : Angular K) : ℂ :=
  fractionalShapeIdealTheta K I (mixedThetaShape K I t u)
    (fun v ↦ ne_of_gt (expMapBasis_pos _ v))

def mixedAngularAverage (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in angularCube K, mixedRadialTheta K I t u

def mixedNegAngularAverage (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  ∫ u in angularCube K, mixedRadialTheta K I t (-u)

def alpha : ℝ :=
  (2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K /
    (torsionOrder K : ℝ)

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
