module

public import DedekindZetaZeroFree.Adeles.Lattices.NormalizedRayCosetLattice
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayTheta

variable (K : Type) [Field K] [NumberField K]

def q (t : ℝ) (h : RayCoset.logHyperplane K) : InfinitePlace K → ℝ :=
  fun v => t ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp (h.val v)

variable {K}

def fδ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
    (t : ℝ) : ℂ :=
  if 0 < t then
    (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ *
      ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
        ∑' ℓ : RayCoset.normalizedLattice D,
          RayParity.gδ K δ (RayParity.Q K (q K t h)
            (RayCoset.normalizedBasepoint D + (ℓ : euclidean.mixedSpace K)))
        ∂Theta.normalizedLogHaar K
  else 0

def gδDual (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
    (t : ℝ) : ℂ :=
  if 0 < t then
    ((RayCoset.rayUnitTorsionCard K D.m : ℂ) *
      (RayCoset.modulusCovolume K D.m : ℂ))⁻¹ *
      ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
        ∑' lam : Theta.dualLattice (RayCoset.normalizedLattice D),
          Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
            (inner ℝ (lam : euclidean.mixedSpace K)
              (RayCoset.normalizedBasepoint D) : ℂ)) *
            RayParity.gδ K δ (RayParity.Q K (q K t (-h))
              (lam : euclidean.mixedSpace K))
        ∂Theta.normalizedLogHaar K
  else 0

def f0δ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) : ℂ :=
  if δ = ∅ ∧ (0 : euclidean.mixedSpace K) ∈ RayCoset.normalizedAffineCoset D then
    (RayCoset.rayUnitDomainVolume K D.m D.modulus_ne_bot : ℂ) /
      (RayCoset.rayUnitTorsionCard K D.m : ℂ)
  else 0

def g0δ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) : ℂ :=
  if δ = ∅ then
    (RayCoset.rayUnitDomainVolume K D.m D.modulus_ne_bot : ℂ) /
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) *
        (RayCoset.modulusCovolume K D.m : ℂ))
  else 0

end DedekindZetaZeroFree.AbelianQuotient.RayTheta

end
