module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PU2TracePeakApproximation
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarmonicPolynomials.SymmetricPowerAction
public import DedekindZetaZeroFree.Analysis.FiniteDimensional.CompatibleComplexNorm
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SU2.WeylIntegration

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir

open scoped Matrix.Norms.L2Operator

noncomputable local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

noncomputable def basisExp {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (t : ℝ) : RawU2 :=
  ⟨NormedSpace.exp ((t : ℂ) • B b.1 b.2),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff]
      simp [hskew])⟩

noncomputable def basisLift {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (b : Fin d × Fin 3) (t : ℝ) : Fin d → RawU2 :=
  fun j => if j = b.1 then basisExp B hskew b t else 1

noncomputable def characterSecondDerivative {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) (g : Fin d → RawU2) : ℂ :=
  deriv (fun t : ℝ => deriv (fun s : ℝ =>
    star (rawCharacter ℓ (g * basisLift B hskew b t * basisLift B hskew b s))) 0) 0

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir
