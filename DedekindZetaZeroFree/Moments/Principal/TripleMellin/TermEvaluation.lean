module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.ShearedKernelInversion

@[expose] public section

namespace DedekindZetaZeroFree.NormalizedProbe.TripleMellin
open TripleMellinRaw
noncomputable section
open MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem orbit_term_mellin (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P)
    (X Y Z : {x : ℝ // 0 < x}) (i : MellinSeriesIndex P) :
    ProbePoissonOrbitFormula.term A σ η hS P (frequencySection P)
      X.val Y.val Z.val (orbitIndexEquiv P i) =
      tripleMellinNormalization * ∫ t : ℝ × ℝ × ℝ,
        initialTripleMellinSummand P X.val Y.val Z.val i t := by
  exact TermRace.term_inversion_race P N X Y Z i

theorem probe_eq_mellin_integral (P : PrincipalData A σ η hS)
    (N : MellinNormalizationData A σ η hS P) (X Y Z : {x : ℝ // 0 < x}) :
    principalProbe A σ η hS P X Y Z =
      principalTripleMellinIntegral A σ η hS P X.val Y.val Z.val := by
  rw [probe_eq_reindexed_sum P N (frequencySection P)
    (frequencySection_leftInverse P) X Y Z]
  simp_rw [orbit_term_mellin P N X Y Z]
  rw [tsum_mul_left]
  exact (integral_eq_sum P X.val Y.val Z.val X.property Y.property Z.property).symm

end
end DedekindZetaZeroFree.NormalizedProbe.TripleMellin
