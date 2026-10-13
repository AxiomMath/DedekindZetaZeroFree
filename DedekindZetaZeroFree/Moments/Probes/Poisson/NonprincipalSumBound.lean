module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySumBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.OmittedProbeBound

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem omittedSum_bound (D : FixedData S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) :=
  RawOmittedRowsAssembly31.rawOmittedSum_bound D

end DedekindZetaZeroFree.Quantitative.OmittedProbeBound
