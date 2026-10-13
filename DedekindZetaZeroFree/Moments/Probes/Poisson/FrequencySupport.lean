module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.InitialFrequencySupport

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem initial_all_frequency_partition (D : FixedData S η) (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = ∑' u : D.Row, PoissonFrequencyDecomposition.rowIntegral D u Z +
      PoissonFrequencyDecomposition.omittedSum D Z :=
  (PoissonFrequencyDecomposition.Iscale_eq_rows_add_omitted D Z hZ).2.2.2.2.2.2.2.2

end

end DedekindZetaZeroFree.Quantitative.InitialFrequencySupport
