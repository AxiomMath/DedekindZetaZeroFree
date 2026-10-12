module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.FundamentalDomainScaling
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.FiniteAdelicCoordinateCharts

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.FiniteOscillatoryStabilization

theorem globalDifferentExponent_eq_localDifferentExponent
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    PoissonS.differentExponent F v = (localDifferentExponent F v : ℤ) := by

  have hmass := FiniteHaarCharts.localMass_eq_inv_sqrt F v
  rw [FiniteHaarCharts.localMass, localNormalizedHaar_integerRing_toReal,
    localHalfDifferentFactor_eq_inv_sqrt, localDifferentNorm, Nat.cast_pow] at hmass
  have hs : Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ localDifferentExponent F v) =
      Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^ DifferentMass.exponent F v) := by
    simpa only [one_div, inv_inj] using hmass
  have hp := (Real.sqrt_inj (by positivity) (by positivity)).mp hs
  have hexponent : localDifferentExponent F v = DifferentMass.exponent F v :=
    (pow_right_strictMono₀
      (by exact_mod_cast DifferentMass.one_lt_absNorm F v)).injective hp
  rw [hexponent, PoissonS.differentExponent,
    FractionalIdeal.count_coe F v differentIdeal_ne_bot,
    Ideal.count_associates_factors_eq differentIdeal_ne_bot v.isPrime v.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity differentIdeal_ne_bot]
  rfl

end DedekindZetaZeroFree.FiniteOscillatoryStabilization

end
