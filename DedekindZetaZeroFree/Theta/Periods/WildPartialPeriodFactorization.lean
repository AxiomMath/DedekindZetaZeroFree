module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts

@[expose] public section

noncomputable section

open scoped NumberField

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildPartialPeriodFactorization

open KPLocalExceptionalConstruction

variable (F : Type) [Field F] [NumberField F]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def wildPlaces : Set (HeightOneSpectrum (𝓞 F)) :=
  {q | (3 : 𝓞 F) ∈ q.asIdeal}

theorem wildPlaces_finite : (wildPlaces F).Finite := by
  have h3 : (3 : 𝓞 F) ≠ 0 := by norm_num
  simpa only [wildPlaces, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using
    (Ideal.finite_factors (I := Ideal.span {(3 : 𝓞 F)})
      (by
        intro h
        apply h3
        exact Ideal.span_singleton_eq_bot.mp h))

abbrev WildPlace := ↥(wildPlaces F)

instance wildPlaceFintype : Fintype (WildPlace F) :=
  (wildPlaces_finite F).fintype

end DedekindZetaZeroFree.KPWildPartialPeriodFactorization

end
