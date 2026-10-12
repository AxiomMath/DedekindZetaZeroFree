module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.CRTRawLocalPhaseAlgebra
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem uniformizer_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : uniformizer C p ≠ 0 := by
  change algebraMap F (LocalField p) (generator C p : F) ≠ 0
  apply (map_ne_zero (algebraMap F (LocalField p))).2
  exact_mod_cast (generator_generates C p).1

theorem phase_difference {K : Type*} [Field K]
    (π S U H d d' v v' r q b : K) (t k J : ℕ)
    (hπ : π ≠ 0) (hS : S ≠ 0) (hU : U ≠ 0)
    (hd : d - d' = π ^ k * r) (hv : v - v' = π ^ t * q)
    (hc : H * π ^ J - U * π ^ t * d = π ^ k * b) :
    ((H * π ^ J - U * π ^ t * d) * v) / (S * U * π ^ (k + t)) -
      ((H * π ^ J - U * π ^ t * d') * v') / (S * U * π ^ (k + t)) =
      (S⁻¹ * U⁻¹) * b * q - S⁻¹ * r * v' := by
  have hd' : d' = d - π ^ k * r := by linear_combination -hd
  have hv' : v = v' + π ^ t * q := by linear_combination hv
  rw [hd', hv', pow_add]
  field_simp [hπ, hS, hU]
  linear_combination π ^ t * q * hc

end DedekindZetaZeroFree.CRTRawLocalPhaseAlgebra

end
