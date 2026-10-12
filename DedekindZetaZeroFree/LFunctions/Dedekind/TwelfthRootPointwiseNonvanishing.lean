module

public import DedekindZetaZeroFree.LFunctions.Dedekind.FiniteEulerRestoration
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalIncompleteLFunction

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalMu12Pointwise

theorem trivial_modulus_arithmetic_data_exists
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    ∃ S : SArithmeticData F, S.zeta12 = ζ ∧ S.modulus = ⊤ := by
  classical
  have h6 : (Ideal.span {(6 : 𝓞 F)} : Ideal (𝓞 F)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show (6 : ℚ) ≠ 0 by norm_num)
  refine ⟨{
    zeta12 := ζ
    primitive_zeta12 := hζ
    Sf := (Ideal.finite_factors h6).toFinset
    S₀ := ∅
    bad_subset := Finset.empty_subset _
    modulus := ⊤
    modulus_ne_zero := ?_
    above_six := ?_
    modulus_support := ?_ }, rfl, rfl⟩
  · intro h
    have hmem : (1 : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := by rw [← h]; exact Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp hmem)
  · intro v hv
    rw [Set.Finite.mem_toFinset]
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_iff_mem v.asIdeal |>.mpr hv)
  · intro v hv
    exact absurd (top_le_iff.mp hv) v.isPrime.ne_top

end DedekindZetaZeroFree.PrincipalMu12Pointwise

end

section

namespace DedekindZetaZeroFree

theorem principal_mu12_continuation_ne_zero
    (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 12)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) :
    ∀ s : ℂ, 5999 / 6000 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := hmu
  obtain ⟨S, _, hmod⟩ :=
    PrincipalMu12Pointwise.trivial_modulus_arithmetic_data_exists F ζ hζ
  have hchar : ∃ η : RayClassCharacter F S.modulus,
      η.IsPrincipal ∧ η.IsPrimitive := by
    rw [hmod]
    exact PrincipalMu12Pointwise.principal_primitive_top_character_exists F
  obtain ⟨η, hη, hprim⟩ := hchar
  obtain ⟨P⟩ := principalRayHeckeData_exists F htc S.modulus
    S.modulus_ne_zero η hprim hη
  exact PrincipalPointwise.continuation_ne_zero_of_incomplete_ne_zero
    F S hmod η hη P f hf hmatch
    (principal_mellin_zero_free F S η hη P)

end DedekindZetaZeroFree

end
