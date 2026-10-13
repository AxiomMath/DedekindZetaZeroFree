module

public import DedekindZetaZeroFree.LFunctions.Dedekind.AbelianContinuation
public import DedekindZetaZeroFree.LFunctions.Dedekind.TwelfthRootPointwiseNonvanishing
public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.PrincipalNonvanishing

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem mu12_continuation_ne_zero (F : Type) [Field F] [NumberField F]
    (htc : NumberField.IsTotallyComplex F) (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 12) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) ∧
      ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  obtain ⟨f, hf, hmatch⟩ := DedekindZetaZeroFree.dedekindZeta_continuation F
  refine ⟨f, hf, hmatch, ?_⟩
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
  have hLf : ∀ s : ℂ, 0 < s.re → s ≠ 1 → P.L s = f s := by
    clear hprim
    revert η hη P
    rw [hmod]
    intro η hη P
    exact PrincipalPointwise.principal_top_continuation_eq F η hη P f hf hmatch
  intro s hs hs1 hfs
  apply comparisonPrincipalIncompleteL_ne_zero F S η hη P s hs hs1
  simp [comparisonPrincipalIncompleteL, hLf s (by linarith) hs1, hfs]

end DedekindZetaZeroFree.Quantitative
