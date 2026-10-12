module

public import DedekindZetaZeroFree.Arithmetic.Kummer.LocalNormCharacter

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLeastLocalExponent

noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem finiteExponent_isLeast (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsLeast (fun n : ℕ =>
      ClassFieldTheory.rayLocalHigherUnitGroup v n ≤
        (RMKummerLocalNormCharacter.lambda F h12 x v).ker)
      ((M F (RMKummerConductor.m F h12 x)
        (RMKummerConductor.m_ne_bot F h12 x)).finitePart v) := by
  have h := ClassFieldTheory.IsAbelianConductor.finiteExponent_isLeast_tensorNorm
    (K := F) (L := RMKummerConductor.E F h12 x)
    (c := M F (RMKummerConductor.m F h12 x) (RMKummerConductor.m_ne_bot F h12 x))
    (RMKummerConductor.isAbelianConductor F h12 x) v
  simpa only [RMKummerLocalNormCharacter.lambda_ker_eq_norm_range] using h

theorem finiteExponent_eq_ord (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M F (RMKummerConductor.m F h12 x)
      (RMKummerConductor.m_ne_bot F h12 x)).finitePart v =
      idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x) := by
  exact M_finitePart F (RMKummerConductor.m F h12 x) (RMKummerConductor.m_ne_bot F h12 x) v

theorem lambda_trivial_on_conductor_units (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ)
    (ht : t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v
      (idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x))) :
    RMKummerLocalNormCharacter.lambda F h12 x v t = 1 := by
  have hle := (finiteExponent_isLeast F h12 x v).1
  rw [finiteExponent_eq_ord F h12 x v] at hle
  exact MonoidHom.mem_ker.mp (hle ht)

theorem lambda_nontrivial_below_conductor (F : Type) [Field F] [NumberField F]
    (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (hk : k < idealPrimeExponent v.asIdeal (RMKummerConductor.m F h12 x)) :
    ∃ t : (v.adicCompletion F)ˣ,
      t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k ∧
        RMKummerLocalNormCharacter.lambda F h12 x v t ≠ 1 := by
  have hnot : ¬ (ClassFieldTheory.rayLocalHigherUnitGroup v k ≤
      (RMKummerLocalNormCharacter.lambda F h12 x v).ker) := by
    intro hh
    have h2 := (finiteExponent_isLeast F h12 x v).2 hh
    rw [finiteExponent_eq_ord F h12 x v] at h2
    exact absurd h2 (not_le.mpr hk)
  obtain ⟨t, ht, htk⟩ := Set.not_subset.mp hnot
  exact ⟨t, ht, htk⟩

theorem higherUnitGroup_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ClassFieldTheory.rayLocalHigherUnitGroup v 0 =
      (v.adicCompletionIntegers F).units :=
  ClassFieldTheory.rayLocalHigherUnitGroup_zero v

end
end DedekindZetaZeroFree.RMKummerLeastLocalExponent
