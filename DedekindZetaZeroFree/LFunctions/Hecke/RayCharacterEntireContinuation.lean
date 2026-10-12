module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
public import DedekindZetaZeroFree.LFunctions.Hecke.PartialRayZetaRegularization
public import DedekindZetaZeroFree.Analysis.FiniteCharacterPoleCancellation

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

theorem rayCharacterEntire
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m)
    (hχ : ¬ χ.IsPrincipal) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ s : ℂ, 1 < s.re →
        HasSum (fun I : Ideal (𝓞 K) =>
          χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s) := by
  classical

  obtain ⟨ψ, hψdesc, hψprinc⟩ := rayCharacterDescent K m hm χ
  have hψ : ψ ≠ 1 := fun h => hχ (hψprinc.mpr h)

  obtain ⟨ρ, F, hF, hpartial⟩ := partialRayZetaRegularization K m hm
  haveI : Fintype (RayIdealClass K m hm) := Fintype.ofFinite _

  obtain ⟨f, hfdiff, hfsum⟩ := finiteCharacterEntireAssembly (rayIdealClass K m hm)
    (fun I s => (Ideal.absNorm I : ℂ) ^ (-s)) ψ hψ ρ F hF (fun c s hs =>
      (hpartial c s hs).congr_fun fun a => by
        by_cases hp : rayIdealClass K m hm a = some c <;> simp [hp])
  refine ⟨f, hfdiff, fun s hs => ?_⟩

  refine (hfsum s hs).congr_fun fun I => ?_
  rw [hψdesc I]
  cases hq : rayIdealClass K m hm I with
  | none => rfl
  | some c => rfl

end DedekindZetaZeroFree.AbelianQuotient
