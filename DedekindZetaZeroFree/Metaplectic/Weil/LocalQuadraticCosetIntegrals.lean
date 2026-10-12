module

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.AdmissibleQuadraticBalls

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

 local instance quadraticCosetCompletionMeasurable
    (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

 local instance quadraticCosetCompletionBorel
    (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem localQuadraticPhase_coset_integral
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (z y : v.adicCompletion F) :
    IntegrableOn
      (fun x : v.adicCompletion F =>
        (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2 - y * x) : ℂ))
      {x | x - z ∈ finiteCompletionBall F v m} (localNormalizedHaar F v) ∧
    (∫ x in {x | x - z ∈ finiteCompletionBall F v m},
      (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2 - y * x) : ℂ)
        ∂(localNormalizedHaar F v)) =
      if 2 * (a : v.adicCompletion F) * z - y ∈
          localFiniteAnnihilator F v (finiteCompletionBall F v m) then
        ((localNormalizedHaar F v
          (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal : ℂ) *
          (localFiniteCharacter F v
            ((a : v.adicCompletion F) * z ^ 2 - y * z) : ℂ)
      else 0 := by
  let U := finiteCompletionBall F v m
  let S : Set (v.adicCompletion F) := {x | x - z ∈ U}
  let f : v.adicCompletion F → ℂ := fun x =>
    (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2 - y * x) : ℂ)
  have hS : IsCompact S := isCompact_finiteCompletionBall_coset F v z m
  have hf : Continuous f := continuous_subtype_val.comp
    ((continuous_localFiniteCharacter F v).comp (by fun_prop))
  refine ⟨hf.continuousOn.integrableOn_compact hS, ?_⟩
  let χ : AddChar (v.adicCompletion F) Circle :=
    { toFun := fun h => localFiniteCharacter F v ((2 * (a : v.adicCompletion F) * z - y) * h)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro h k
        simp only [mul_add, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    (continuous_localFiniteCharacter F v).comp (continuous_const.mul continuous_id)
  have horth := (compactSubgroup_character_integral
    (localNormalizedHaar F v) U (isCompact_finiteCompletionBall F v m) χ hχ).2
  have htrivial : (∀ h ∈ U, χ h = 1) ↔
      2 * (a : v.adicCompletion F) * z - y ∈ localFiniteAnnihilator F v U := by
    simp only [mem_localFiniteAnnihilator]
    constructor <;> intro h u hu <;> simpa [χ, mul_comm] using h u hu
  have hphase (h : v.adicCompletion F) (hh : h ∈ U) :
      f (z + h) = f z * (χ h : ℂ) := by
    have hexp : (a : v.adicCompletion F) * (z + h) ^ 2 - y * (z + h) =
        ((a : v.adicCompletion F) * z ^ 2 - y * z) +
          (a : v.adicCompletion F) * h ^ 2 + (2 * (a : v.adicCompletion F) * z - y) * h := by ring
    simp [f, hexp, AddChar.map_add_eq_mul, hq h hh, χ]
  have htranslate : (fun x => S.indicator f (z + x)) =
      (fun x => f z * (U : Set (v.adicCompletion F)).indicator (fun h => (χ h : ℂ)) x) := by
    funext x
    have hmem : z + x ∈ S ↔ x ∈ U := by simp [S]
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
      exact hphase x hx
    · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem hx, mul_zero]
  change (∫ x in S, f x ∂(localNormalizedHaar F v)) = _
  rw [← integral_indicator hS.measurableSet,
    ← integral_add_left_eq_self (μ := localNormalizedHaar F v) (S.indicator f) z,
    htranslate, integral_const_mul,
    integral_indicator (isCompact_finiteCompletionBall F v m).measurableSet, horth]
  by_cases ht : 2 * (a : v.adicCompletion F) * z - y ∈ localFiniteAnnihilator F v U
  · rw [if_pos (htrivial.mpr ht), if_pos ht]
    exact mul_comm _ _
  · rw [if_neg (mt htrivial.mp ht), if_neg ht, mul_zero]

end DedekindZetaZeroFree

end
