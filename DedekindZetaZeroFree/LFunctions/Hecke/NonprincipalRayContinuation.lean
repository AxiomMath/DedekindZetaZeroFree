module

public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation
public import DedekindZetaZeroFree.LFunctions.Hecke.RayContinuationData

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

theorem nonprincipalRayHeckeData_exists
     (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (hprim : η.IsPrimitive) (hnp : ¬ η.IsPrincipal) :
    Nonempty (NonprincipalRayHeckeData F 𝔪 η) := by
  obtain ⟨Λ, Λ', W, hΛ, hΛ', hW, hser, hser', hrefl, hord⟩ :=
    (DedekindZetaZeroFree.Hecke.heckeFunctionalEquation F hF 𝔪 hm η hprim).1 hnp
  refine ⟨fun s => if 0 < s.re then Λ s / heckeCompletionFactor F 𝔪 s else 0,
    Λ, Λ', W, ?_, hΛ, hΛ', ?_, ?_, hser', hW, hrefl, hord⟩
  ·
    refine DifferentiableOn.congr (hΛ.differentiableOn.mul
      (differentiableOn_inv_heckeCompletionFactor F 𝔪 hm)) ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp only [if_pos hs, div_eq_mul_inv, Pi.mul_apply]
  ·
    intro s hs
    have hs0 : 0 < s.re := lt_trans zero_lt_one hs
    show HasSum (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s))
      (if 0 < s.re then Λ s / heckeCompletionFactor F 𝔪 s else 0)
    rw [if_pos hs0]
    exact hasSum_div_heckeCompletionFactor F 𝔪 hm s hs0
      (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) (Λ s) (hser s hs)
  ·
    intro s hs
    show Λ s = heckeCompletionFactor F 𝔪 s *
      (if 0 < s.re then Λ s / heckeCompletionFactor F 𝔪 s else 0)
    rw [if_pos hs, mul_div_cancel₀]
    exact heckeCompletionFactor_ne_zero F 𝔪 hm s hs

def nonprincipalRayHeckeData
     (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (hprim : η.IsPrimitive) (hnp : ¬ η.IsPrincipal) :
    NonprincipalRayHeckeData F 𝔪 η :=
  Classical.choice (nonprincipalRayHeckeData_exists F hF 𝔪 hm η hprim hnp)

end

end DedekindZetaZeroFree
