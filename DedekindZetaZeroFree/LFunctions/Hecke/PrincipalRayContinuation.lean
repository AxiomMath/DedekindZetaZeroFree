module

public import DedekindZetaZeroFree.LFunctions.Hecke.FunctionalEquation
public import DedekindZetaZeroFree.LFunctions.Hecke.RayContinuationData

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

theorem principalRayHeckeData_exists
     (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (hprim : η.IsPrimitive) (hp : η.IsPrincipal) :
    Nonempty (PrincipalRayHeckeData F 𝔪 η) := by
  obtain ⟨Λ₀, E₀, hΛ_holo, hE_entire, hseries, hreflection, hE_eq, horder⟩ :=
    (DedekindZetaZeroFree.Hecke.heckeFunctionalEquation F hF 𝔪 hm η hprim).2 hp

  let R : ℂ → ℂ := fun s => E₀ s / (s * heckeCompletionFactor F 𝔪 s)

  let L : ℂ → ℂ := fun s => R s / (s - 1)

  have hL_eq : ∀ s : ℂ, 0 < s.re → s ≠ 1 →
      L s = Λ₀ s / heckeCompletionFactor F 𝔪 s := by
    intro s hs hs1
    have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
    have hAne : heckeCompletionFactor F 𝔪 s ≠ 0 :=
      heckeCompletionFactor_ne_zero F 𝔪 hm s hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hE := hE_eq s hs0 hs1
    simp only [L, R]
    rw [hE]
    field_simp
  refine ⟨L, R, Λ₀, E₀, ?_, ?_, hΛ_holo, hE_entire, ?_, ?_, ?_, ?_,
    hreflection, horder⟩
  ·
    have hR_holo : DifferentiableOn ℂ R {s : ℂ | 0 < s.re} := by
      have hden : DifferentiableOn ℂ (fun s : ℂ => s * heckeCompletionFactor F 𝔪 s)
          {s : ℂ | 0 < s.re} :=
        differentiableOn_id.mul (differentiableOn_heckeCompletionFactor F 𝔪 hm)
      have hden_ne : ∀ s ∈ {s : ℂ | 0 < s.re},
          s * heckeCompletionFactor F 𝔪 s ≠ 0 := by
        intro s hs
        exact mul_ne_zero (Complex.ne_zero_of_re_pos hs)
          (heckeCompletionFactor_ne_zero F 𝔪 hm s hs)
      exact (hE_entire.differentiableOn.mono (Set.subset_univ _)).div hden hden_ne
    have hR' : DifferentiableOn ℂ R {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
      hR_holo.mono (fun s hs => hs.1)
    have h1 : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
      differentiableOn_id.sub_const 1
    have h1ne : ∀ s ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1}, s - 1 ≠ 0 :=
      fun s hs => sub_ne_zero.mpr hs.2
    exact hR'.div h1 h1ne
  ·
    have hden : DifferentiableOn ℂ (fun s : ℂ => s * heckeCompletionFactor F 𝔪 s)
        {s : ℂ | 0 < s.re} :=
      differentiableOn_id.mul (differentiableOn_heckeCompletionFactor F 𝔪 hm)
    have hden_ne : ∀ s ∈ {s : ℂ | 0 < s.re},
        s * heckeCompletionFactor F 𝔪 s ≠ 0 := by
      intro s hs
      exact mul_ne_zero (Complex.ne_zero_of_re_pos hs)
        (heckeCompletionFactor_ne_zero F 𝔪 hm s hs)
    exact (hE_entire.differentiableOn.mono (Set.subset_univ _)).div hden hden_ne
  ·
    intro s hs
    have hs0 : 0 < s.re := zero_lt_one.trans hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have h := hasSum_div_heckeCompletionFactor F 𝔪 hm s hs0
      (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) (Λ₀ s)
      (by simpa only [heckeCompletionFactor] using hseries s hs)
    rw [hL_eq s hs0 hs1]
    simpa using h
  ·
    intro s hs hs1
    have hAne : heckeCompletionFactor F 𝔪 s ≠ 0 :=
      heckeCompletionFactor_ne_zero F 𝔪 hm s hs
    rw [hL_eq s hs hs1, mul_div_assoc', mul_div_cancel_left₀ (Λ₀ s) hAne]
  ·
    intro s hs hs1
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [L]
    rw [mul_div_assoc', mul_div_cancel_left₀ (R s) hs1']
  ·
    intro s hs
    have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
    have hAne : heckeCompletionFactor F 𝔪 s ≠ 0 :=
      heckeCompletionFactor_ne_zero F 𝔪 hm s hs
    have hden : s * heckeCompletionFactor F 𝔪 s ≠ 0 := mul_ne_zero hs0 hAne
    simp only [R]
    rw [mul_div_assoc', mul_div_cancel_left₀ (E₀ s) hden]

def principalRayHeckeData
     (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (hprim : η.IsPrimitive) (hp : η.IsPrincipal) :
    PrincipalRayHeckeData F 𝔪 η :=
  Classical.choice (principalRayHeckeData_exists F hF 𝔪 hm η hprim hp)

end

end DedekindZetaZeroFree
