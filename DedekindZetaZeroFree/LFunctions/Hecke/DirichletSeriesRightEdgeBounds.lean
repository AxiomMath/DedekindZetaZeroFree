module

public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealNormAbsoluteSummability
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarity

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

private theorem right_edge_term_bound (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) (a : Ideal (𝓞 F) → ℂ)
    (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1) (I : Ideal (𝓞 F)) :
    ‖a I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤ idealAbsoluteWeight F σ I := by
  by_cases hI : I = ⊥
  · subst I
    simp [ha0, idealAbsoluteWeight]
  · have hn : 0 < Ideal.absNorm I :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hnR : 0 < (Ideal.absNorm I : ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast hn
    rw [idealAbsoluteWeight, if_neg hI, norm_mul]
    have hp : ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ =
        (Ideal.absNorm I : ℝ) ^ (-s.re) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnR (-s)
    rw [hp]
    calc
      ‖a I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm I : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (ha I) (Real.rpow_nonneg hnR.le _)
      _ ≤ (Ideal.absNorm I : ℝ) ^ (-σ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)

private theorem right_edge_of_bound (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 1 < σ) (s : ℂ) (hs : σ ≤ s.re)
    (a : Ideal (𝓞 F) → ℂ) (ha0 : a ⊥ = 0) (ha : ∀ I, ‖a I‖ ≤ 1) :
    Summable (fun I : Ideal (𝓞 F) => a I * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      ‖∑' I : Ideal (𝓞 F), a I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤
        idealAbsoluteSum F σ := by
  have hw := (idealAbsoluteSum_converges F σ hσ).1
  have hb := right_edge_term_bound F σ s hs a ha0 ha
  have hf := hw.of_norm_bounded hb
  refine ⟨hf, (norm_tsum_le_tsum_norm hf.norm).trans ?_⟩
  exact hf.norm.tsum_le_tsum hb hw

theorem heckeDirichlet_right_edge (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 1 < σ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (s : ℂ) (hs : σ ≤ s.re) :
    Summable (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      ‖∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤
        idealAbsoluteSum F σ := by
  apply right_edge_of_bound F σ hσ s hs (fun I => η I)
  · exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  · exact RayUnitary.ray_character_norm_le_one F 𝔪 h𝔪 η

theorem conjugateHeckeDirichlet_right_edge (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 1 < σ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (s : ℂ) (hs : σ ≤ s.re) :
    Summable (fun I : Ideal (𝓞 F) =>
      (starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s)) ∧
      ‖∑' I : Ideal (𝓞 F),
        (starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s)‖ ≤
        idealAbsoluteSum F σ := by
  apply right_edge_of_bound F σ hσ s hs (fun I => (starRingEnd ℂ) (η I))
  · rw [show η ⊥ = 0 from (η.eq_zero_iff' ⊥).mpr (Or.inl rfl), map_zero]
  · intro I
    simpa using RayUnitary.ray_character_norm_le_one F 𝔪 h𝔪 η I

theorem heckeDirichlet_hasSum_norm_le (F : Type) [Field F] [NumberField F]
    (σ : ℝ) (hσ : 1 < σ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (η : RayClassCharacter F 𝔪) (s : ℂ) (hs : σ ≤ s.re) (v : ℂ)
    (hv : HasSum (fun I : Ideal (𝓞 F) => η I * (Ideal.absNorm I : ℂ) ^ (-s)) v) :
    ‖v‖ ≤ idealAbsoluteSum F σ := by
  rw [← hv.tsum_eq]
  exact (heckeDirichlet_right_edge F σ hσ 𝔪 h𝔪 η s hs).2

end

end DedekindZetaZeroFree
