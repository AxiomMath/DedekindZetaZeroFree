module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalUnitCharacter

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical

 def principalRealSeries (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) : ℝ :=
  if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-(2 : ℝ))

private theorem summable_principalRealSeries (F : Type) [Field F] [NumberField F] :
    Summable (principalRealSeries F) :=
  summable_ideal_inverse_power F 2 (by norm_num)

private theorem principalRealSeries_nonneg (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) : 0 ≤ principalRealSeries F I := by
  rw [principalRealSeries]
  split
  · norm_num
  · positivity

private theorem tsum_principalRealSeries_ge_one (F : Type) [Field F] [NumberField F] :
    1 ≤ ∑' I : Ideal (𝓞 F), principalRealSeries F I := by
  have h := (summable_principalRealSeries F).sum_le_tsum ({⊤} : Finset (Ideal (𝓞 F)))
    (fun i _ => principalRealSeries_nonneg F i)
  have h1 : ∑ i ∈ ({⊤} : Finset (Ideal (𝓞 F))), principalRealSeries F i = 1 := by
    simp [principalRealSeries, Ideal.absNorm_top]
  linarith [h, h1]

private theorem principalUnit_term_eq (F : Type) [Field F] [NumberField F]
    (I : Ideal (𝓞 F)) :
    principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-(2 : ℂ))
      = (principalRealSeries F I : ℂ) := by
  rw [principalRealSeries]
  by_cases hI : I = ⊥
  · subst hI
    rw [principalUnitRayCharacter_bot]
    simp
  · rw [principalUnitRayCharacter_apply]
    simp only [hI, if_false, if_neg hI, one_mul]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm I))]
    norm_num

private theorem idealHeckeL_principalUnit_two_eq (F : Type) [Field F] [NumberField F] :
    idealHeckeL (principalUnitRayCharacter F) (2 : ℂ)
      = ((∑' I : Ideal (𝓞 F), principalRealSeries F I : ℝ) : ℂ) := by
  unfold idealHeckeL
  rw [show (fun I : Ideal (𝓞 F) =>
      principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-(2 : ℂ)))
      = fun I => (principalRealSeries F I : ℂ) from funext (fun I => principalUnit_term_eq F I)]
  exact (Complex.ofReal_tsum (principalRealSeries F)).symm

private theorem heckeCompletionFactor_top_two_ne_zero (F : Type) [Field F] [NumberField F] :
    heckeCompletionFactor F ⊤ (2 : ℂ) ≠ 0 := by
  rw [heckeCompletionFactor, Ideal.absNorm_top, Nat.cast_one, mul_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
  · rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    exact Int.cast_ne_zero.mpr (abs_ne_zero.mpr (NumberField.discr_ne_zero F))
  · rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num : (-(2 : ℂ)) ≠ 0)).mpr
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · intro h
      rw [Complex.Gamma_eq_zero_iff] at h
      obtain ⟨m, hm⟩ := h
      have hm' : (2 : ℝ) = -(m : ℝ) := by exact_mod_cast hm
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith

theorem principalUnitRayCharacter_summable_two
    (F : Type) [Field F] [NumberField F] :
    Summable (fun I : Ideal (𝓞 F) =>
      principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-(2 : ℂ))) := by
  have h : Summable (fun I : Ideal (𝓞 F) => (principalRealSeries F I : ℂ)) :=
    Complex.summable_ofReal.mpr (summable_principalRealSeries F)
  exact h.congr (fun I => (principalUnit_term_eq F I).symm)

theorem idealHeckeL_principalUnit_two_real_pos
    (F : Type) [Field F] [NumberField F] :
    (idealHeckeL (principalUnitRayCharacter F) (2 : ℂ)).im = 0 ∧
      0 < (idealHeckeL (principalUnitRayCharacter F) (2 : ℂ)).re := by
  rw [idealHeckeL_principalUnit_two_eq F]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  exact lt_of_lt_of_le zero_lt_one (tsum_principalRealSeries_ge_one F)

theorem principalUnitHeckeWitness_Lambda_two_ne_zero
    (F : Type) [Field F] [NumberField F]
    (p : PrincipalHeckeWitness (principalUnitRayCharacter F)) :
    p.Λ (2 : ℂ) ≠ 0 := by
  have hs : HasSum (fun I : Ideal (𝓞 F) =>
      principalUnitRayCharacter F I * (Ideal.absNorm I : ℂ) ^ (-(2 : ℂ)))
      (idealHeckeL (principalUnitRayCharacter F) (2 : ℂ)) :=
    (principalUnitRayCharacter_summable_two F).hasSum
  have h := p.hasSum (2 : ℂ) (by norm_num)
  have huniq := HasSum.unique h (hs.mul_left (heckeCompletionFactor F ⊤ (2 : ℂ)))
  rw [huniq]
  refine mul_ne_zero (heckeCompletionFactor_top_two_ne_zero F) ?_
  intro hzero
  have := (idealHeckeL_principalUnit_two_real_pos F).2
  rw [hzero] at this
  simp at this

theorem principalUnitHeckeWitness_U_two_ne_zero
    (F : Type) [Field F] [NumberField F]
    (p : PrincipalHeckeWitness (principalUnitRayCharacter F)) :
    p.U (2 : ℂ) ≠ 0 := by
  have h := p.poleClearing (2 : ℂ) (by norm_num) (by norm_num)
  rw [h]
  refine mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) ?_
  exact principalUnitHeckeWitness_Lambda_two_ne_zero F p

end

end DedekindZetaZeroFree.LargeSieve
