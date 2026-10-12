module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.IdealEuler

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}

noncomputable def idealHeckeSummandHom
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ) :
    Ideal (𝓞 F) →*₀ ℂ where
  toFun I := η I * (Ideal.absNorm I : ℂ) ^ (-s)
  map_zero' := by
    show η (⊥ : Ideal (𝓞 F)) * (Ideal.absNorm (⊥ : Ideal (𝓞 F)) : ℂ) ^ (-s) = 0
    rw [(η.eq_zero_iff' ⊥).mpr (Or.inl rfl), zero_mul]
  map_one' := by
    rw [Ideal.one_eq_top, η.map_top', Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, mul_one]
  map_mul' I J := by
    rw [η.map_mul' I J, map_mul Ideal.absNorm I J, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring

theorem idealHeckeSummandHom_apply
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ) (I : Ideal (𝓞 F)) :
    idealHeckeSummandHom η s I = η I * (Ideal.absNorm I : ℂ) ^ (-s) := rfl

theorem idealHeckeSummandHom_bot
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ) :
    idealHeckeSummandHom η s ⊥ = 0 :=
  map_zero _

theorem idealHeckeSummandHom_top
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ) :
    idealHeckeSummandHom η s ⊤ = 1 := by
  rw [← Ideal.one_eq_top]
  exact map_one _

theorem summable_norm_idealHeckeSummand
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ)
    (hf : f ≠ ⊥) (hη : ∀ I, ‖η I‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun I => ‖idealHeckeSummandHom η s I‖) := by
  have hs0 : s.re ≠ 0 := by linarith

  have hsum : Summable (fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-s.re)) := by
    have hif : (fun I : Ideal (𝓞 F) =>
          if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-s.re))
        = fun I => (Ideal.absNorm I : ℝ) ^ (-s.re) := by
      funext I
      by_cases h : I = ⊥
      · rw [if_pos h, h, Ideal.absNorm_bot, Nat.cast_zero,
          Real.zero_rpow (neg_ne_zero.mpr hs0)]
      · rw [if_neg h]
    rw [← hif]
    exact summable_ideal_inverse_power F s.re hs
  refine Summable.of_nonneg_of_le (fun I => norm_nonneg _) (fun I => ?_) hsum
  by_cases hI : I = ⊥
  · rw [hI, idealHeckeSummandHom_bot, norm_zero, Ideal.absNorm_bot, Nat.cast_zero,
      Real.zero_rpow (neg_ne_zero.mpr hs0)]
  · rw [idealHeckeSummandHom_apply, norm_mul]
    have hpos : (0 : ℝ) < (Ideal.absNorm I : ℝ) := by
      have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero h0
    have hnorm : ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ = (Ideal.absNorm I : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos (-s),
        Complex.neg_re]
    rw [hnorm]
    calc ‖η I‖ * (Ideal.absNorm I : ℝ) ^ (-s.re)
        ≤ 1 * (Ideal.absNorm I : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hη I) (Real.rpow_nonneg hpos.le _)
      _ = (Ideal.absNorm I : ℝ) ^ (-s.re) := one_mul _

theorem summable_idealHeckeSummand
    (η : DedekindZetaZeroFree.RayClassCharacter F f) (s : ℂ)
    (hf : f ≠ ⊥) (hη : ∀ I, ‖η I‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun I => η I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  have h : Summable (fun I : Ideal (𝓞 F) => ‖η I * (Ideal.absNorm I : ℂ) ^ (-s)‖) := by
    simpa only [idealHeckeSummandHom_apply] using
      summable_norm_idealHeckeSummand η s hf hη hs
  exact Summable.of_norm h

end DedekindZetaZeroFree.LargeSieve.IdealEuler
