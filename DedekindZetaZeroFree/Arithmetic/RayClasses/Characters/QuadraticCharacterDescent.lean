module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField

variable {F : Type} [Field F] [NumberField F]

theorem descendedCharacter_square (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) :
    ∀ x : ClassFieldTheory.RayClassGroup (fullModulus f hf),
      (descendedCharacter f hf η) x ^ 2 = 1 := by

  let ψ := descendedCharacter f hf η
  have hpow : ψ ^ 3 = ψ := by
    have huniq := descendedCharacter_unique f hf η (ψ ^ 3) (by
      intro I hI hcop
      have hx : ((ψ (idealClass f hf I hI hcop)) : ℂ) = η I := by
        simp [ψ]
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hx, hq I])
    rw [huniq]
  intro x
  have hx : (ψ x) ^ 3 = ψ x := by
    have := DFunLike.congr_fun hpow x
    rwa [MonoidHom.pow_apply] at this
  have hcancel : (ψ x) ^ 2 * ψ x = 1 * ψ x := by
    rw [one_mul, ← pow_succ]
    exact hx
  exact mul_right_cancel hcancel

theorem descendedCharacter_ne_one (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hn : ¬η.IsPrincipal) :
    descendedCharacter f hf η ≠ 1 := by
  intro h
  apply hn
  intro I hI hcop
  have hx := descendedCharacter_apply_idealClass f hf η I hI hcop
  rw [h] at hx
  simpa using hx.symm

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
