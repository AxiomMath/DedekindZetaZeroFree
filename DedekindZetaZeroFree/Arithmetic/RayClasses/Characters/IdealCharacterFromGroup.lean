module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralPrincipalAndPrimeClasses

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def characterFromRayGroup (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ψ : ClassFieldTheory.RayClassGroup (fullModulus m hm) →* ℂˣ) :
    DedekindZetaZeroFree.RayClassCharacter F m where
  toFun I := if hI : I = ⊥ then 0
    else if hcop : I ⊔ m = ⊤ then
      (ψ (idealClass m hm I hI hcop) : ℂ)
    else 0
  map_mul' := by
    intro I J
    by_cases hI : I = ⊥
    · subst hI
      rw [Ideal.bot_mul]
      simp
    by_cases hJ : J = ⊥
    · subst hJ
      rw [Ideal.mul_bot]
      simp
    have hIJ : I * J ≠ ⊥ := ideal_mul_ne_bot I J hI hJ
    by_cases hIJm : (I * J) ⊔ m = ⊤
    · have hIm : I ⊔ m = ⊤ := by
        by_contra h
        have hle : (I * J) ⊔ m ≤ I ⊔ m :=
          sup_le (Ideal.mul_le_left.trans le_sup_left) le_sup_right
        rw [hIJm] at hle
        exact h (top_le_iff.mp hle)
      have hJm : J ⊔ m = ⊤ := by
        by_contra h
        have hle : (I * J) ⊔ m ≤ J ⊔ m :=
          sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right
        rw [hIJm] at hle
        exact h (top_le_iff.mp hle)
      rw [dif_neg hIJ, dif_pos hIJm, dif_neg hI, dif_pos hIm, dif_neg hJ, dif_pos hJm,
        idealClass_mul m hm I J hI hJ hIm hJm hIJ hIJm, map_mul]
      exact Units.val_mul _ _
    · rw [dif_neg hIJ, dif_neg hIJm]
      by_cases hIm : I ⊔ m = ⊤
      · rw [dif_neg hI, dif_pos hIm, dif_neg hJ]
        have hJm : J ⊔ m ≠ ⊤ := fun h => hIJm (ideal_mul_coprime m I J hIm h)
        rw [dif_neg hJm]
        simp
      · rw [dif_neg hI, dif_neg hIm]
        simp
  map_top' := by
    show (if h : (⊤ : Ideal (𝓞 F)) = ⊥ then 0
      else if hcop : ⊤ ⊔ m = ⊤ then (ψ (idealClass m hm ⊤ h hcop) : ℂ) else 0) = 1
    rw [dif_neg (top_ne_bot), dif_pos (by simp)]
    rw [idealClass_top]
    simp
  eq_zero_iff' := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      simp
    · by_cases hcop : I ⊔ m = ⊤
      · rw [dif_neg hI, dif_pos hcop]
        constructor
        · intro h
          exact absurd h (Units.ne_zero (ψ (idealClass m hm I hI hcop)))
        · intro h
          rcases h with h | h
          · exact absurd h hI
          · exact absurd hcop h
      · rw [dif_neg hI, dif_neg hcop]
        simp [hI, hcop]
  map_span' := by
    intro α hα hcong hpos
    have hne : Ideal.span {α} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hα
    have hcop : Ideal.span {α} ⊔ m = ⊤ := integral_span_coprime m α hcong
    rw [dif_neg hne, dif_pos hcop]
    rw [idealClass_integral_principal m hm α hα hcong hpos]
    simp

theorem characterFromRayGroup_apply (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (ψ : ClassFieldTheory.RayClassGroup (fullModulus m hm) →* ℂˣ)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    (characterFromRayGroup m hm ψ) I =
      (ψ (idealClass m hm I hI hcop) : ℂ) := by
  show (if hI' : I = ⊥ then 0
    else if hcop' : I ⊔ m = ⊤ then (ψ (idealClass m hm I hI' hcop') : ℂ) else 0) = _
  rw [dif_neg hI, dif_pos hcop]

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
