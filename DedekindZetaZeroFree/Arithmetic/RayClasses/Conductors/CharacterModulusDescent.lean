module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.ModulusReductionKernel
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdealCharacterFromGroup

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem initial_ray_one_step_descent
    (F : Type) [Field F] [NumberField F]
    (m f : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hmf : m ≤ f)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (htriv : ∀ a : 𝓞 F, a ≠ 0 → a - 1 ∈ f →
      (∀ φ : F →+* ℝ, 0 < φ (a : F)) →
      Ideal.span {a} ⊔ m = ⊤ → η (Ideal.span {a}) = 1) :
    ∃ θ : DedekindZetaZeroFree.RayClassCharacter F f,
      ∀ I : Ideal (𝓞 F), η I = if I = ⊥ ∨ I ⊔ m ≠ ⊤ then 0 else θ I := by
  classical
  let χ : ClassFieldTheory.RayClassGroup (RayBridge.fullModulus m hm) →* ℂˣ :=
    RayBridge.descendedCharacter m hm η
  have hker : (RayBridge.modulusReduction m hm f hf hmf).ker ≤ χ.ker := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc ⊢
    obtain ⟨a, b, ha, hb, hca, hcb, haf, hbf, hpa, hpb, hc_eq⟩ :=
      RayBridge.modulusReduction_kernel m hm f hf hmf c hc
    rw [hc_eq, map_mul, map_inv]
    have h1 : (χ (RayBridge.idealClass m hm (Ideal.span {a})
        (mt Ideal.span_singleton_eq_bot.mp ha) hca) : ℂ) = 1 := by
      rw [RayBridge.descendedCharacter_apply_idealClass m hm η (Ideal.span {a})
        (mt Ideal.span_singleton_eq_bot.mp ha) hca, htriv a ha haf hpa hca]
    have h2 : (χ (RayBridge.idealClass m hm (Ideal.span {b})
        (mt Ideal.span_singleton_eq_bot.mp hb) hcb) : ℂ) = 1 := by
      rw [RayBridge.descendedCharacter_apply_idealClass m hm η (Ideal.span {b})
        (mt Ideal.span_singleton_eq_bot.mp hb) hcb, htriv b hb hbf hpb hcb]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    rw [h1, h2]
    simp
  have hsurj : Function.Surjective (RayBridge.modulusReduction m hm f hf hmf) :=
    RayBridge.modulusReduction_surjective m hm f hf hmf
  let χf : ClassFieldTheory.RayClassGroup (RayBridge.fullModulus f hf) →* ℂˣ :=
    (RayBridge.modulusReduction m hm f hf hmf).liftOfSurjective hsurj ⟨χ, hker⟩
  have hχf : ∀ x : ClassFieldTheory.RayClassGroup (RayBridge.fullModulus m hm),
      χf (RayBridge.modulusReduction m hm f hf hmf x) = χ x := by
    intro x
    exact MonoidHom.liftOfRightInverse_comp_apply
      (RayBridge.modulusReduction m hm f hf hmf) (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨χ, hker⟩ x
  refine ⟨RayBridge.characterFromRayGroup f hf χf, ?_⟩
  intro I
  by_cases hbad : I = ⊥ ∨ I ⊔ m ≠ ⊤
  · rw [if_pos hbad]
    exact (η.eq_zero_iff' I).mpr hbad
  · rw [if_neg hbad]
    push Not at hbad
    obtain ⟨hI, hcop⟩ := hbad
    have hcopf : I ⊔ f = ⊤ :=
      top_unique (le_trans (le_of_eq hcop.symm) (sup_le_sup_left hmf I))
    have hθ : (RayBridge.characterFromRayGroup f hf χf) I =
        (χf (RayBridge.idealClass f hf I hI hcopf) : ℂ) :=
      RayBridge.characterFromRayGroup_apply f hf χf I hI hcopf
    have hred : RayBridge.modulusReduction m hm f hf hmf
          (RayBridge.idealClass m hm I hI hcop) =
        RayBridge.idealClass f hf I hI hcopf := by
      rw [RayBridge.modulusReduction_apply_idealClass m hm f hf hmf I hI hcop]
    have hχI : (χf (RayBridge.idealClass f hf I hI hcopf) : ℂ) = η I := by
      rw [← hred, hχf]
      exact RayBridge.descendedCharacter_apply_idealClass m hm η I hI hcop
    rw [hθ, hχI]

end DedekindZetaZeroFree.LargeSieve
