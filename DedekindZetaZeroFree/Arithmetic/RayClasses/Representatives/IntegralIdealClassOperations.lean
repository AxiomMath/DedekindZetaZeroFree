module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Moduli.IntegralNarrowCongruence

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.AbelianQuotient

@[simp] theorem rayIdealClass_top
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    rayIdealClass K m hm ⊤ = some 1 := by
  rw [rayIdealClass_eq_some K m hm ⊤ top_ne_bot (by simp)]
  have heq : rayIdealClassRepresentative K m hm ⊤ top_ne_bot (by simp) = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp [rayIdealClassRepresentative]
  rw [heq, map_one]

theorem rayIdealClass_mul
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (I J : Ideal (𝓞 K)) :
    rayIdealClass K m hm (I * J) =
      (rayIdealClass K m hm I).bind
        (fun a => (rayIdealClass K m hm J).map (fun b => a * b)) := by
  by_cases hI : I = ⊥ ∨ I ⊔ m ≠ ⊤
  · have hIJ : I * J = ⊥ ∨ I * J ⊔ m ≠ ⊤ := by
      rcases hI with hI | hI
      · simp [hI]
      · right
        intro h
        apply hI
        exact top_unique (h ▸ sup_le_sup_right Ideal.mul_le_left m)
    rw [rayIdealClass_eq_none K m hm (I * J) hIJ,
      rayIdealClass_eq_none K m hm I hI]
    rfl
  by_cases hJ : J = ⊥ ∨ J ⊔ m ≠ ⊤
  · have hIJ : I * J = ⊥ ∨ I * J ⊔ m ≠ ⊤ := by
      rcases hJ with hJ | hJ
      · simp [hJ]
      · right
        intro h
        apply hJ
        exact top_unique (h ▸ sup_le_sup_right Ideal.mul_le_right m)
    rw [rayIdealClass_eq_none K m hm (I * J) hIJ,
      rayIdealClass_eq_none K m hm J hJ]
    cases rayIdealClass K m hm I <;> rfl
  have hIn : I ≠ ⊥ := fun h => hI (Or.inl h)
  have hJn : J ≠ ⊥ := fun h => hJ (Or.inl h)
  have hIc : I ⊔ m = ⊤ := not_not.mp (fun h => hI (Or.inr h))
  have hJc : J ⊔ m = ⊤ := not_not.mp (fun h => hJ (Or.inr h))
  have hIJn : I * J ≠ ⊥ := by
    intro h
    exact (not_or.mpr ⟨hIn, hJn⟩) (Ideal.mul_eq_bot.mp h)
  have hIJc : I * J ⊔ m = ⊤ := by
    rw [Ideal.mul_sup_eq_of_coprime_left hIc, hJc]
  rw [rayIdealClass_eq_some K m hm I hIn hIc,
    rayIdealClass_eq_some K m hm J hJn hJc,
    rayIdealClass_eq_some K m hm (I * J) hIJn hIJc]
  simp only [Option.bind_some, Option.map_some]
  have heq : rayIdealClassRepresentative K m hm (I * J) hIJn hIJc =
      rayIdealClassRepresentative K m hm I hIn hIc *
        rayIdealClassRepresentative K m hm J hJn hJc := by
    apply Subtype.ext
    apply Units.ext
    simp [rayIdealClassRepresentative, FractionalIdeal.coeIdeal_mul]
  rw [heq, map_mul]

theorem rayIdealClass_span
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (α : 𝓞 K) (hα : α ≠ 0) (hcong : α - 1 ∈ m)
    (hpos : ∀ φ : K →+* ℝ, 0 < φ (α : K)) :
    rayIdealClass K m hm (Ideal.span {α}) = some 1 := by
  have hn : Ideal.span {α} ≠ ⊥ := fun h => hα (Ideal.span_singleton_eq_bot.mp h)
  have hc : Ideal.span {α} ⊔ m = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have ha : α ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_left (Ideal.subset_span (by simp))
    have hb : α - 1 ∈ Ideal.span {α} ⊔ m := Ideal.mem_sup_right hcong
    have hh := (Ideal.span {α} ⊔ m).sub_mem ha hb
    simpa using hh
  rw [rayIdealClass_eq_some K m hm (Ideal.span {α}) hn hc]
  apply congrArg some
  apply (QuotientGroup.eq_one_iff _).mpr
  change rayIdealFractionalIdeal K (Ideal.span {α}) hn ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup (narrowIdealModulus K m hm)
  apply Subgroup.subset_closure
  have hαK : (α : K) ≠ 0 := by
    exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hα
  refine ⟨Units.mk0 (α : K) hαK,
    (integralNarrowRayCongruence K m hm α hαK).mpr ⟨hcong, hpos⟩, ?_⟩
  apply Units.ext
  simp [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]

end DedekindZetaZeroFree.AbelianQuotient

end
