module

public import DedekindZetaZeroFree.Arithmetic.Kummer.FrequencyClassesAndCharacterRigidity

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.CofinitePrimitiveRigidity
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain
variable {F : Type} [Field F] [NumberField F]

 def quotientRay (ν ψ : Detector.PrimitiveFrequencyCharacter F) :
    RayClassCharacter F (ν.conductor * ψ.conductor) where
  toFun I := ν.character I / ψ.character I
  map_mul' I J := by rw [ν.character.map_mul', ψ.character.map_mul', mul_div_mul_comm]
  map_top' := by simp [ν.character.map_top', ψ.character.map_top']
  eq_zero_iff' I := by
    have hc : I ⊔ (ν.conductor * ψ.conductor) = ⊤ ↔
        I ⊔ ν.conductor = ⊤ ∧ I ⊔ ψ.conductor = ⊤ := by
      constructor
      · intro h
        exact ⟨top_unique (h ▸ sup_le_sup_left Ideal.mul_le_left I),
          top_unique (h ▸ sup_le_sup_left Ideal.mul_le_right I)⟩
      · rintro ⟨hν, hψ⟩
        rw [Ideal.sup_mul_eq_of_coprime_left hν, hψ]
    simp only [div_eq_zero_iff, ν.character.eq_zero_iff', ψ.character.eq_zero_iff']
    tauto
  map_span' a ha hmod hpos := by
    rw [ν.character.map_span' a ha (Ideal.mul_le_left hmod) hpos,
      ψ.character.map_span' a ha (Ideal.mul_le_right hmod) hpos, div_self one_ne_zero]

theorem prime_character_ne_zero_cofinite (ψ : Detector.PrimitiveFrequencyCharacter F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ψ.character v.asIdeal ≠ 0 := by
  let m := RayClassBridge.narrowIdealModulus F ψ.conductor ψ.conductor_ne_zero
  filter_upwards [m.finitePart.support.finite_toSet.compl_mem_cofinite] with v hv
  have hn : ¬ ψ.conductor ≤ v.asIdeal := by
    change v ∉ (RayClassBridge.narrowIdealModulus F ψ.conductor
      ψ.conductor_ne_zero).finitePart.support at hv
    simpa only [← Finset.mem_coe, RayClassBridge.narrowIdealModulus_support,
      Set.mem_setOf_eq] using hv
  intro hz
  rcases (ψ.character.eq_zero_iff' _).mp hz with hz | hz
  · exact v.ne_bot hz
  · apply hz
    exact v.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left
      (fun he => hn (he ▸ le_sup_right)))

theorem ideal_values_eq_on_common_domain [NumberField.IsTotallyComplex F]
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ν.character v.asIdeal = ψ.character v.asIdeal)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hν : I ⊔ ν.conductor = ⊤) (hψ : I ⊔ ψ.conductor = ⊤) :
    ν.character I = ψ.character I := by
  have hq : (quotientRay ν ψ).IsPrincipal := by
    apply Detector.FrequencyCharacterRigidity.principal_of_cofinite_prime_values
    filter_upwards [h, prime_character_ne_zero_cofinite ψ] with v hv hn
    change ν.character v.asIdeal / ψ.character v.asIdeal = 1
    rw [hv, div_self hn]
  have hc : I ⊔ (ν.conductor * ψ.conductor) = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left hν, hψ]
  have hn : ψ.character I ≠ 0 := by
    intro hz
    rcases (ψ.character.eq_zero_iff' I).mp hz with hz | hz
    · exact hI hz
    · exact hz hψ
  exact (div_eq_one_iff_eq hn).mp (hq I hI hc)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.CofinitePrimitiveRigidity

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.CofinitePrimitiveRigidity
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

private theorem totallyPositive [NumberField.IsTotallyComplex F] (a : 𝓞 F) :
    ∀ φ : F →+* ℝ, 0 < φ (a : F) := by
  intro φ
  exfalso
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ)
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  simp [NumberField.ComplexEmbedding.conjugate]

private theorem coprime_congr {R : Type*} [CommRing R] (m : Ideal R) (a b : R)
    (ha : Ideal.span {a} ⊔ m = ⊤) (hba : b - a ∈ m) : Ideal.span {b} ⊔ m = ⊤ := by
  apply top_unique
  rw [← ha]
  apply sup_le _ le_sup_right
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  have hb : b ∈ Ideal.span {b} ⊔ m :=
    (show Ideal.span {b} ≤ Ideal.span {b} ⊔ m from le_sup_left) (Ideal.mem_span_singleton_self b)
  have hd : b - a ∈ Ideal.span {b} ⊔ m :=
    (show m ≤ Ideal.span {b} ⊔ m from le_sup_right) hba
  simpa only [sub_sub_cancel] using (Ideal.span {b} ⊔ m).sub_mem hb hd

private theorem principal_value_congr [NumberField.IsTotallyComplex F]
    (m : Ideal (𝓞 F)) (χ : RayClassCharacter F m) (hm : m ≠ ⊤)
    (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hac : Ideal.span {a} ⊔ m = ⊤) (hab : a - b ∈ m) :
    χ (Ideal.span {a}) = χ (Ideal.span {b}) := by
  have hu : IsUnit (Ideal.Quotient.mk m a) := by
    have he := congrArg (Ideal.map (Ideal.Quotient.mk m)) hac
    have he' : Ideal.map (Ideal.Quotient.mk m) (Ideal.span {a}) = ⊤ := by
      simpa only [Ideal.map_sup, Ideal.map_top, Ideal.map_quotient_self, sup_bot_eq] using he
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top] at he'
    exact he'
  obtain ⟨u, hu⟩ := hu
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (𝓞 F ⧸ m)ˣ).val
  have he : Ideal.Quotient.mk m (a * c) = 1 := by
    rw [map_mul, ← hu, hc]
    exact u.val_inv
  have hac' : a * c - 1 ∈ m := Ideal.Quotient.eq.mp (by simpa using he)
  have hc0 : c ≠ 0 := by
    intro hz
    subst c
    have h1 : (1 : 𝓞 F) ∈ m := by simpa using m.neg_mem hac'
    exact hm (Ideal.eq_top_of_isUnit_mem m h1 isUnit_one)
  have hbe : Ideal.Quotient.mk m b = Ideal.Quotient.mk m a :=
    (Ideal.Quotient.eq.mpr hab).symm
  have hbc : b * c - 1 ∈ m := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_mul, map_one, hbe] using he
  have hva := χ.map_span' (a * c) (mul_ne_zero ha hc0) hac' (totallyPositive _)
  have hvb := χ.map_span' (b * c) (mul_ne_zero hb hc0) hbc (totallyPositive _)
  rw [← Ideal.span_singleton_mul_span_singleton, χ.map_mul'] at hva hvb
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hva) (hva.trans hvb.symm)

private theorem conductor_le [NumberField.IsTotallyComplex F]
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ ν.conductor = ⊤ →
      I ⊔ ψ.conductor = ⊤ → ν.character I = ψ.character I) :
    ψ.conductor ≤ ν.conductor := by
  by_contra hn
  have hlt : ν.conductor < ν.conductor ⊔ ψ.conductor :=
    lt_of_le_of_ne le_sup_left (fun he => hn (he ▸ le_sup_right))
  have hmt : ν.conductor ≠ ⊤ := by intro he; simp [he] at hn
  obtain ⟨a, ha, ham, _, hac, hne⟩ := ν.primitive _ hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ham
  let b := a - x
  have hba : b - a ∈ ν.conductor := by
    convert ν.conductor.neg_mem hx using 1 <;> dsimp [b] <;> ring
  have hb1 : b - 1 ∈ ψ.conductor := by
    have he : b - 1 = y := by dsimp [b]; linear_combination -hxy
    rw [he]
    exact hy
  have hbc : Ideal.span {b} ⊔ ν.conductor = ⊤ := coprime_congr _ _ _ hac hba
  have hb : b ≠ 0 := by
    intro hz
    have : ν.conductor = ⊤ := by simpa [hz] using hbc
    exact hmt this
  have hbψ : Ideal.span {b} ⊔ ψ.conductor = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hbm : b ∈ Ideal.span {b} ⊔ ψ.conductor :=
      (show Ideal.span {b} ≤ Ideal.span {b} ⊔ ψ.conductor from le_sup_left)
        (Ideal.mem_span_singleton_self b)
    have hbd : b - 1 ∈ Ideal.span {b} ⊔ ψ.conductor :=
      (show ψ.conductor ≤ Ideal.span {b} ⊔ ψ.conductor from le_sup_right) hb1
    simpa only [sub_sub_cancel] using (Ideal.span {b} ⊔ ψ.conductor).sub_mem hbm hbd
  apply hne
  calc
    ν.character (Ideal.span {a}) = ν.character (Ideal.span {b}) :=
      principal_value_congr _ _ hmt a b ha hb hac (by simpa using ν.conductor.neg_mem hba)
    _ = ψ.character (Ideal.span {b}) := h _ (by simpa using hb) hbc hbψ
    _ = 1 := ψ.character.map_span' b hb hb1 (totallyPositive _)

theorem primitive_conductors_eq [NumberField.IsTotallyComplex F]
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ ν.conductor = ⊤ →
      I ⊔ ψ.conductor = ⊤ → ν.character I = ψ.character I) :
    ν.conductor = ψ.conductor := by
  exact le_antisymm (conductor_le ψ ν (fun I hI hψ hν => (h I hI hν hψ).symm))
    (conductor_le ν ψ h)

theorem primitive_eq_of_common_domain [NumberField.IsTotallyComplex F]
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ ν.conductor = ⊤ →
      I ⊔ ψ.conductor = ⊤ → ν.character I = ψ.character I) : ν = ψ := by
  have hc := primitive_conductors_eq ν ψ h
  have hv : ∀ I : Ideal (𝓞 F), ν.character I = ψ.character I := by
    intro I
    by_cases hbad : I = ⊥ ∨ I ⊔ ν.conductor ≠ ⊤
    · exact ((ν.character.eq_zero_iff' I).mpr hbad).trans
        ((ψ.character.eq_zero_iff' I).mpr (by simpa only [← hc] using hbad)).symm
    · push Not at hbad
      exact h I hbad.1 hbad.2 (by simpa only [← hc] using hbad.2)
  cases ν with
  | mk m hm χ hχ =>
    cases ψ with
    | mk n hn η hη =>
      dsimp at hc hv
      subst n
      have he : χ = η := by
        cases χ
        cases η
        congr
        exact funext hv
      subst η
      rfl
end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic.CofinitePrimitiveRigidity

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

theorem primitive_inducers_eq_of_cofinite_prime_values
    [NumberField.IsTotallyComplex F]
    (ν ψ : Detector.PrimitiveFrequencyCharacter F)
    (h : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ν.character v.asIdeal = ψ.character v.asIdeal) :
    ν = ψ := by
  apply CofinitePrimitiveRigidity.primitive_eq_of_common_domain ν ψ
  exact CofinitePrimitiveRigidity.ideal_values_eq_on_common_domain ν ψ h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.MinusArithmetic

end
