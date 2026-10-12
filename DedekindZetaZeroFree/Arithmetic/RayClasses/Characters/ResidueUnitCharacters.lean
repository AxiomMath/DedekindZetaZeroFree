module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUnitarityAndOrthogonality

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

private theorem residueLift_coprime (α : 𝓞 F) (u : (𝓞 F ⧸ m)ˣ)
    (hu : (u : 𝓞 F ⧸ m) = Ideal.Quotient.mk m α) :
    Ideal.span {α} ⊔ m = ⊤ := by
  obtain ⟨δ, hδ⟩ := Ideal.Quotient.mk_surjective ((↑(u⁻¹)) : 𝓞 F ⧸ m)
  have hprod : Ideal.Quotient.mk m (α * δ) = 1 := by
    rw [map_mul, ← hu, hδ]
    exact u.val_inv
  have hmem : α * δ - 1 ∈ m := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hprod
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  have hmul : α * δ ∈ Ideal.span {α} ⊔ m :=
    Ideal.mem_sup_left (Ideal.mul_mem_right δ _ (Ideal.subset_span (by simp)))
  have hsub := (Ideal.span {α} ⊔ m).sub_mem hmul (Ideal.mem_sup_right hmem)
  simpa using hsub

theorem residueUnit_exists_nonzero_lift
    (hmt : m ≠ ⊤) (u : (𝓞 F ⧸ m)ˣ) :
    ∃ α : 𝓞 F, α ≠ 0 ∧ Ideal.span {α} ⊔ m = ⊤ ∧
      (u : 𝓞 F ⧸ m) = Ideal.Quotient.mk m α := by
  letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
  obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 F ⧸ m)
  refine ⟨α, ?_, residueLift_coprime α u hα.symm, hα.symm⟩
  intro hz
  have hu0 : (u : 𝓞 F ⧸ m) = 0 := by simpa [hz] using hα.symm
  exact u.isUnit.ne_zero hu0

private theorem residue_positive (hF : NumberField.IsTotallyComplex F)
    (α : 𝓞 F) : ∀ φ : F →+* ℝ, 0 < φ (α : F) := by
  letI := hF
  intro φ
  exfalso
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal
    (Complex.ofRealHom.comp φ)
  change star (Complex.ofRealHom.comp φ) = Complex.ofRealHom.comp φ
  ext x
  simp

theorem residueRayCharacter_lift_compatible
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (α β : 𝓞 F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαcop : Ideal.span {α} ⊔ m = ⊤) (hβcop : Ideal.span {β} ⊔ m = ⊤)
    (hres : Ideal.Quotient.mk m α = Ideal.Quotient.mk m β) :
    η (Ideal.span {α}) = η (Ideal.span {β}) := by
  letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp
    (Ideal.isCoprime_iff_sup_eq.mpr hαcop)
  obtain ⟨δ, haδ⟩ := Ideal.mem_span_singleton.mp ha
  have hprod : Ideal.Quotient.mk m (α * δ) = 1 := by
    have h := congrArg (Ideal.Quotient.mk m) hab
    simpa [← haδ, hb, Ideal.Quotient.eq_zero_iff_mem.mpr hb] using h
  let u : (𝓞 F ⧸ m)ˣ :=
    ⟨Ideal.Quotient.mk m α, Ideal.Quotient.mk m δ,
      by simpa using hprod, by simpa [mul_comm] using hprod⟩
  have hδ : δ ≠ 0 := by
    intro hz
    have : (↑(u⁻¹) : 𝓞 F ⧸ m) = 0 := by change Ideal.Quotient.mk m δ = 0; simp [hz]
    exact (u⁻¹).isUnit.ne_zero this
  have hδcop : Ideal.span {δ} ⊔ m = ⊤ := residueLift_coprime δ (u⁻¹) rfl
  have hβprod : Ideal.Quotient.mk m (β * δ) = 1 := by
    rw [map_mul, ← hres, ← map_mul]
    exact hprod
  have hαδ := η.map_span' (α * δ) (mul_ne_zero hα hδ)
    ((Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hprod) (residue_positive hF _)
  have hβδ := η.map_span' (β * δ) (mul_ne_zero hβ hδ)
    ((Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hβprod) (residue_positive hF _)
  rw [← Ideal.span_singleton_mul_span_singleton, η.map_mul'] at hαδ hβδ
  have hηδ : η (Ideal.span {δ}) ≠ 0 := by
    rw [ne_eq, η.eq_zero_iff']
    simp [Ideal.span_singleton_eq_bot, hδ, hδcop]
  exact mul_right_cancel₀ hηδ (hαδ.trans hβδ.symm)

 def residueLift (hmt : m ≠ ⊤) (u : (𝓞 F ⧸ m)ˣ) : 𝓞 F :=
  Classical.choose (residueUnit_exists_nonzero_lift hmt u)

 theorem residueLift_spec (hmt : m ≠ ⊤) (u : (𝓞 F ⧸ m)ˣ) :
    residueLift hmt u ≠ 0 ∧ Ideal.span {residueLift hmt u} ⊔ m = ⊤ ∧
      (u : 𝓞 F ⧸ m) = Ideal.Quotient.mk m (residueLift hmt u) :=
  Classical.choose_spec (residueUnit_exists_nonzero_lift hmt u)

 def residueValue (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (u : (𝓞 F ⧸ m)ˣ) : ℂˣ :=
  Units.mk0 (η (Ideal.span {residueLift hmt u})) (by
    rw [ne_eq, η.eq_zero_iff']
    simp [Ideal.span_singleton_eq_bot, (residueLift_spec hmt u).1,
      (residueLift_spec hmt u).2.1])

 theorem residueValue_apply
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (α : 𝓞 F) (hα : α ≠ 0) (hcop : Ideal.span {α} ⊔ m = ⊤)
    (u : (𝓞 F ⧸ m)ˣ) (hu : (u : 𝓞 F ⧸ m) = Ideal.Quotient.mk m α) :
    (residueValue hmt η u : ℂ) = η (Ideal.span {α}) := by
  exact residueRayCharacter_lift_compatible hF hm hmt η _ α
    (residueLift_spec hmt u).1 hα (residueLift_spec hmt u).2.1 hcop
    ((residueLift_spec hmt u).2.2.symm.trans hu)

def residueRayCharacter
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    (𝓞 F ⧸ m)ˣ →* ℂˣ where
  toFun := residueValue hmt η
  map_one' := by
    apply Units.ext
    change (residueValue hmt η 1 : ℂ) = 1
    rw [residueValue_apply hF hm hmt η 1 one_ne_zero (by simp) 1 (by simp)]
    simpa using η.map_top'
  map_mul' u v := by
    apply Units.ext
    change (residueValue hmt η (u * v) : ℂ) =
      (residueValue hmt η u : ℂ) * (residueValue hmt η v : ℂ)
    let α := residueLift hmt u
    let β := residueLift hmt v
    have hα := residueLift_spec hmt u
    have hβ := residueLift_spec hmt v
    have hcop : Ideal.span {α * β} ⊔ m = ⊤ := by
      rw [← Ideal.span_singleton_mul_span_singleton,
        Ideal.mul_sup_eq_of_coprime_left hα.2.1, hβ.2.1]
    rw [residueValue_apply hF hm hmt η (α * β) (mul_ne_zero hα.1 hβ.1) hcop
      (u * v) (by simp only [Units.val_mul, map_mul]; rw [hα.2.2, hβ.2.2])]
    exact (congrArg η (Ideal.span_singleton_mul_span_singleton α β)).symm.trans
      (η.map_mul' _ _)

theorem residueRayCharacter_apply
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (α : 𝓞 F) (hα : α ≠ 0) (hcop : Ideal.span {α} ⊔ m = ⊤)
    (u : (𝓞 F ⧸ m)ˣ) (hu : (u : 𝓞 F ⧸ m) = Ideal.Quotient.mk m α) :
    (residueRayCharacter hF hm hmt η u : ℂ) = η (Ideal.span {α}) := by
  exact residueValue_apply hF hm hmt η α hα hcop u hu

end

end DedekindZetaZeroFree.Hecke
