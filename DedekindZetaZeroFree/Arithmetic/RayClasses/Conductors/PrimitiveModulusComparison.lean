module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.TotallyPositiveCoprimeRepresentatives
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.PrincipalIdealCharacterValues

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

variable {F : Type} [Field F] [NumberField F]

theorem rayCharacter_primitive_modulus_le {m f q : Ideal (𝓞 F)}
    (hm : m ≠ ⊥) (hf : f ≠ ⊥) (hq : q ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (hη : η.IsPrimitive)
    (θ : DedekindZetaZeroFree.RayClassCharacter F f)
    (h : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ (m * f * q) = ⊤ → η I = θ I) :
    f ≤ m := by
  by_contra hfm

  have hlt : m < m ⊔ f := by
    rw [lt_iff_le_not_ge]
    exact ⟨le_sup_left, fun hge => hfm (le_trans le_sup_right hge)⟩

  obtain ⟨α, hα0, hα1, hαpos, hαcop, hηα⟩ := hη (m ⊔ f) hlt

  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hα1

  set b0 : 𝓞 F := α - u with hb0def
  have hb0_eq : b0 = 1 + v := by
    have hα : α = u + v + 1 := by rw [huv]; ring
    rw [hb0def, hα]; ring
  have hb0α : b0 - α ∈ m := by
    have : b0 - α = -u := by rw [hb0def]; ring
    rw [this]; exact neg_mem hu
  have hb0f : b0 - 1 ∈ f := by
    have : b0 - 1 = v := by rw [hb0_eq]; ring
    rw [this]; exact hv

  have key : ∀ {a b : 𝓞 F}, a - b ∈ m → Ideal.span {a} ⊔ m = Ideal.span {b} ⊔ m := by
    intro a b hab
    apply le_antisymm
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      rw [Ideal.span_singleton_le_iff_mem]
      have : a = b + (a - b) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mem_span_singleton_self b) hab
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      rw [Ideal.span_singleton_le_iff_mem]
      have : b = a - (a - b) := by ring
      rw [this]
      exact Submodule.sub_mem_sup (Ideal.mem_span_singleton_self a) hab

  have hsup_b0_m : Ideal.span {b0} ⊔ m = ⊤ := by
    rw [key hb0α, hαcop]
  have hsup_b0_f : Ideal.span {b0} ⊔ f = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 F) = b0 - (b0 - 1) := by ring
    rw [this]
    exact Submodule.sub_mem_sup (Ideal.mem_span_singleton_self b0) hb0f
  have hmf : m * f ≠ ⊥ := by
    intro hc
    rcases (Ideal.mul_eq_bot.mp hc) with hc | hc
    · exact hm hc
    · exact hf hc
  have hsup_b0_mf : Ideal.span {b0} ⊔ (m * f) = ⊤ := by
    rw [Ideal.sup_mul_eq_of_coprime_left (I := Ideal.span {b0}) (J := m) (K := f) hsup_b0_m,
      hsup_b0_f]

  obtain ⟨b, hb0, hbb0, hbcop, hbpos⟩ :=
    exists_totallyPositive_coprime_residue F (m * f) q hmf hq b0 hsup_b0_mf
  have hb_α : b - α ∈ m := by
    have : b - α = (b - b0) + (b0 - α) := by ring
    rw [this]
    exact add_mem (Ideal.mul_le_left (I := m) (J := f) hbb0) hb0α
  have hb_1 : b - 1 ∈ f := by
    have : b - 1 = (b - b0) + (b0 - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_le_right (I := m) (J := f) hbb0) hb0f

  have hres : η (Ideal.span {α}) = η (Ideal.span {b}) :=
    rayCharacter_span_eq_of_residue hm η α b hα0 hb0 (by
      have : α - b = -(b - α) := by ring
      rw [this]; exact neg_mem hb_α) hαcop hαpos hbpos
  have hspanb_ne : Ideal.span {b} ≠ ⊥ := fun hc => hb0 (Ideal.span_singleton_eq_bot.mp hc)
  have hηb : η (Ideal.span {b}) = θ (Ideal.span {b}) := h _ hspanb_ne hbcop
  have hθb : θ (Ideal.span {b}) = 1 := θ.map_span' b hb0 hb_1 hbpos
  exact hηα (hres.trans (hηb.trans hθb))

end DedekindZetaZeroFree.LargeSieve
