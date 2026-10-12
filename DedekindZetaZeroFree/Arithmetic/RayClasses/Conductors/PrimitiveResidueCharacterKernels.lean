module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.ResidueUnitCharacters

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

theorem residueRayCharacter_kernel_trivial_iff
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (f : Ideal (𝓞 F)) (hmf : m ≤ f) :
    (∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ f → Ideal.span {α} ⊔ m = ⊤ →
      η (Ideal.span {α}) = 1) ↔
    (∀ u : (𝓞 F ⧸ m)ˣ,
      Units.map (Ideal.Quotient.factor hmf).toMonoidHom u = 1 →
      residueRayCharacter hF hm hmt η u = 1) := by
  classical
  constructor
  · intro h u hu
    obtain ⟨α, hα, hcop, hlift⟩ := residueUnit_exists_nonzero_lift hmt u
    have hq : Ideal.Quotient.mk f α = 1 := by
      have hv := congrArg (fun v : (𝓞 F ⧸ f)ˣ => (v : 𝓞 F ⧸ f)) hu
      simpa [Units.coe_map, hlift, Ideal.Quotient.factor_mk] using hv
    apply Units.ext
    simpa only [Units.val_one, residueRayCharacter_apply hF hm hmt η α hα hcop u hlift]
      using h α hα ((Ideal.Quotient.mk_eq_one_iff_sub_mem α).mp hq) hcop
  · intro h α hα hcong hcop
    have hunit : IsUnit (Ideal.Quotient.mk m α) := by
      apply Ideal.span_singleton_eq_top.mp
      have hx := congrArg (Ideal.map (Ideal.Quotient.mk m)) hcop
      simpa only [Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self,
        Ideal.map_top, sup_bot_eq, Set.image_singleton] using hx
    obtain ⟨u, hu⟩ := hunit
    have hker : Units.map (Ideal.Quotient.factor hmf).toMonoidHom u = 1 := by
      apply Units.ext
      simpa [Units.coe_map, hu, Ideal.Quotient.factor_mk] using
        (Ideal.Quotient.mk_eq_one_iff_sub_mem α).mpr hcong
    have hv := congrArg (fun v : ℂˣ => (v : ℂ)) (h u hker)
    simpa only [Units.val_one, residueRayCharacter_apply hF hm hmt η α hα hcop u hu] using hv

theorem isPrimitive_iff_residueRayCharacter_kernel_nontrivial
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) :
    η.IsPrimitive ↔
    ∀ (f : Ideal (𝓞 F)) (hmf : m < f), ∃ u : (𝓞 F ⧸ m)ˣ,
      Units.map (Ideal.Quotient.factor hmf.le).toMonoidHom u = 1 ∧
      residueRayCharacter hF hm hmt η u ≠ 1 := by
  classical
  constructor
  · intro hprim f hmf
    by_contra hn
    have hker : ∀ u : (𝓞 F ⧸ m)ˣ,
        Units.map (Ideal.Quotient.factor hmf.le).toMonoidHom u = 1 →
        residueRayCharacter hF hm hmt η u = 1 := by
      simpa only [not_exists, not_and, not_not] using hn
    have htriv := (residueRayCharacter_kernel_trivial_iff hF hm hmt η f hmf.le).mpr hker
    obtain ⟨α, hα, hcong, _, hcop, hne⟩ := hprim f hmf
    exact hne (htriv α hα hcong hcop)
  · intro h f hmf
    have hn : ¬ (∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ f →
        Ideal.span {α} ⊔ m = ⊤ → η (Ideal.span {α}) = 1) := by
      intro htriv
      obtain ⟨u, hker, hne⟩ := h f hmf
      exact hne ((residueRayCharacter_kernel_trivial_iff hF hm hmt η f hmf.le).mp htriv u hker)
    push_neg at hn
    obtain ⟨α, hα, hcong, hcop, hne⟩ := hn
    refine ⟨α, hα, hcong, ?_, hcop, hne⟩
    letI := hF
    intro φ
    have hc := NumberField.IsTotallyComplex.complexEmbedding_not_isReal
      (Complex.ofRealHom.comp φ)
    apply (hc ?_).elim
    apply NumberField.ComplexEmbedding.isReal_iff.mpr
    ext x
    simp [NumberField.ComplexEmbedding.conjugate]

theorem residueRayCharacter_exists_kernel_ne_one
    (hF : NumberField.IsTotallyComplex F) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (hprim : η.IsPrimitive)
    (f : Ideal (𝓞 F)) (hmf : m < f) :
    ∃ u : (𝓞 F ⧸ m)ˣ,
      Units.map (Ideal.Quotient.factor hmf.le).toMonoidHom u = 1 ∧
      residueRayCharacter hF hm hmt η u ≠ 1 := by
  exact (isPrimitive_iff_residueRayCharacter_kernel_nontrivial hF hm hmt η).mp hprim f hmf

end

end DedekindZetaZeroFree.Hecke
