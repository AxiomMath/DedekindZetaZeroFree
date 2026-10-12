module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

namespace DedekindZetaZeroFree

namespace IsotropicComplement

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

private lemma extend_disjoint (E B : Submodule K M) (hd : Disjoint E B)
    (x : M) (hx : x ∉ E ⊔ B) : Disjoint E (B ⊔ K ∙ x) := by
  rw [Submodule.disjoint_def]
  intro v hvE hv
  obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, add_zero] at hvE ⊢
    exact (Submodule.disjoint_def.mp hd) b hvE hb
  · exfalso
    apply hx
    have haz : a • x ∈ E ⊔ B := by
      have : b + a • x - b ∈ E ⊔ B :=
        (E ⊔ B).sub_mem (Submodule.mem_sup_left hvE) (Submodule.mem_sup_right hb)
      simpa only [add_sub_cancel_left] using this
    have := (E ⊔ B).smul_mem a⁻¹ haz
    simpa [smul_smul, ha] using this

private lemma extend_isotropic (H : LinearMap.BilinForm K M) (hAlt : H.IsAlt)
    (B : Submodule K M) (hB : B ≤ H.orthogonal B)
    (x : M) (hx : x ∈ H.orthogonal B) :
    B ⊔ K ∙ x ≤ H.orthogonal (B ⊔ K ∙ x) := by
  intro v hv w hw
  obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hcb : H c b = 0 := hB hb c hc
  have hcx : H c x = 0 := hx c hc
  have hxb : H x b = 0 := hAlt.isRefl _ _ (hx b hb)
  simp [map_add, map_smul, hcb, hcx, hxb, hAlt.self_eq_zero]

end IsotropicComplement

open Module

theorem exists_lagrangian_complement
    (K M : Type*) [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M]
    (H : LinearMap.BilinForm K M) (hAlt : H.IsAlt)
    (hPerfect : H.Nondegenerate) (E : Submodule K M)
    (hLagrangian : H.orthogonal E = E) :
    ∃ B : Submodule K M,
      IsCompl E B ∧ H.orthogonal B = B ∧
      (∀ x ∈ B, ∀ y ∈ B, H x y = 0) ∧
      (∀ v : M, ∃! p : E × B, (p.1 : M) + (p.2 : M) = v) := by
  classical
  let S : Set (Submodule K M) := {B | Disjoint E B ∧ B ≤ H.orthogonal B}
  have hS : S.Nonempty := ⟨⊥, disjoint_bot_right, bot_le⟩
  obtain ⟨B, ⟨hEB, hB⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian K M)) S hS
  have hle : H.orthogonal B ≤ E ⊔ B := by
    intro x hx
    by_contra hx'
    have hC : B ⊔ K ∙ x ∈ S :=
      ⟨IsotropicComplement.extend_disjoint E B hEB x hx', IsotropicComplement.extend_isotropic H hAlt B hB x hx⟩
    apply hmax (B ⊔ K ∙ x) hC
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hx'
    have hxB : x ∈ B := by
      rw [heq]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    exact Submodule.mem_sup_right hxB
  have horth : H.orthogonal (E ⊔ B) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxE : x ∈ E := by
      rw [← hLagrangian]
      exact H.orthogonal_le le_sup_left hx
    have hxB : x ∈ B := by
      rw [← H.orthogonal_orthogonal hPerfect hAlt.isRefl B]
      exact H.orthogonal_le hle hx
    exact Submodule.disjoint_def.mp hEB x hxE hxB
  have htop : E ⊔ B = ⊤ := by
    have := H.orthogonal_orthogonal hPerfect hAlt.isRefl (E ⊔ B)
    rw [horth, H.orthogonal_bot] at this
    exact this.symm
  have hc : IsCompl E B := ⟨hEB, codisjoint_iff.mpr htop⟩
  have hdimE := H.finrank_orthogonal hPerfect E
  rw [hLagrangian] at hdimE
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq E B
  rw [htop, hEB.eq_bot] at hdim
  simp only [finrank_top, finrank_bot, add_zero] at hdim
  have hdimB := H.finrank_orthogonal hPerfect B
  have heq : H.orthogonal B = B := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hB
    omega
  refine ⟨B, hc, heq, ?_, fun v => Submodule.existsUnique_add_of_isCompl_prod hc v⟩
  intro x hx y hy
  exact hB hy x hx

namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

def IsSelfOrthogonal (A : SArithmeticData F) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) : Prop :=
  ∀ x : A.V, x ∈ L ↔ ∀ y : A.V, y ∈ L → H y x = 1

def IsIsotropic (A : SArithmeticData F) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) : Prop :=
  ∀ x : A.V, x ∈ L → ∀ y : A.V, y ∈ L → H x y = 1

def IsSUnitIsotropicComplement (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V) : Prop :=
  IsCompl A.E B ∧ A.IsIsotropic H B ∧
    (∀ v : A.V, ∃! p : A.E × B, (p.1 : A.V) * (p.2 : A.V) = v)

noncomputable section

abbrev PrimarySpace (A : SArithmeticData F) (ℓ : ℕ) :=
  AddSubgroup.torsionBy (Additive A.V) (ℓ : ℤ)

instance primaryModule (A : SArithmeticData F) (ℓ : ℕ) :
    Module (ZMod ℓ) (A.PrimarySpace ℓ) :=
  AddSubgroup.torsionBy.zmodModule

def primarySubspace (A : SArithmeticData F) (ℓ : ℕ) (B : Subgroup A.V) :
    Submodule (ZMod ℓ) (A.PrimarySpace ℓ) :=
  AddSubgroup.toZModSubmodule ℓ
    (B.toAddSubgroup.comap (A.PrimarySpace ℓ).subtype)

def PrimaryLagrangianComplementSpec (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V) (ℓ : ℕ) : Prop :=
  IsCompl (A.primarySubspace ℓ A.E) (A.primarySubspace ℓ B) ∧
    (∀ x : A.PrimarySpace ℓ,
      x ∈ A.primarySubspace ℓ A.E ↔
        ∀ y : A.PrimarySpace ℓ, y ∈ A.primarySubspace ℓ A.E →
          H (Additive.toMul y.val) (Additive.toMul x.val) = 1) ∧
    (∀ x : A.PrimarySpace ℓ,
      x ∈ A.primarySubspace ℓ B ↔
        ∀ y : A.PrimarySpace ℓ, y ∈ A.primarySubspace ℓ B →
          H (Additive.toMul y.val) (Additive.toMul x.val) = 1)

end
end SArithmeticData
end DedekindZetaZeroFree
