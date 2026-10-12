module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem algebra_normalized_reciprocity
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hsandwich : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      a ∣ Q.cond a ∧ Q.cond a ∣ a * q) :
    (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      ∀ n : Ideal (𝓞 F), n ⊔ q = ⊤ →
        ((Q.χ a) n = 0 ↔ n = ⊥ ∨ n ⊔ a ≠ ⊤)) ∧
    (∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b)) ∧
    (∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ → a ⊔ b = ⊤ → Q.cls a = Q.cls b →
      ∃ ψ : DedekindZetaZeroFree.RayClassCharacter F (a * b), ψ.IsPrimitive ∧
        ∀ n : Ideal (𝓞 F), n ⊔ q = ⊤ →
          ψ n = (Q.χ a) n * (Q.χ b) n) := by
  classical

  have hqc : q ≤ c := Ideal.le_of_dvd hcq
  have hsupc : ∀ a : Ideal (𝓞 F), a ⊔ q = ⊤ → a ⊔ c = ⊤ := fun a haq =>
    eq_top_iff.mpr (haq ▸ sup_le_sup_left hqc a)

  have hcop_mul : ∀ n m f : Ideal (𝓞 F),
      (n ⊔ (m * f) = ⊤) ↔ (n ⊔ m = ⊤ ∧ n ⊔ f = ⊤) := fun n m f => by
    simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]

  have hcond_coprime : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      ∀ n : Ideal (𝓞 F), n ⊔ q = ⊤ → (n ⊔ Q.cond a = ⊤ ↔ n ⊔ a = ⊤) := by
    intro a ha haq n hnq
    obtain ⟨hac, hca⟩ := hsandwich a ha haq
    have hle : Q.cond a ≤ a := Ideal.le_of_dvd hac
    refine ⟨fun h => le_antisymm le_top (h ▸ sup_le_sup_left hle n), fun h => ?_⟩

    have h1 : n ⊔ (a * q) = ⊤ := (hcop_mul n a q).mpr ⟨h, hnq⟩
    obtain ⟨k, hk⟩ := hca
    rw [hk] at h1
    exact ((hcop_mul n (Q.cond a) k).mp h1).1

  have h1 : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      ∀ n : Ideal (𝓞 F), n ⊔ q = ⊤ →
        ((Q.χ a) n = 0 ↔ n = ⊥ ∨ n ⊔ a ≠ ⊤) := by
    intro a ha haq n hnq
    rw [quadraticFamily_eq_zero_iff Q ha (hsupc a haq) n]
    simp only [ne_eq]
    rw [not_congr (hcond_coprime a ha haq n hnq)]

  have h2 : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b) := by
    intro a b ha haq hb hbq
    by_cases hab : a ⊔ b = ⊤
    · exact Q.reciprocity a b ha (hsupc a haq) hb (hsupc b hbq) hab
    · have hba : b ⊔ a ≠ ⊤ := by rw [sup_comm]; exact hab
      have hza : (Q.χ a) b = 0 := (h1 a ha haq b hbq).mpr (Or.inr hba)
      have hzb : (Q.χ b) a = 0 := (h1 b hb hbq a haq).mpr (Or.inr hab)
      rw [hza, hzb, zero_mul]
  refine ⟨h1, h2, ?_⟩

  intro a b ha haq hb hbq hab hcls
  obtain ⟨ψ, hψprim, hψagree⟩ :=
    Q.product_primitive a b ha (hsupc a haq) hb (hsupc b hbq) hab hcls
  refine ⟨ψ, hψprim, fun n hnq => ?_⟩
  by_cases hcop : n ⊔ (Q.cond a * Q.cond b) = ⊤
  ·
    rw [hψagree n hcop, quadraticFamily_conj Q hb (hsupc b hbq) n]
  ·
    have hcopab : (n ⊔ (a * b) = ⊤) ↔ (n ⊔ (Q.cond a * Q.cond b) = ⊤) := by
      rw [hcop_mul, hcop_mul, hcond_coprime a ha haq n hnq,
        hcond_coprime b hb hbq n hnq]
    have hnotab : n ⊔ (a * b) ≠ ⊤ := fun h => hcop (hcopab.mp h)
    have hψ0 : ψ n = 0 := (RayOperations.eq_zero_iff ψ n).mpr (Or.inr hnotab)
    have hna : n ⊔ a ≠ ⊤ ∨ n ⊔ b ≠ ⊤ := by
      by_cases hna' : n ⊔ a = ⊤
      · right
        intro hnb'
        exact hnotab ((hcop_mul n a b).mpr ⟨hna', hnb'⟩)
      · exact Or.inl hna'
    have hprod0 : (Q.χ a) n * (Q.χ b) n = 0 := by
      rcases hna with h | h
      · rw [(h1 a ha haq n hnq).mpr (Or.inr h), zero_mul]
      · rw [(h1 b hb hbq n hnq).mpr (Or.inr h), mul_zero]
    rw [hψ0, hprod0]

end DedekindZetaZeroFree.LargeSieve
