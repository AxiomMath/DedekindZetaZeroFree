module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.GcdPairCharacterIdentities
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.PrimitiveProductValues
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterLift

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.PrimitivePhases
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)

structure ReferenceCharacter (u u₀ : Ideal (𝓞 F)) where
  modulus : Ideal (𝓞 F)
  modulus_ne : modulus ≠ ⊥
  modulus_dvd : modulus ∣ u * u₀
  character : DedekindZetaZeroFree.RayClassCharacter F modulus
  self_conj : ∀ z, starRingEnd ℂ (character z) = character z
  norm_le : ∀ z, ‖character z‖ ≤ 1
  comparison : Ideal (𝓞 F)
  comparison_ne : comparison ≠ ⊥
  agree : ∀ z, z ≠ ⊥ → z ⊔ comparison = ⊤ →
    character z = (Q.χ u) z * (Q.χ u₀) z

private theorem reference_character_exists (hc : c ≠ ⊥)
    {u u₀ : Ideal (𝓞 F)} (hu : Squarefree u) (hu₀ : Squarefree u₀)
    (huc : u ⊔ c = ⊤) (hu₀c : u₀ ⊔ c = ⊤)
    (hclass : Q.cls u = Q.cls u₀) : Nonempty (ReferenceCharacter Q u u₀) := by
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, -⟩ := SquarefreeGcd.existsUnique_strip hu hu₀
  obtain ⟨hd, hxsf, hysf, hxy, -, -⟩ :=
    SquarefreeGcd.strip_squarefree_and_coprime hu hu₀ hx hy
  obtain ⟨-, hxc, hyc⟩ := SquarefreeGcd.strip_coprime_aux hu hu₀ hx hy huc hu₀c
  have hcls : Q.cls x = Q.cls y := by
    letI := Q.instGroup
    have ha := congrArg Q.cls hx
    have hb := congrArg Q.cls hy
    have hdc : (u ⊔ u₀) ⊔ c = ⊤ :=
      (SquarefreeGcd.strip_coprime_aux hu hu₀ hx hy huc hu₀c).1
    rw [Q.cls_mul _ _ hdc hxc] at ha
    rw [Q.cls_mul _ _ hdc hyc] at hb
    exact mul_left_cancel (ha.symm.trans (hclass.trans hb))
  obtain ⟨hR, -, ⟨ψ, hψ, hψagree⟩, -, -⟩ :=
    rawGcdPairTransport hc Q hu hu₀ huc hu₀c hclass hx hy
  obtain ⟨ψ', -, hψ'⟩ := Q.product_primitive x y hxsf hxc hysf hyc hxy hcls
  have hquad := primitiveProductQuadratic Q
    (SquarefreeGcd.ne_bot_of_squarefree hxsf)
    (SquarefreeGcd.ne_bot_of_squarefree hysf)
    hxsf hysf hxc hyc hxy hcls ψ' hψ'
  have hxdiv : x ∣ u := ⟨u ⊔ u₀, hx.trans (mul_comm _ _)⟩
  have hydiv : y ∣ u₀ := ⟨u ⊔ u₀, hy.trans (mul_comm _ _)⟩
  let R := c * u * u₀ * Q.cond u * Q.cond u₀ * Q.cond x * Q.cond y
  refine ⟨{ modulus := x*y
            modulus_ne := mul_ne_zero (SquarefreeGcd.ne_bot_of_squarefree hxsf)
              (SquarefreeGcd.ne_bot_of_squarefree hysf)
            modulus_dvd := mul_dvd_mul hxdiv hydiv
            character := ψ'
            self_conj := fun z => (hquad.1 z).1
            norm_le := fun z => (hquad.1 z).2.2.2
            comparison := R
            comparison_ne := hR
            agree := ?_ }⟩
  intro z hz hzc
  have hprod := (rawGcdPairTransport hc Q hu hu₀ huc hu₀c hclass hx hy).2.1 z hz hzc
  have hcond : z ⊔ (Q.cond x * Q.cond y) = ⊤ := by
    apply top_unique
    rw [← hzc]
    apply sup_le_sup_left
    dsimp [R]
    simpa only [mul_assoc] using
      (Ideal.mul_le_right (I := c * u * u₀ * Q.cond u * Q.cond u₀)
        (J := Q.cond x * Q.cond y))
  rw [hψ' z hcond, quadraticFamily_conj Q hysf hyc]
  exact hprod.symm

theorem primitive_pair_phase_separation
    (hc : c ≠ ⊥) (S : Finset (Ideal (𝓞 F)))
    (hS : ∀ u ∈ S, Squarefree u ∧ u ⊔ c = ⊤)
    (hclass : ∀ u ∈ S, ∀ v ∈ S, Q.cls u = Q.cls v) :
    ∃ phase : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ,
      (∀ u ∈ S, ∀ z, ‖phase u z‖ ≤ 1) ∧
      ∀ u ∈ S, ∀ v ∈ S, u ⊔ v = ⊤ →
      ∀ ψ : DedekindZetaZeroFree.RayClassCharacter F (u * v),
        (∀ I, I ⊔ (Q.cond u * Q.cond v) = ⊤ →
          ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I)) →
      ∀ z, z ≠ ⊥ → (∀ b ∈ S, z ⊔ b = ⊤) →
        ψ z = phase u z * star (phase v z) := by
  by_cases hS0 : S.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hS0
    have href : ∀ u ∈ S, Nonempty (ReferenceCharacter Q u u₀) := by
      intro u hu
      exact reference_character_exists Q hc (hS u hu).1 (hS u₀ hu₀).1
        (hS u hu).2 (hS u₀ hu₀).2 (hclass u hu u₀ hu₀)
    let Γ (u : {u : Ideal (𝓞 F) // u ∈ S}) : ReferenceCharacter Q u.val u₀ :=
      Classical.choice (href u.val u.property)
    refine ⟨fun u z => if hu : u ∈ S then (Γ ⟨u, hu⟩).character z else 0, ?_, ?_⟩
    · intro u hu z
      simp only [dif_pos hu]
      exact (Γ ⟨u, hu⟩).norm_le z
    intro u hu v hv huv ψ hψ z hz hzS
    simp only [dif_pos hu, dif_pos hv]
    let m := (u * v) * ((Γ ⟨u, hu⟩).modulus * (Γ ⟨v, hv⟩).modulus)
    have huv0 : u * v ≠ ⊥ := mul_ne_zero
      (SquarefreeGcd.ne_bot_of_squarefree (hS u hu).1)
      (SquarefreeGcd.ne_bot_of_squarefree (hS v hv).1)
    have hmΓ : (Γ ⟨u, hu⟩).modulus * (Γ ⟨v, hv⟩).modulus ≠ ⊥ :=
      mul_ne_zero (Γ ⟨u, hu⟩).modulus_ne (Γ ⟨v, hv⟩).modulus_ne
    have hm : m ≠ ⊥ := mul_ne_zero huv0 hmΓ
    have hdivψ : u * v ∣ m := dvd_mul_right _ _
    have hdivΓ : (Γ ⟨u, hu⟩).modulus * (Γ ⟨v, hv⟩).modulus ∣ m := dvd_mul_left _ _
    let θ := RayOperations.mul (Γ ⟨u, hu⟩).character (Γ ⟨v, hv⟩).character
    let R := (Γ ⟨u, hu⟩).comparison * (Γ ⟨v, hv⟩).comparison *
      (Q.cond u * Q.cond v) * Q.cond u₀
    have hR : R ≠ ⊥ := by
      exact mul_ne_zero (mul_ne_zero
        (mul_ne_zero (Γ ⟨u, hu⟩).comparison_ne (Γ ⟨v, hv⟩).comparison_ne)
        (mul_ne_zero (Q.primitive u (hS u hu).1 (hS u hu).2).1
          (Q.primitive v (hS v hv).1 (hS v hv).2).1))
        (Q.primitive u₀ (hS u₀ hu₀).1 (hS u₀ hu₀).2).1
    have heq := RayComparison.away_uniqueness hm hR
      (Sieve.Initial.liftCharacter hdivψ ψ)
      (Sieve.Initial.liftCharacter hdivΓ θ) (by
        intro I hI hImR
        have hsplit : I ⊔ m = ⊤ ∧ I ⊔ (Γ ⟨u, hu⟩).comparison = ⊤ ∧
            I ⊔ (Γ ⟨v, hv⟩).comparison = ⊤ ∧ I ⊔ Q.cond u = ⊤ ∧
            I ⊔ Q.cond v = ⊤ ∧ I ⊔ Q.cond u₀ = ⊤ := by
          simpa only [m, R, ← Ideal.isCoprime_iff_sup_eq,
            IsCoprime.mul_right_iff, and_assoc] using hImR
        rw [Sieve.Initial.liftCharacter_apply_of_coprime hdivψ ψ I hsplit.1,
          Sieve.Initial.liftCharacter_apply_of_coprime hdivΓ θ I hsplit.1,
          RayOperations.mul_apply,
          (Γ ⟨u, hu⟩).agree I hI hsplit.2.1, (Γ ⟨v, hv⟩).agree I hI hsplit.2.2.1,
          hψ I (by
            simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]
            exact ⟨Ideal.isCoprime_iff_sup_eq.mpr hsplit.2.2.2.1,
              Ideal.isCoprime_iff_sup_eq.mpr hsplit.2.2.2.2.1⟩),
          quadraticFamily_conj Q (hS v hv).1 (hS v hv).2]
        have hsq := quadraticFamily_value_sq_eq_one Q (hS u₀ hu₀).1
          (hS u₀ hu₀).2 I hI hsplit.2.2.2.2.2
        calc
          _ = ((Q.χ u) I * (Q.χ v) I) * 1 := by ring
          _ = ((Q.χ u) I * (Q.χ v) I) * ((Q.χ u₀) I)^2 := by rw [hsq]
          _ = _ := by ring)
    have hzmod : z ⊔ m = ⊤ := by
      have hzu := hzS u hu
      have hzv := hzS v hv
      have hz₀ := hzS u₀ hu₀
      have hzΓ : ∀ b, ∀ hb : b ∈ S, z ⊔ (Γ ⟨b, hb⟩).modulus = ⊤ := by
        intro b hb
        apply top_unique
        have hzprod : z ⊔ b * u₀ = ⊤ := by
          simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]
          exact ⟨Ideal.isCoprime_iff_sup_eq.mpr (hzS b hb),
            Ideal.isCoprime_iff_sup_eq.mpr hz₀⟩
        rw [← hzprod]
        exact sup_le_sup_left (Ideal.dvd_iff_le.mp (Γ ⟨b, hb⟩).modulus_dvd) z
      dsimp [m]
      simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]
      exact ⟨⟨Ideal.isCoprime_iff_sup_eq.mpr hzu,
        Ideal.isCoprime_iff_sup_eq.mpr hzv⟩,
        ⟨Ideal.isCoprime_iff_sup_eq.mpr (hzΓ u hu),
          Ideal.isCoprime_iff_sup_eq.mpr (hzΓ v hv)⟩⟩
    have hzEq := heq z
    rw [Sieve.Initial.liftCharacter_apply_of_coprime hdivψ ψ z hzmod,
      Sieve.Initial.liftCharacter_apply_of_coprime hdivΓ θ z hzmod,
      RayOperations.mul_apply] at hzEq
    simpa only [← starRingEnd_apply, (Γ ⟨v, hv⟩).self_conj z] using hzEq
  · refine ⟨fun _ _ => 0, ?_, ?_⟩ <;>
      intro u hu <;> exact False.elim (hS0 ⟨u, hu⟩)
end DedekindZetaZeroFree.LargeSieve.Bilinear.PrimitivePhases

end
