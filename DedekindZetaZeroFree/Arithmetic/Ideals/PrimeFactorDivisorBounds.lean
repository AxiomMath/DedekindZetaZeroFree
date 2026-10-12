module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

open UniqueFactorizationMonoid

theorem idealDivisorCount_le_normalizedFactors_box
    {F : Type*} [Field F] [NumberField F]
    (A : Ideal (𝓞 F)) (hA : A ≠ ⊥) :
    let m := UniqueFactorizationMonoid.normalizedFactors A
    let S := m.toFinset
    (idealDivisorCount A : ℝ) ≤ ∏ P ∈ S, ((m.count P : ℝ) + 1) := by
  classical
  dsimp only
  set m := UniqueFactorizationMonoid.normalizedFactors A with hm
  set S := m.toFinset with hS
  have hSmem : ∀ P : Ideal (𝓞 F), P ∈ S ↔ 0 < m.count P := by
    intro P
    rw [hS, Multiset.mem_toFinset, Multiset.count_pos]
  have hmemA : ∀ D : Ideal (𝓞 F), D ∈ idealDivisors A → D ∣ A := by
    intro D hD
    rw [idealDivisors, if_neg hA] at hD
    exact (Finset.mem_filter.mp hD).2
  have hne : ∀ D : Ideal (𝓞 F), D ∈ idealDivisors A → D ≠ ⊥ := by
    intro D hD hDb
    have hdvd : Ideal.absNorm D ∣ Ideal.absNorm A := map_dvd Ideal.absNorm (hmemA D hD)
    rw [hDb, Ideal.absNorm_bot] at hdvd
    exact (Ideal.absNorm_eq_zero_iff.not.mpr hA) (Nat.zero_dvd.mp hdvd)
  have hle : ∀ D : Ideal (𝓞 F), D ∈ idealDivisors A →
      UniqueFactorizationMonoid.normalizedFactors D ≤ m := by
    intro D hD
    rw [hm]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors (hne D hD) hA).mp (hmemA D hD)

  have hcoord : ∀ D : Ideal (𝓞 F), D ∈ idealDivisors A →
      ∀ P : {x : Ideal (𝓞 F) // x ∈ S},
        (UniqueFactorizationMonoid.normalizedFactors D).count P.val ≤ m.count P.val := by
    intro D hD P
    exact Multiset.le_iff_count.mp (hle D hD) P.val
  let box := (P : {x : Ideal (𝓞 F) // x ∈ S}) → Fin (m.count P.val + 1)
  let f : {D : Ideal (𝓞 F) // D ∈ idealDivisors A} →
      {x : box // x ∈ (Finset.univ : Finset box)} :=
    fun D => ⟨fun P => ⟨(UniqueFactorizationMonoid.normalizedFactors D.val).count P.val,
        Nat.lt_succ_of_le (hcoord D.val D.property P)⟩, Finset.mem_univ _⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨D₁, hD₁⟩ ⟨D₂, hD₂⟩ heq
    simp only [Subtype.mk.injEq]
    have hpt : ∀ P : {x : Ideal (𝓞 F) // x ∈ S},
        (UniqueFactorizationMonoid.normalizedFactors D₁).count P.val =
          (UniqueFactorizationMonoid.normalizedFactors D₂).count P.val := by
      intro P
      have h2 := congrArg (fun (g : {x : box // x ∈ (Finset.univ : Finset box)}) =>
        (g.val P).val) heq
      simpa [f] using h2
    have hext : UniqueFactorizationMonoid.normalizedFactors D₁ =
        UniqueFactorizationMonoid.normalizedFactors D₂ := by
      rw [Multiset.ext]
      intro P
      by_cases hP : P ∈ S
      · exact hpt ⟨P, hP⟩
      · have h1 : m.count P = 0 := by
          by_contra h
          exact hP ((hSmem P).mpr (Nat.pos_of_ne_zero h))
        have hc₁ := Multiset.le_iff_count.mp (hle D₁ hD₁) P
        have hc₂ := Multiset.le_iff_count.mp (hle D₂ hD₂) P
        rw [h1] at hc₁ hc₂
        rw [Nat.eq_zero_of_le_zero hc₁, Nat.eq_zero_of_le_zero hc₂]
    rw [← Ideal.prod_normalizedFactors_eq_self (hne D₁ hD₁),
      ← Ideal.prod_normalizedFactors_eq_self (hne D₂ hD₂), hext]
  have hcard : idealDivisorCount A ≤ ∏ P ∈ S, (m.count P + 1) := by
    have h1 : (idealDivisors A).card ≤ (Finset.univ : Finset box).card :=
      Finset.card_le_card_of_injective (s := idealDivisors A) (t := Finset.univ) hf_inj
    rw [idealDivisorCount]
    calc (idealDivisors A).card ≤ (Finset.univ : Finset box).card := h1
      _ = Fintype.card box := Finset.card_univ
      _ = ∏ P : {x : Ideal (𝓞 F) // x ∈ S}, (m.count P.val + 1) := by
            rw [Fintype.card_pi]; simp
      _ = ∏ P ∈ S, (m.count P + 1) :=
            (Finset.prod_subtype S (fun x => Iff.rfl) (fun P => m.count P + 1)).symm
  exact_mod_cast hcard

theorem absNorm_eq_prod_normalizedFactors_counts
    {F : Type*} [Field F] [NumberField F]
    (A : Ideal (𝓞 F)) (hA : A ≠ ⊥) :
    let m := UniqueFactorizationMonoid.normalizedFactors A
    let S := m.toFinset
    Ideal.absNorm A = ∏ P ∈ S, Ideal.absNorm P ^ m.count P := by
  classical
  dsimp only
  have h1 : Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors A).prod =
      ((UniqueFactorizationMonoid.normalizedFactors A).map Ideal.absNorm).prod :=
    map_multiset_prod (f := (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ)) _
  calc Ideal.absNorm A
      = Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors A).prod := by
          rw [Ideal.prod_normalizedFactors_eq_self hA]
    _ = ((UniqueFactorizationMonoid.normalizedFactors A).map Ideal.absNorm).prod := h1
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors A).toFinset,
          Ideal.absNorm P ^ (UniqueFactorizationMonoid.normalizedFactors A).count P :=
          Finset.prod_multiset_map_count _ _

theorem two_le_absNorm_of_mem_normalizedFactors
    {F : Type*} [Field F] [NumberField F]
    (A : Ideal (𝓞 F)) (hA : A ≠ ⊥) :
    let m := UniqueFactorizationMonoid.normalizedFactors A
    let S := m.toFinset
    ∀ P ∈ S, 2 ≤ Ideal.absNorm P := by
  classical
  dsimp only
  intro P hP
  have hPrime : Prime P := prime_of_normalized_factor _ (Multiset.mem_toFinset.mp hP)
  rw [Nat.two_le_iff]
  exact ⟨fun h => hPrime.ne_zero (Ideal.absNorm_eq_zero_iff.mp h),
    fun h => hPrime.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))⟩

end DedekindZetaZeroFree.LargeSieve
