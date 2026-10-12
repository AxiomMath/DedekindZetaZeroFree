module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.WeightedEnergyAndPrimeSupportCost
public import DedekindZetaZeroFree.LargeSieve.Bilinear.FiniteDisjointSupportInequality

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

private lemma sum_powerset_neg_one_pow_card_C {P : Type*} [DecidableEq P] (A : Finset P) :
    (∑ D ∈ A.powerset, (-1 : ℂ) ^ D.card) = if A = ∅ then 1 else 0 := by
  have h : ((∑ D ∈ A.powerset, (-1 : ℤ) ^ D.card : ℤ) : ℂ) =
      ((if A = ∅ then 1 else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  rw [Int.cast_sum] at h
  simpa using h

private lemma disjoint_indicator_expansion {P : Type*} [DecidableEq P]
    (ambient S T : Finset P) (hS : S ⊆ ambient) (hT : T ⊆ ambient) :
    (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ S ∧ D ⊆ T then 1 else 0)) = if Disjoint S T then 1 else 0 := by
  have hfilter : ambient.powerset.filter (fun D => D ⊆ S ∧ D ⊆ T) = (S ∩ T).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hDS, hDT⟩ x hx
      exact Finset.mem_inter.mpr ⟨hDS hx, hDT hx⟩
    · intro hD
      exact ⟨fun x hx => hS (Finset.mem_inter.mp (hD hx)).1,
        fun x hx => (Finset.mem_inter.mp (hD hx)).1,
        fun x hx => (Finset.mem_inter.mp (hD hx)).2⟩
  have hsum : (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ S ∧ D ⊆ T then 1 else 0))
      = ∑ D ∈ ambient.powerset.filter (fun D => D ⊆ S ∧ D ⊆ T), (-1 : ℂ) ^ D.card := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D _
    split_ifs <;> simp
  rw [hsum, hfilter, sum_powerset_neg_one_pow_card_C]
  by_cases h : S ∩ T = ∅
  · rw [if_pos h, if_pos (Finset.disjoint_iff_inter_eq_empty.mpr h)]
  · rw [if_neg h, if_neg (fun hd => h (Finset.disjoint_iff_inter_eq_empty.mp hd))]

private lemma sum_comm_three {α β γ M : Type*} [AddCommMonoid M]
    (A : Finset α) (B : Finset β) (C : Finset γ) (f : α → β → γ → M) :
    (∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C, f i j k) = ∑ k ∈ C, ∑ i ∈ A, ∑ j ∈ B, f i j k := by
  calc (∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C, f i j k)
      = ∑ j ∈ B, ∑ i ∈ A, ∑ k ∈ C, f i j k := Finset.sum_comm
    _ = ∑ j ∈ B, ∑ k ∈ C, ∑ i ∈ A, f i j k := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = ∑ k ∈ C, ∑ j ∈ B, ∑ i ∈ A, f i j k := Finset.sum_comm
    _ = ∑ k ∈ C, ∑ i ∈ A, ∑ j ∈ B, f i j k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]

private lemma disjoint_expansion_finset {P ι κ : Type*} [DecidableEq P]
    (ambient : Finset P) (S : ι → Finset P) (T : κ → Finset P)
    (U : Finset ι) (V : Finset κ) (z : ι → ℂ) (v : κ → ℂ)
    (hS : ∀ i ∈ U, S i ⊆ ambient) (hT : ∀ j ∈ V, T j ⊆ ambient) :
    (∑ i ∈ U, ∑ j ∈ V, if Disjoint (S i) (T j) then z i * star (v j) else 0) =
      ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        ((∑ i ∈ U, if D ⊆ S i then z i else 0) *
          star (∑ j ∈ V, if D ⊆ T j then v j else 0)) := by
  have hp : ∀ i ∈ U, ∀ j ∈ V,
      (if Disjoint (S i) (T j) then z i * star (v j) else 0) =
        ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          (if D ⊆ S i ∧ D ⊆ T j then z i * star (v j) else 0) := by
    intro i hi j hj
    calc (if Disjoint (S i) (T j) then z i * star (v j) else 0)
        = (if Disjoint (S i) (T j) then (1 : ℂ) else 0) * (z i * star (v j)) := by
          split_ifs <;> simp
      _ = (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
            (if D ⊆ S i ∧ D ⊆ T j then 1 else 0)) * (z i * star (v j)) := by
          rw [disjoint_indicator_expansion ambient (S i) (T j) (hS i hi) (hT j hj)]
      _ = ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
            (if D ⊆ S i ∧ D ⊆ T j then z i * star (v j) else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro D _
          split_ifs <;> ring
  have hcongr : (∑ i ∈ U, ∑ j ∈ V, if Disjoint (S i) (T j) then z i * star (v j) else 0)
      = ∑ i ∈ U, ∑ j ∈ V, ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          (if D ⊆ S i ∧ D ⊆ T j then z i * star (v j) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hp i hi j hj
  rw [hcongr, sum_comm_three]
  apply Finset.sum_congr rfl
  intro D _
  have hstar : star (∑ j ∈ V, if D ⊆ T j then v j else 0)
      = ∑ j ∈ V, if D ⊆ T j then star (v j) else 0 := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hstar, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h1 : D ⊆ S i <;> by_cases h2 : D ⊆ T j <;> simp [h1, h2]

private lemma sup_eq_top_iff_disjoint_normalizedFactors
    {F : Type} [Field F] [NumberField F] {u v : Ideal (𝓞 F)} (hu : u ≠ ⊥) (hv : v ≠ ⊥) :
    u ⊔ v = ⊤ ↔ Disjoint (UniqueFactorizationMonoid.normalizedFactors u).toFinset
      (UniqueFactorizationMonoid.normalizedFactors v).toFinset := by
  constructor
  · intro h
    have hprod : (UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v).prod = 1 := by
      have h1 := Ideal.sup_eq_prod_inf_factors hu hv
      rw [h, ← Ideal.one_eq_top] at h1
      exact h1.symm
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rw [Multiset.mem_toFinset] at hxu hxv
    have hxmem : x ∈ UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v := Multiset.mem_inter.mpr ⟨hxu, hxv⟩
    have hdvd : x ∣ (UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v).prod := Multiset.dvd_prod hxmem
    rw [hprod] at hdvd
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor x hxu).not_isUnit
      (isUnit_of_dvd_one hdvd)
  · intro hd
    rw [Ideal.sup_eq_prod_inf_factors hu hv]
    have hinter : UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx
      exact (Finset.disjoint_left.mp hd (Multiset.mem_toFinset.mpr (Multiset.mem_inter.mp hx).1))
        (Multiset.mem_toFinset.mpr (Multiset.mem_inter.mp hx).2)
    rw [hinter, Multiset.prod_zero, Ideal.one_eq_top]

theorem coprime_form_bound
    {F : Type} [Field F] [NumberField F] {R : Type*}
    (rows : Finset R) (cols : Finset (Ideal (𝓞 F)))
    (hcols : ∀ u ∈ cols, u ≠ ⊥)
    (w : R → ℝ) (hw : ∀ r ∈ rows, 0 ≤ w r)
    (A : R → Ideal (𝓞 F) → ℂ)
    (U : ℝ) (hU : 0 ≤ U)
    (henergy : ∀ alpha : Ideal (𝓞 F) → ℂ,
      weightedEnergy rows cols w A alpha ≤ U * ∑ u ∈ cols, ‖alpha u‖ ^ 2)
    (alpha : Ideal (𝓞 F) → ℂ) :
    ‖coprimeForm rows cols w A alpha‖ ≤
      U * ∑ u ∈ cols, primeSupportCost u * ‖alpha u‖ ^ 2 := by
  classical
  set s : Ideal (𝓞 F) → Finset (Ideal (𝓞 F)) :=
    fun u => (UniqueFactorizationMonoid.normalizedFactors u).toFinset with hs
  set ambient : Finset (Ideal (𝓞 F)) := cols.biUnion s with hambient
  have hamb : ∀ u ∈ cols, s u ⊆ ambient := by
    intro u hu
    rw [hambient]
    exact Finset.subset_biUnion_of_mem s hu
  have hdisj : ∀ u ∈ cols, ∀ v ∈ cols, (u ⊔ v = ⊤ ↔ Disjoint (s u) (s v)) := by
    intro u hu v hv
    simpa only [hs] using sup_eq_top_iff_disjoint_normalizedFactors (hcols u hu) (hcols v hv)

  have hinner : ∀ r : R,
      (∑ u ∈ cols, ∑ v ∈ cols,
          if u ⊔ v = ⊤ then (A r u * alpha u) * star (A r v * alpha v) else 0)
      = ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          ((∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)) *
           star (∑ v ∈ cols, A r v * (if D ⊆ s v then alpha v else 0))) := by
    intro r
    have hb := disjoint_expansion_finset ambient s s cols cols
      (fun u => A r u * alpha u) (fun v => A r v * alpha v) hamb hamb
    have hL : (∑ u ∈ cols, ∑ v ∈ cols,
          if Disjoint (s u) (s v) then (A r u * alpha u) * star (A r v * alpha v) else 0)
        = ∑ u ∈ cols, ∑ v ∈ cols,
          if u ⊔ v = ⊤ then (A r u * alpha u) * star (A r v * alpha v) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact if_congr (hdisj u hu v hv).symm rfl rfl
    have hR : (∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          ((∑ u ∈ cols, if D ⊆ s u then A r u * alpha u else 0) *
           star (∑ v ∈ cols, if D ⊆ s v then A r v * alpha v else 0)))
        = ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          ((∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)) *
           star (∑ v ∈ cols, A r v * (if D ⊆ s v then alpha v else 0))) := by
      apply Finset.sum_congr rfl
      intro D _
      have h1 : (∑ u ∈ cols, if D ⊆ s u then A r u * alpha u else 0)
          = ∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [mul_ite]
        simp
      rw [h1]
    rw [hL] at hb
    rw [hR] at hb
    exact hb
  have hcf : coprimeForm rows cols w A alpha
      = ∑ r ∈ rows, (w r : ℂ) * ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          ((∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)) *
           star (∑ v ∈ cols, A r v * (if D ⊆ s v then alpha v else 0))) := by
    unfold coprimeForm
    apply Finset.sum_congr rfl
    intro r _
    rw [hinner r]

  have hA : ‖∑ r ∈ rows, (w r : ℂ) * ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
        ((∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)) *
         star (∑ v ∈ cols, A r v * (if D ⊆ s v then alpha v else 0)))‖
      ≤ ∑ r ∈ rows, ∑ D ∈ ambient.powerset,
          w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2 := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => ?_))
    rw [norm_mul, Complex.norm_of_nonneg (hw r hr)]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw r hr)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D _ => ?_))
    rw [norm_mul, show ‖(-1 : ℂ) ^ D.card‖ = 1 by simp, one_mul, norm_mul, norm_star,
      pow_two]
  have hB : ∑ r ∈ rows, ∑ D ∈ ambient.powerset,
        w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2
      = ∑ D ∈ ambient.powerset, ∑ r ∈ rows,
        w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2 :=
    Finset.sum_comm

  have hstep2 : ∀ D : Finset (Ideal (𝓞 F)), ∑ r ∈ rows, w r *
        ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2
      ≤ U * ∑ u ∈ cols, ‖(if D ⊆ s u then alpha u else 0)‖ ^ 2 := by
    intro D
    have hb := henergy (fun u => if D ⊆ s u then alpha u else 0)
    simpa only [weightedEnergy] using hb
  have hC : ∑ D ∈ ambient.powerset, ∑ r ∈ rows,
        w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2
      ≤ ∑ D ∈ ambient.powerset, U * ∑ u ∈ cols,
        ‖(if D ⊆ s u then alpha u else 0)‖ ^ 2 :=
    Finset.sum_le_sum (fun D _ => hstep2 D)

  have hcost : ∀ u ∈ cols, (∑ D ∈ ambient.powerset, (if D ⊆ s u then (1 : ℝ) else 0))
      = (2 : ℝ) ^ (s u).card := by
    intro u hu
    rw [Finset.sum_boole]
    have hfil : ambient.powerset.filter (fun D => D ⊆ s u) = (s u).powerset := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨fun x hx => hamb u hu (h hx), h⟩⟩
    rw [hfil, Finset.card_powerset, Nat.cast_pow]
    norm_num
  have hD : ∑ D ∈ ambient.powerset, U * ∑ u ∈ cols,
        ‖(if D ⊆ s u then alpha u else 0)‖ ^ 2
      = U * ∑ u ∈ cols, (2 : ℝ) ^ (s u).card * ‖alpha u‖ ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    have hterm : ∀ D : Finset (Ideal (𝓞 F)),
        ‖(if D ⊆ s u then alpha u else 0)‖ ^ 2
          = (if D ⊆ s u then (1 : ℝ) else 0) * ‖alpha u‖ ^ 2 := by
      intro D
      by_cases h : D ⊆ s u <;> simp [h]
    simp_rw [hterm]
    rw [← Finset.sum_mul, hcost u hu]
  calc ‖coprimeForm rows cols w A alpha‖
      = ‖∑ r ∈ rows, (w r : ℂ) * ∑ D ∈ ambient.powerset, (-1 : ℂ) ^ D.card *
          ((∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)) *
           star (∑ v ∈ cols, A r v * (if D ⊆ s v then alpha v else 0)))‖ := by
        rw [hcf]
    _ ≤ ∑ r ∈ rows, ∑ D ∈ ambient.powerset,
          w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2 := hA
    _ = ∑ D ∈ ambient.powerset, ∑ r ∈ rows,
          w r * ‖∑ u ∈ cols, A r u * (if D ⊆ s u then alpha u else 0)‖ ^ 2 := hB
    _ ≤ ∑ D ∈ ambient.powerset, U * ∑ u ∈ cols,
          ‖(if D ⊆ s u then alpha u else 0)‖ ^ 2 := hC
    _ = U * ∑ u ∈ cols, (2 : ℝ) ^ (s u).card * ‖alpha u‖ ^ 2 := hD
    _ = U * ∑ u ∈ cols, primeSupportCost u * ‖alpha u‖ ^ 2 := by
        simp only [primeSupportCost, hs]

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end
