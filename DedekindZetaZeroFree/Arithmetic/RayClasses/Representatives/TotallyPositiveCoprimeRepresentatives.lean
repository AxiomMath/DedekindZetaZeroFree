module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.TotallyPositiveResidueRepresentatives

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

private lemma mem_factors_toFinset_iff {F : Type} [Field F] [NumberField F]
    {I P : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hP : Prime P) :
    P ∈ (UniqueFactorizationMonoid.factors I).toFinset ↔ I ≤ P := by
  rw [Multiset.mem_toFinset, UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    Ideal.mem_normalizedFactors_iff hI]
  exact ⟨fun h => h.2, fun h => ⟨Ideal.isPrime_of_prime hP, h⟩⟩

private theorem exists_coprime_residue (F : Type) [Field F] [NumberField F]
    (m q : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hq : q ≠ ⊥) (a : 𝓞 F)
    (ha : Ideal.span {a} ⊔ m = ⊤) :
    ∃ b0 : 𝓞 F, b0 - a ∈ m ∧ Ideal.span {b0} ⊔ (m * q) = ⊤ := by
  classical
  set fm : Multiset (Ideal (𝓞 F)) := UniqueFactorizationMonoid.factors m with hfm
  set fq : Multiset (Ideal (𝓞 F)) := UniqueFactorizationMonoid.factors q with hfq
  set s : Finset (Ideal (𝓞 F)) := fm.toFinset ∪ fq.toFinset with hs
  let e : Ideal (𝓞 F) → ℕ := fun P => if P ∈ fm.toFinset then fm.count P else fq.count P
  let x : Ideal (𝓞 F) → 𝓞 F := fun P => if P ∈ fm.toFinset then a else 1
  have hprime : ∀ P ∈ s, Prime P := by
    intro P hP
    rw [hs] at hP
    rcases Finset.mem_union.mp hP with h | h
    · exact UniqueFactorizationMonoid.prime_of_factor P (Multiset.mem_toFinset.mp h)
    · exact UniqueFactorizationMonoid.prime_of_factor P (Multiset.mem_toFinset.mp h)
  obtain ⟨b0, hb0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (R := 𝓞 F) (s := s) (fun P => P) e hprime (fun i _ j _ hij => hij) (fun P => x P)
  have hm_eq : (∏ P ∈ fm.toFinset, P ^ fm.count P) = m := by
    have h := UniqueFactorizationMonoid.factors_pow_count_prod (x := m) hm
    simp only [← hfm] at h
    exact associated_iff_eq.mp h
  have hb0' : ∀ i ∈ s, b0 - (if i ∈ fm.toFinset then a else 1) ∈
      i ^ (if i ∈ fm.toFinset then fm.count i else fq.count i) := by
    intro i hi
    simpa only [x, e] using hb0 i hi
  have key : ∀ P ∈ fm.toFinset, b0 - a ∈ P ^ fm.count P := by
    intro P hP
    have h := hb0' P (by rw [hs]; exact Finset.mem_union_left _ hP)
    rw [show (if P ∈ fm.toFinset then a else (1 : 𝓞 F)) = a from if_pos hP,
      show (if P ∈ fm.toFinset then fm.count P else fq.count P) = fm.count P from
        if_pos hP] at h
    exact h
  have hpair : (↑fm.toFinset : Set (Ideal (𝓞 F))).Pairwise
      (Function.onFun IsCoprime fun P => P ^ fm.count P) := by
    intro P hP Q hQ hPQ
    have hPP : Prime P := UniqueFactorizationMonoid.prime_of_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_coe.mp hP))
    have hQQ : Prime Q := UniqueFactorizationMonoid.prime_of_factor Q
      (Multiset.mem_toFinset.mp (Finset.mem_coe.mp hQ))
    have hsup : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne
      (Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hPP) hPP.ne_zero)
      (Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hQQ) hQQ.ne_zero) hPQ
    exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top hsup)
  have h1 : b0 - a ∈ m := by
    rw [← hm_eq]
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair]
    simp only [Submodule.mem_iInf]
    exact fun P hP => key P hP
  have hspan_m : Ideal.span {b0} ⊔ m = ⊤ := by
    have hlt : Ideal.span {b0} ≤ Ideal.span {a} ⊔ m := by
      rw [Ideal.span_singleton_le_iff_mem]
      have : b0 = a + (b0 - a) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span (Set.mem_singleton a)) h1
    have hgt : Ideal.span {a} ≤ Ideal.span {b0} ⊔ m := by
      rw [Ideal.span_singleton_le_iff_mem]
      have : a = b0 - (b0 - a) := by ring
      rw [this]
      exact Submodule.sub_mem_sup (Ideal.subset_span (Set.mem_singleton b0)) h1
    have heq : Ideal.span {b0} ⊔ m = Ideal.span {a} ⊔ m :=
      le_antisymm (sup_le hlt le_sup_right) (sup_le hgt le_sup_right)
    rw [heq, ha]
  refine ⟨b0, h1, ?_⟩
  by_contra hne
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hne
  have hb0M : b0 ∈ M := hMle (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton b0)))
  have hmqM : m * q ≤ M := le_trans le_sup_right hMle
  have hMbot : M ≠ ⊥ := by
    intro h
    exact mul_ne_zero hm hq (le_bot_iff.mp (h ▸ hmqM))
  have hMprime : Prime M := (Ideal.prime_iff_isPrime hMbot).mpr hMmax.isPrime
  have hMdvd : M ∣ m * q := Ideal.dvd_iff_le.mpr hmqM
  rcases (hMprime.dvd_mul).mp hMdvd with hMm | hMq
  · refine hMmax.ne_top (top_le_iff.mp ?_)
    rw [← hspan_m]
    exact sup_le ((Ideal.span_singleton_le_iff_mem M).mpr hb0M) (Ideal.dvd_iff_le.mp hMm)
  · by_cases hMem : M ∈ fm.toFinset
    · have hMm' : m ≤ M := (mem_factors_toFinset_iff hm hMprime).mp hMem
      exact hMmax.ne_top (top_le_iff.mp (by
        rw [← hspan_m]
        exact sup_le ((Ideal.span_singleton_le_iff_mem M).mpr hb0M) hMm'))
    · have hMfq : M ∈ fq.toFinset := by
        rw [hfq]
        exact (mem_factors_toFinset_iff hq hMprime).mpr (Ideal.dvd_iff_le.mp hMq)
      have h := hb0' M (by rw [hs]; exact Finset.mem_union_right _ hMfq)
      rw [show (if M ∈ fm.toFinset then a else (1 : 𝓞 F)) = 1 from if_neg hMem,
        show (if M ∈ fm.toFinset then fm.count M else fq.count M) = fq.count M from
          if_neg hMem] at h
      have hcount : 1 ≤ fq.count M := by
        rw [hfq]
        exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (hfq ▸ hMfq))
      have hle : M ^ fq.count M ≤ M := by
        simpa using Ideal.pow_le_pow_right (I := M) hcount
      have h1M : (1 : 𝓞 F) ∈ M := by
        have : b0 - (b0 - (1 : 𝓞 F)) ∈ M := Ideal.sub_mem M hb0M (hle h)
        simpa using this
      exact hMmax.ne_top (Ideal.eq_top_iff_one M |>.mpr h1M)

theorem exists_totallyPositive_coprime_residue (F : Type) [Field F] [NumberField F]
    (m q : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hq : q ≠ ⊥) (a : 𝓞 F)
    (ha : Ideal.span {a} ⊔ m = ⊤) :
    ∃ b : 𝓞 F, b ≠ 0 ∧ b - a ∈ m ∧ Ideal.span {b} ⊔ (m * q) = ⊤ ∧
      (∀ φ : F →+* ℝ, 0 < φ (b : F)) := by
  classical
  obtain ⟨b0, hb0a, hb0cop⟩ := exists_coprime_residue F m q hm hq a ha
  obtain ⟨b, hbne, hbshift, hbpos⟩ :=
    exists_totallyPositive_residue F (m * q) (mul_ne_zero hm hq) b0
  refine ⟨b, hbne, ?_, ?_, hbpos⟩
  · have : b - a = (b - b0) + (b0 - a) := by ring
    rw [this]
    exact Ideal.add_mem m (Ideal.mul_le_left hbshift) hb0a
  · have hlt : Ideal.span {b} ≤ Ideal.span {b0} ⊔ (m * q) := by
      rw [Ideal.span_singleton_le_iff_mem]
      have : b = b0 + (b - b0) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span (Set.mem_singleton b0)) hbshift
    have hgt : Ideal.span {b0} ≤ Ideal.span {b} ⊔ (m * q) := by
      rw [Ideal.span_singleton_le_iff_mem]
      have : b0 = b - (b - b0) := by ring
      rw [this]
      exact Submodule.sub_mem_sup (Ideal.subset_span (Set.mem_singleton b)) hbshift
    have heq : Ideal.span {b} ⊔ (m * q) = Ideal.span {b0} ⊔ (m * q) :=
      le_antisymm (sup_le hlt le_sup_right) (sup_le hgt le_sup_right)
    rw [heq, hb0cop]

end DedekindZetaZeroFree.LargeSieve
