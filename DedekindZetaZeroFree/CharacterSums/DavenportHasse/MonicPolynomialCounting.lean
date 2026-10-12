module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.WeightedMonicPolynomials

@[expose] public section

open Polynomial UniqueFactorizationMonoid

namespace DavenportHasse.PolyPart

open scoped Classical

set_option linter.unusedSectionVars false

variable {k : Type*} [Field k] [Fintype k]

lemma divisors_reindex {M : Type*} [AddCommMonoid M] (n : ℕ) (H : ℕ → ℕ → M) :
    ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors, H d (m / d) =
      ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, if d * j ≤ n then H d j else 0 := by
  simp_rw [← Nat.sum_divisorsAntidiagonal H]
  rw [← Finset.sum_product' (f := fun d j => if d * j ≤ n then H d j else 0),
    ← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 * x.2)
    (t := Finset.Icc 1 n)]
  · refine Finset.sum_congr rfl fun m hm => Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.mem_Icc] at hm
    ext ⟨x, y⟩
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨rfl, -⟩
      have hx : x ≠ 0 := by rintro rfl; omega
      have hy : y ≠ 0 := by rintro rfl; omega
      have h1 : x ≤ x * y := Nat.le_mul_of_pos_right x (by omega)
      have h2 : y ≤ x * y := Nat.le_mul_of_pos_left y (by omega)
      omega
    · intro h
      omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    refine ⟨Nat.mul_pos (by omega) (by omega), hx.2⟩

noncomputable def MonLe (k : Type*) [Field k] [Fintype k] (n : ℕ) : Finset k[X] :=
  (Finset.Icc 1 n).biUnion (Mon k)

lemma sum_MonLe {M : Type*} [AddCommMonoid M] (n : ℕ) (G : k[X] → M) :
    ∑ d ∈ Finset.Icc 1 n, ∑ P ∈ Mon k d, G P = ∑ P ∈ MonLe k n, G P := by
  unfold MonLe
  rw [Finset.sum_biUnion]
  intro d _ e _ hde
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro P h1 h2
  exact hde ((mem_Mon.1 h1).2.symm.trans (mem_Mon.1 h2).2)

lemma mem_nf_monic {f P : k[X]} (h : P ∈ normalizedFactors f) : P.Monic := by
  have h0 : P ≠ 0 := (irreducible_of_normalized_factor P h).ne_zero
  rw [← normalize_eq_self_iff_monic h0]
  exact normalize_normalized_factor P h

lemma natDegree_eq_sum_count {f : k[X]} (hf : f.Monic) :
    ∑ P ∈ (normalizedFactors f).toFinset, (normalizedFactors f).count P * P.natDegree =
      f.natDegree := by
  have h := Finset.sum_multiset_map_count (normalizedFactors f) natDegree
  simp only [smul_eq_mul] at h
  rw [← h, ← natDegree_multiset_prod]
  · exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated
      (prod_normalizedFactors hf.ne_zero))
  · intro h0
    exact (irreducible_of_normalized_factor _ h0).ne_zero rfl

lemma pow_dvd_iff_le_count {f P : k[X]} (hf : f.Monic) (hP : P ∈ normalizedFactors f) (j : ℕ) :
    P ^ j ∣ f ↔ j ≤ (normalizedFactors f).count P := by
  have hirr := irreducible_of_normalized_factor P hP
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hirr.ne_zero) hf.ne_zero,
    hirr.normalizedFactors_pow, normalize_normalized_factor P hP,
    Multiset.le_count_iff_replicate_le]

lemma core {f : k[X]} (hf : f.Monic) :
    ∑ d ∈ Finset.Icc 1 f.natDegree, ∑ j ∈ Finset.Icc 1 f.natDegree, ∑ P ∈ Mon k d,
      (if Irreducible P ∧ P ^ j ∣ f then d else 0) = f.natDegree := by
  set n := f.natDegree
  set NF := (normalizedFactors f).toFinset
  rw [Finset.sum_comm]
  have step : ∀ j ∈ Finset.Icc 1 n,
      ∑ d ∈ Finset.Icc 1 n, ∑ P ∈ Mon k d, (if Irreducible P ∧ P ^ j ∣ f then d else 0) =
        ∑ P ∈ NF, if P ^ j ∣ f then P.natDegree else 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun P hP =>
      (show (if Irreducible P ∧ P ^ j ∣ f then d else 0) =
        if Irreducible P ∧ P ^ j ∣ f then P.natDegree else 0 by rw [(mem_Mon.1 hP).2]),
      sum_MonLe]
    symm
    rw [Finset.sum_congr rfl fun P hP => (show (if P ^ j ∣ f then P.natDegree else 0) =
        if Irreducible P ∧ P ^ j ∣ f then P.natDegree else 0 by
      simp [irreducible_of_normalized_factor P (Multiset.mem_toFinset.1 hP)])]
    refine Finset.sum_subset ?_ ?_
    · intro P hP
      rw [Multiset.mem_toFinset] at hP
      have hirr := irreducible_of_normalized_factor P hP
      have hm := mem_nf_monic hP
      unfold MonLe
      rw [Finset.mem_biUnion]
      refine ⟨P.natDegree, ?_, mem_Mon.2 ⟨hm, rfl⟩⟩
      rw [Finset.mem_Icc]
      exact ⟨hirr.natDegree_pos, natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hP)
        hf.ne_zero⟩
    · intro P hP hPNF
      refine ite_eq_right_iff.2 fun ⟨hirr, hdvd⟩ => absurd ?_ hPNF
      unfold MonLe at hP
      obtain ⟨d, -, hd⟩ := Finset.mem_biUnion.1 hP
      have hm := (mem_Mon.1 hd).1
      obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf.ne_zero hirr
        ((dvd_pow_self P (by omega)).trans hdvd)
      rw [eq_of_monic_of_associated hm (mem_nf_monic hq) hassoc]
      exact Multiset.mem_toFinset.2 hq
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Eq.trans ?_ (natDegree_eq_sum_count hf)
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' := Multiset.mem_toFinset.1 hP
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.Icc 1 n).filter (fun j => P ^ j ∣ f) =
      Finset.Icc 1 ((normalizedFactors f).count P) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, pow_dvd_iff_le_count hf hP']
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      have hd := natDegree_le_of_dvd ((pow_dvd_iff_le_count hf hP' j).2 h2) hf.ne_zero
      rw [natDegree_pow] at hd
      have := (irreducible_of_normalized_factor P hP').natDegree_pos
      nlinarith
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]

end DavenportHasse.PolyPart
