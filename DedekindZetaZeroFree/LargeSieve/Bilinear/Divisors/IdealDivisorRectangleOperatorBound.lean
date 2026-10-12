module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorIncidenceRectangles

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve.DivisorSeparation

def idealDivisorRectangle (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (S T R U V : Finset (Ideal (𝓞 F)))
    (x y : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ d ∈ S, ∑ e ∈ T, ∑ a ∈ R,
    ‖∑ u ∈ U, ∑ v ∈ V,
      if u ⊔ v = ⊤ ∧ d ∣ u ∧ e ∣ v then
        x u * (starRingEnd ℂ) (y v) * (Q.χ u) a *
          (starRingEnd ℂ) ((Q.χ v) a)
      else 0‖

private lemma rectangle_support_disjoint
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

set_option maxHeartbeats 2000000 in

theorem rectangle_operator_bound
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (S T R U V : Finset (Ideal (𝓞 F)))
    (hU : ∀ u ∈ U, u ≠ ⊥) (hV : ∀ v ∈ V, v ≠ ⊥)
    (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ d ∈ S, ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ u ∈ U,
        if d ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
      UA * (∑ u ∈ U, ‖z u‖ ^ 2))
    (hB : ∀ e ∈ T, ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ v ∈ V,
        if e ∣ v then z v * (Q.χ v) a else 0‖ ^ 2) ≤
      UB * (∑ v ∈ V, ‖z v‖ ^ 2))
    (x y : Ideal (𝓞 F) → ℂ) :
    idealDivisorRectangle F c Q S T R U V x y ^ 2 ≤
      (S.card : ℝ) * (T.card : ℝ) * UA * UB *
        (∑ u ∈ U,
          (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
            ((S.filter (fun d => d ∣ u)).card : ℝ) * ‖x u‖ ^ 2) *
        (∑ v ∈ V,
          (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors v).toFinset.card *
            ((T.filter (fun e => e ∣ v)).card : ℝ) * ‖y v‖ ^ 2) := by
  classical
  let supp : Ideal (𝓞 F) → Finset (Ideal (𝓞 F)) :=
    fun u => (UniqueFactorizationMonoid.normalizedFactors u).toFinset
  let P := U.biUnion supp ∪ V.biUnion supp
  have hpU : ∀ u ∈ U, supp u ⊆ P := by
    intro u hu
    exact Finset.subset_union_left.trans' (Finset.subset_biUnion_of_mem supp hu)
  have hpV : ∀ v ∈ V, supp v ⊆ P := by
    intro v hv
    exact Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem supp hv)
  let s : U → Finset P := fun u => (supp u).subtype (fun p => p ∈ P)
  let t : V → Finset P := fun v => (supp v).subtype (fun p => p ∈ P)
  have hs : ∀ u : U, (s u).card = (supp u).card := by
    intro u
    dsimp [s]
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr (hpU u u.property)]
  have ht : ∀ v : V, (t v).card = (supp v).card := by
    intro v
    dsimp [t]
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr (hpV v v.property)]
  have hdisj : ∀ (u : U) (v : V), Disjoint (s u) (t v) ↔ (u : Ideal (𝓞 F)) ⊔ v = ⊤ := by
    intro u v
    rw [rectangle_support_disjoint (hU u u.property) (hV v v.property)]
    change Disjoint (s u) (t v) ↔ Disjoint (supp u) (supp v)
    simp only [Finset.disjoint_left]
    constructor
    · intro h p hu hv
      exact @h ⟨p, hpU u u.property hu⟩ (Finset.mem_subtype.mpr hu)
        (Finset.mem_subtype.mpr hv)
    · intro h p hu hv
      exact @h p (Finset.mem_subtype.mp hu) (Finset.mem_subtype.mp hv)
  let A : S → R → U → ℂ := fun d a u => if (d : Ideal (𝓞 F)) ∣ u then (Q.χ u) a else 0
  let B : T → R → V → ℂ := fun e a v => if (e : Ideal (𝓞 F)) ∣ v then (Q.χ v) a else 0
  have hAA : ∀ d (z : U → ℂ),
      (∑ a : R, ‖∑ u : U, A d a u * z u‖ ^ 2) ≤ UA * ∑ u : U, ‖z u‖ ^ 2 := by
    intro d z
    let zz : Ideal (𝓞 F) → ℂ := fun u => if hu : u ∈ U then z ⟨u, hu⟩ else 0
    have hz : ∀ u : U, zz u = z u := by intro u; simp [zz, u.property]
    have hh := hA d d.property zz
    rw [← Finset.sum_coe_sort R, ← Finset.sum_coe_sort U] at hh
    simp_rw [← Finset.sum_coe_sort U] at hh
    simpa only [hz, A, ite_mul, mul_ite, zero_mul, mul_zero, mul_comm] using hh
  have hBB : ∀ e (z : V → ℂ),
      (∑ a : R, ‖∑ v : V, B e a v * z v‖ ^ 2) ≤ UB * ∑ v : V, ‖z v‖ ^ 2 := by
    intro e z
    let zz : Ideal (𝓞 F) → ℂ := fun v => if hv : v ∈ V then z ⟨v, hv⟩ else 0
    have hz : ∀ v : V, zz v = z v := by intro v; simp [zz, v.property]
    have hh := hB e e.property zz
    rw [← Finset.sum_coe_sort R, ← Finset.sum_coe_sort V] at hh
    simp_rw [← Finset.sum_coe_sort V] at hh
    simpa only [hz, B, ite_mul, mul_ite, zero_mul, mul_zero, mul_comm] using hh
  have h := DedekindZetaZeroFree.LargeSieve.Vendor.DivisorBlocks.divisor_block_bound s t
    (fun (d : S) (u : U) => (d : Ideal (𝓞 F)) ∣ u)
    (fun (e : T) (v : V) => (e : Ideal (𝓞 F)) ∣ v)
    A B UA UB hUA hUB hAA hBB (fun u => x u) (fun v => y v)
  have hcS : ∀ u : U,
      (Finset.univ.filter (fun d : S => (d : Ideal (𝓞 F)) ∣ u)).card =
      (S.filter (fun d => d ∣ (u : Ideal (𝓞 F)))).card := by
    intro u
    simp only [Finset.card_filter]
    exact Finset.sum_coe_sort _ (fun d => if d ∣ _ then (1 : ℕ) else 0)
  have hcT : ∀ v : V,
      (Finset.univ.filter (fun e : T => (e : Ideal (𝓞 F)) ∣ v)).card =
      (T.filter (fun e => e ∣ (v : Ideal (𝓞 F)))).card := by
    intro v
    simp only [Finset.card_filter]
    exact Finset.sum_coe_sort _ (fun d => if d ∣ _ then (1 : ℕ) else 0)
  simp_rw [hs, ht, hcS, hcT] at h
  have hentry : ∀ (d : S) (e : T) (a : R) (u : U) (v : V),
      (if Disjoint (s u) (t v) then
        (A d a u * (if (d : Ideal (𝓞 F)) ∣ u then x u else 0)) *
          star (B e a v * (if (e : Ideal (𝓞 F)) ∣ v then y v else 0)) else 0) =
      (if (u : Ideal (𝓞 F)) ⊔ v = ⊤ ∧ (d : Ideal (𝓞 F)) ∣ u ∧ (e : Ideal (𝓞 F)) ∣ v then
        x u * (starRingEnd ℂ) (y v) * (Q.χ u) a *
          (starRingEnd ℂ) ((Q.χ v) a) else 0) := by
    intro d e a u v
    simp only [hdisj]
    by_cases huv : (u : Ideal (𝓞 F)) ⊔ v = ⊤ <;>
      by_cases hd : (d : Ideal (𝓞 F)) ∣ u <;>
      by_cases he : (e : Ideal (𝓞 F)) ∣ v <;>
      simp [A, B, huv, hd, he, star_mul, mul_comm, mul_left_comm, mul_assoc]
  simp_rw [hentry] at h
  simp only [Fintype.card_coe] at h
  unfold idealDivisorRectangle
  simp_rw [← Finset.sum_coe_sort V (fun v => _),
    ← Finset.sum_coe_sort U (fun u => _),
    ← Finset.sum_coe_sort R (fun a => _),
    ← Finset.sum_coe_sort T (fun e => _),
    ← Finset.sum_coe_sort S (fun d => _)]
  exact h

end DedekindZetaZeroFree.LargeSieve.Sieve.DivisorSeparation

end
