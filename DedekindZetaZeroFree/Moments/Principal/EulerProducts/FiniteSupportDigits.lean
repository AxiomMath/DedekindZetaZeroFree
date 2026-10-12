module
public import Mathlib.Analysis.Normed.Group.InfiniteSum

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

namespace DedekindZetaZeroFree.FinsuppEulerProduct

abbrev Digit := ℕ × ℕ × ℕ × ℕ

noncomputable def coefficient {P : Type*} [DecidableEq P]
    (a : P → Digit → ℂ) (d : P →₀ Digit) : ℂ :=
  ∏ p ∈ d.support, a p (d p)

theorem local_norm_summable {P : Type*} [DecidableEq P]
    (a : P → Digit → ℂ) (hzero : ∀ p, a p 0 = 1)
    (hsum : Summable (fun d : P →₀ Digit => ‖coefficient a d‖)) (p : P) :
    Summable (fun δ : Digit => ‖a p δ‖) := by
  have h := hsum.comp_injective (Finsupp.single_injective p)
  change Summable (fun δ => ‖(Finsupp.single p δ).prod a‖) at h
  simpa only [Finsupp.prod_single_index (hzero p)] using h

universe u
def PiSpec (I : Type u) [Fintype I] : Prop :=
  ∀ a : I → Digit → ℂ,
    (∀ i, Summable (fun d => ‖a i d‖)) →
    Summable (fun f : I → Digit => ‖∏ i, a i (f i)‖) ∧
    HasSum (fun f : I → Digit => ∏ i, a i (f i)) (∏ i, ∑' d, a i d)
private theorem finite_pi (I : Type u) [Fintype I] : PiSpec I := by
  classical
  apply Fintype.induction_empty_option (P := PiSpec)
  · intro I J inst e ih a h
    letI : Fintype I := Fintype.ofEquiv J e.symm
    let E := Equiv.piCongrLeft (fun _ : J => Digit) e
    obtain ⟨hs, ht⟩ := ih (fun i => a (e i)) (fun i => h (e i))
    have he : ∀ f, (∏ j, a j (E f j)) = ∏ i, a (e i) (f i) := by
      intro f
      rw [← e.prod_comp]
      congr 1
      ext i
      simp [E]
    constructor
    · apply E.summable_iff.mp
      simpa only [Function.comp_def, he] using hs
    · apply E.hasSum_iff.mp
      rw [Function.comp_def]
      simp_rw [he]
      convert ht using 1
      exact (e.prod_comp (fun j => ∑' d, a j d)).symm
  · intro a h
    constructor
    · exact summable_of_finite_support (Set.toFinite _)
    · simp
  · intro I _ ih a h
    obtain ⟨hs, ht⟩ := ih (fun i => a (some i)) (fun i => h (some i))
    let E := (Equiv.piOptionEquivProd (α := I) (β := fun _ => Digit)).symm
    have he : ∀ x, (∏ i, a i (E x i)) = a none x.1 * ∏ i, a (some i) (x.2 i) := by
      intro x
      simp [E, Fintype.prod_option]
    constructor
    · apply E.summable_iff.mp
      simpa only [Function.comp_def, he] using (h none).mul_norm hs
    · apply E.hasSum_iff.mp
      simp only [Function.comp_def, he, Fintype.prod_option]
      have hh : Summable (fun x : Digit × (I → Digit) =>
          a none x.1 * ∏ i, a (some i) (x.2 i)) :=
        summable_mul_of_summable_norm (f := a none)
          (g := fun f : I → Digit => ∏ i, a (some i) (f i)) (h none) hs
      have H := (h none).of_norm.hasSum.mul ht hh
      exact H

noncomputable def supportEquiv {P : Type*} [DecidableEq P] (s : Finset P) :
    {d : P →₀ Digit // d.support ⊆ s} ≃ (s → Digit) :=
  (Equiv.subtypeEquivRight (fun d => by simp only [Finset.coe_subset])).trans
    ((Finsupp.restrictSupportEquiv (s : Set P) Digit).trans Finsupp.equivFunOnFinite)

private theorem supportEquiv_coeff {P : Type*} [DecidableEq P] (s : Finset P)
    (a : P → Digit → ℂ) (hzero : ∀ p, a p 0 = 1) (f : s → Digit) :
    coefficient a ((supportEquiv s).symm f).1 = ∏ p : s, a p (f p) := by
  classical
  let d := ((supportEquiv s).symm f).1
  have hd : d.support ⊆ s := ((supportEquiv s).symm f).2
  have he : ∀ p : s, d p = f p := by
    intro p
    change ((Finsupp.restrictSupportEquiv (s : Set P) Digit).symm
      (Finsupp.equivFunOnFinite.symm f)).1 p = f p
    rw [Finsupp.restrictSupportEquiv_symm_apply_coe]
    simp [Finsupp.extendDomain_apply]
  unfold coefficient
  rw [Finset.prod_subset hd (fun p hp hdp => ?_)]
  · rw [← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl (fun p _ => congrArg (a p) (he p))
  · rw [Finsupp.notMem_support_iff.mp hdp, hzero]

private theorem finite_prod_eq {P : Type*} [DecidableEq P]
    (a : P → Digit → ℂ) (hzero : ∀ p, a p 0 = 1)
    (hsum : Summable (fun d : P →₀ Digit => ‖coefficient a d‖)) (s : Finset P) :
    (∏ p ∈ s, ∑' δ : Digit, a p δ) =
      ∑' d : {d : P →₀ Digit // d.support ⊆ s}, coefficient a d.1 := by
  classical
  have ht := (finite_pi s) (fun p δ => a p δ)
    (fun p => local_norm_summable a hzero hsum p)
  have H : HasSum (fun d : {d : P →₀ Digit // d.support ⊆ s} => coefficient a d.1)
      (∏ p : s, ∑' δ : Digit, a p δ) := by
    apply (supportEquiv s).symm.hasSum_iff.mp
    simpa only [Function.comp_def, supportEquiv_coeff s a hzero] using ht.2
  rw [← Finset.prod_coe_sort s]
  exact H.tsum_eq.symm

theorem hasProd {P : Type*} [DecidableEq P]
    (a : P → Digit → ℂ) (hzero : ∀ p, a p 0 = 1)
    (hsum : Summable (fun d : P →₀ Digit => ‖coefficient a d‖)) :
    HasProd (fun p => ∑' δ : Digit, a p δ)
      (∑' d : P →₀ Digit, coefficient a d) := by
  classical
  open Filter in
    have H : Tendsto
        (fun s : Finset P => ∑' d : P →₀ Digit,
          if d.support ⊆ s then coefficient a d else 0)
        atTop (nhds (∑' d : P →₀ Digit, coefficient a d)) := by
      apply tendsto_tsum_of_dominated_convergence hsum
      · intro d
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop d.support] with s hs
        simp [hs]
      · apply Eventually.of_forall
        intro s d
        split_ifs <;> simp
    change Tendsto _ atTop _
    convert H using 1
    ext s
    rw [finite_prod_eq a hzero hsum s]
    have ht := tsum_subtype {d : P →₀ Digit | d.support ⊆ s} (coefficient a)
    simp only [Set.indicator, Set.mem_setOf_eq] at ht
    convert ht using 1
    exact (Equiv.subtypeEquivRight (fun d : P →₀ Digit =>
      (Iff.rfl : (d.support ⊆ s) ↔ d ∈ {d : P →₀ Digit | d.support ⊆ s}))).tsum_eq
      (fun d => coefficient a d.1)

end DedekindZetaZeroFree.FinsuppEulerProduct
