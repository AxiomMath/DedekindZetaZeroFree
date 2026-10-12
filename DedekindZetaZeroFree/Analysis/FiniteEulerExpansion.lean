module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.IdealEuler

open scoped Classical

universe u

private lemma finsupp_pow_single {P : Type u} (w : (P →₀ ℕ) → ℂ)
    (hzero : w 0 = 1) (hadd : ∀ e d, w (e + d) = w e * w d) (p : P) (n : ℕ) :
    w (Finsupp.single p n) = w (Finsupp.single p 1) ^ n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hstep : Finsupp.single p (n + 1) = Finsupp.single p n + Finsupp.single p 1 :=
      Finsupp.single_add p n 1
    rw [hstep, hadd, ih, pow_succ]

noncomputable def supportedEraseEquiv {P : Type u} [DecidableEq P] (p : P)
    (S : Finset P) (hp : p ∉ S) :
    {e : P →₀ ℕ // e.support ⊆ insert p S} ≃ ℕ × {d : P →₀ ℕ // d.support ⊆ S} where
  toFun e := (e.val p, ⟨e.val.erase p, by
    intro x hx
    rw [Finsupp.support_erase, Finset.mem_erase] at hx
    obtain ⟨hxp, hxs⟩ := hx
    rcases Finset.mem_insert.mp (e.property hxs) with h | h
    · exact absurd h hxp
    · exact h⟩)
  invFun x := ⟨Finsupp.single p x.1 + x.2.val, by
    intro q hq
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      exact Finset.mem_insert_self p S
    · exact Finset.mem_insert_of_mem (x.2.property h)⟩
  left_inv e := by
    apply Subtype.ext
    show Finsupp.single p (e.val p) + e.val.erase p = e.val
    exact Finsupp.single_add_erase p e.val
  right_inv x := by
    apply Prod.ext
    · show (Finsupp.single p x.1 + x.2.val) p = x.1
      have hz : x.2.val p = 0 := by
        by_contra h
        exact hp (x.2.property (Finsupp.mem_support_iff.mpr h))
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hz, add_zero]
    · apply Subtype.ext
      show (Finsupp.single p x.1 + x.2.val).erase p = x.2.val
      rw [Finsupp.erase_add, Finsupp.erase_single, zero_add,
        Finsupp.erase_of_notMem_support (fun h => hp (x.2.property h))]

private lemma supportedEraseEquiv_symm_apply {P : Type u} [DecidableEq P] (p : P)
    (S : Finset P) (hp : p ∉ S) (x : ℕ × {d : P →₀ ℕ // d.support ⊆ S}) :
    ((supportedEraseEquiv p S hp).symm x).val = Finsupp.single p x.1 + x.2.val := rfl

theorem finsupp_generator_norm_lt_one {P : Type u} (w : (P →₀ ℕ) → ℂ)
    (hzero : w 0 = 1) (hadd : ∀ e d, w (e + d) = w e * w d)
    (habs : Summable (fun e => ‖w e‖)) (p : P) :
    ‖w (Finsupp.single p 1)‖ < 1 := by
  classical
  have h1 : Summable (fun n : ℕ => w (Finsupp.single p n)) :=
    (habs.of_norm).comp_injective (Finsupp.single_injective p)
  have hf : (fun n : ℕ => w (Finsupp.single p n))
      = fun n => w (Finsupp.single p 1) ^ n :=
    funext (finsupp_pow_single w hzero hadd p)
  rw [hf] at h1
  exact summable_geometric_iff_norm_lt_one.mp h1

theorem hasSum_finsupp_supported {P : Type u} (w : (P →₀ ℕ) → ℂ)
    (hzero : w 0 = 1) (hadd : ∀ e d, w (e + d) = w e * w d)
    (habs : Summable (fun e => ‖w e‖)) (S : Finset P) :
    HasSum (fun e : {e : P →₀ ℕ // e.support ⊆ S} => w e.val)
      (∏ p ∈ S, (1 - w (Finsupp.single p 1))⁻¹) := by
  classical
  induction S using Finset.induction with
  | empty =>
    haveI : Unique {e : P →₀ ℕ // e.support ⊆ ∅} :=
      { default := ⟨0, by simp⟩
        uniq := fun e =>
          Subtype.ext (Finsupp.support_eq_empty.mp (Finset.subset_empty.mp e.property)) }
    have h1 : HasSum (fun _ : {e : P →₀ ℕ // e.support ⊆ ∅} => (1 : ℂ)) 1 := by
      have h := hasSum_unique (fun _ : {e : P →₀ ℕ // e.support ⊆ ∅} => (1 : ℂ))
      beta_reduce at h
      exact h
    have hf : (fun e : {e : P →₀ ℕ // e.support ⊆ ∅} => w e.val)
        = fun _ => (1 : ℂ) := by
      funext e
      rw [Finsupp.support_eq_empty.mp (Finset.subset_empty.mp e.property), hzero]
    rw [Finset.prod_empty, hf]
    exact h1
  | insert p S hp ih =>
    rw [Finset.prod_insert hp]
    have hfac : ∀ x : ℕ × {d : P →₀ ℕ // d.support ⊆ S},
        w ((supportedEraseEquiv p S hp).symm x).val
          = w (Finsupp.single p x.1) * w x.2.val :=
      fun x => by
        rw [supportedEraseEquiv_symm_apply]
        exact hadd (Finsupp.single p x.1) x.2.val
    have hgeo : HasSum (fun n : ℕ => w (Finsupp.single p n))
        (1 - w (Finsupp.single p 1))⁻¹ := by
      have h := hasSum_geometric_of_norm_lt_one
        (finsupp_generator_norm_lt_one w hzero hadd habs p)
      have hf : (fun n : ℕ => w (Finsupp.single p 1) ^ n)
          = fun n => w (Finsupp.single p n) :=
        funext fun n => (finsupp_pow_single w hzero hadd p n).symm
      rwa [hf] at h
    have hsumm : Summable (fun x : ℕ × {d : P →₀ ℕ // d.support ⊆ S} =>
        w (Finsupp.single p x.1) * w x.2.val) := by
      have h1 : Summable (fun e : {e : P →₀ ℕ // e.support ⊆ insert p S} => ‖w e.val‖) :=
        habs.subtype _
      have h2 : Summable (fun x : ℕ × {d : P →₀ ℕ // d.support ⊆ S} =>
          ‖w ((supportedEraseEquiv p S hp).symm x).val‖) :=
        (supportedEraseEquiv p S hp).symm.summable_iff.mpr h1
      have h3 : Summable (fun x : ℕ × {d : P →₀ ℕ // d.support ⊆ S} =>
          ‖w (Finsupp.single p x.1) * w x.2.val‖) := by
        simpa only [hfac] using h2
      exact h3.of_norm
    have hmain : HasSum (fun x : ℕ × {d : P →₀ ℕ // d.support ⊆ S} =>
        w (Finsupp.single p x.1) * w x.2.val)
        ((1 - w (Finsupp.single p 1))⁻¹ * ∏ q ∈ S, (1 - w (Finsupp.single q 1))⁻¹) :=
      HasSum.mul (f := fun n : ℕ => w (Finsupp.single p n))
        (g := fun d : {d : P →₀ ℕ // d.support ⊆ S} => w d.val) hgeo ih hsumm
    exact (Equiv.hasSum_iff (supportedEraseEquiv p S hp).symm
      (f := fun e : {e : P →₀ ℕ // e.support ⊆ insert p S} => w e.val)).mp
      (hmain.congr_fun hfac)

end DedekindZetaZeroFree.LargeSieve.IdealEuler
