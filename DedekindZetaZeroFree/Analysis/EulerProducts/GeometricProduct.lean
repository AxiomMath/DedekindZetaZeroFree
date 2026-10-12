module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic

public import Mathlib.Analysis.Normed.Ring.InfiniteProd

@[expose] public section

namespace DedekindZetaZeroFree.ExteriorEulerGeometricProduct
noncomputable section
open scoped Classical BigOperators Topology
open Filter

set_option maxHeartbeats 1000000

private theorem finite_geom (ι : Type*) [Fintype ι] (z : ι → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    Summable (fun f : ι → ℕ => ‖∏ i, z i ^ f i‖) ∧
    HasSum (fun f : ι → ℕ => ∏ i, z i ^ f i) (∏ i, (1 - z i)⁻¹) := by
  classical
  revert z hz
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ (z : ι → ℂ), (∀ i, ‖z i‖ < 1) →
    Summable (fun f : ι → ℕ => ‖∏ i, z i ^ f i‖) ∧
    HasSum (fun f : ι → ℕ => ∏ i, z i ^ f i) (∏ i, (1 - z i)⁻¹)) ?_ ?_ ?_ ι
  · intro α β _ e ih z hz
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := Equiv.piCongrLeft (fun _ : β => ℕ) e
    have h := ih (z ∘ e) (fun i => hz (e i))
    constructor
    · apply E.summable_iff.mp
      simpa [E, Function.comp_def, ← Equiv.prod_comp e] using h.1
    · apply E.hasSum_iff.mp
      simpa [E, Function.comp_def, ← Equiv.prod_comp e] using h.2
  · intro z hz
    have h : (fun f : PEmpty → ℕ => ∏ i, z i ^ f i) = fun _ => (1 : ℂ) := by ext f; simp
    rw [h]
    exact ⟨(hasSum_fintype _).summable, by simpa using (hasSum_fintype (fun _ : PEmpty → ℕ => (1 : ℂ)))⟩
  · intro α _ ih z hz
    have h := ih (fun i => z (some i)) (fun i => hz (some i))
    have hg := hasSum_geometric_of_norm_lt_one (hz none)
    have hn : Summable (fun n : ℕ => ‖z none ^ n‖) := by
      simpa [norm_pow] using (hasSum_geometric_of_norm_lt_one (by simpa using hz none : ‖‖z none‖‖ < 1)).summable
    have hp : Summable (fun f : ℕ × (α → ℕ) => ‖z none ^ f.1 * ∏ i, z (some i) ^ f.2 i‖) := by
      simp_rw [norm_mul]
      exact hn.mul_of_nonneg h.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    constructor
    · simpa [E, Function.comp_def, Fintype.prod_option] using E.summable_iff.mpr hp
    · simpa [E, Function.comp_def, Fintype.prod_option, mul_comm] using
        E.hasSum_iff.mpr (hg.mul h.2 hp.of_norm)

private theorem supported_hasSum {P : Type*} (r : P → ℂ) (hr : ∀ p, ‖r p‖ < 1) (s : Finset P) :
    HasSum (fun e : {e : P →₀ ℕ // (↑e.support : Set P) ⊆ (s : Set P)} =>
      e.val.prod (fun p k => r p ^ k)) (∏ p ∈ s, (1 - r p)⁻¹) := by
  classical
  let E := (Finsupp.restrictSupportEquiv (s : Set P) ℕ).trans Finsupp.equivFunOnFinite
  have he (e : {e : P →₀ ℕ // (↑e.support : Set P) ⊆ (s : Set P)}) :
      e.val.prod (fun p k => r p ^ k) = ∏ p : (s : Set P), r p ^ (E e) p := by
    rw [← Finsupp.prod_subtypeDomain_index (fun p hp => e.property hp), Finsupp.prod_fintype]
    · rfl
    · intro i; simp
  have hh := (finite_geom (s : Set P) (fun p => r p) (fun p => hr p)).2
  have ht : (∏ p : (s : Set P), (1 - r p)⁻¹) = ∏ p ∈ s, (1 - r p)⁻¹ := by
    exact Finset.prod_coe_sort s (fun p : P => (1 - r p)⁻¹)
  rw [← ht]
  simpa only [Function.comp_def, ← he] using E.hasSum_iff.mpr hh

theorem hasProd_geometric {P : Type*} (r : P → ℂ)
    (hr : ∀ p, ‖r p‖ < 1)
    (h : Summable (fun e : P →₀ ℕ => ‖e.prod (fun p k => r p ^ k)‖)) :
    HasProd (fun p => (1 - r p)⁻¹)
      (∑' e : P →₀ ℕ, e.prod (fun p k => r p ^ k)) := by
  classical
  let f : (P →₀ ℕ) → ℂ := fun e => e.prod (fun p k => r p ^ k)
  let g : Finset P → (P →₀ ℕ) → ℂ := fun s e =>
    if e.support ⊆ s then f e else 0
  have ht : Tendsto (fun s : Finset P => ∑' e, g s e) atTop (𝓝 (∑' e, f e)) := by
    apply tendsto_tsum_of_dominated_convergence h
    · intro e
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop e.support] with s hs
      simp [g, hs]
    · exact Filter.Eventually.of_forall (fun s e => by
        dsimp [g]; split_ifs <;> simp [f])
  have he (s : Finset P) : (∑' e, g s e) = ∏ p ∈ s, (1 - r p)⁻¹ := by
    have hsame (e : P →₀ ℕ) : g s e =
        {e : P →₀ ℕ | (↑e.support : Set P) ⊆ (s : Set P)}.indicator f e := by
      simp [g, Set.indicator, Finset.coe_subset]
    simp_rw [hsame]
    rw [← tsum_subtype]
    exact (supported_hasSum r hr s).tsum_eq
  change Tendsto (fun s : Finset P => ∏ p ∈ s, (1 - r p)⁻¹) atTop _
  simpa only [he] using ht

end
end DedekindZetaZeroFree.ExteriorEulerGeometricProduct
