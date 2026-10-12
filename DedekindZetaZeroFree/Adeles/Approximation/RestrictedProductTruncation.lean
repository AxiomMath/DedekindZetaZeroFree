module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section

noncomputable section
open Filter Topology
namespace DedekindZetaZeroFree.WildRestrictedTruncation
variable {I : Type*} (G : I → Type*) [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] (K : ∀ i, Subgroup (G i))
local instance : DecidableEq I := Classical.decEq _

abbrev Product := RestrictedProduct G (fun i ↦ (K i : Set (G i))) Filter.cofinite

def truncate (x : Product G K) (s : Finset I) : Product G K :=
  ⟨fun i ↦ if i ∈ s then x i else 1, by
    apply Filter.eventually_cofinite.mpr
    apply s.finite_toSet.subset
    intro i hi
    by_contra hn
    apply hi
    change (if i ∈ s then x i else 1) ∈ K i
    rw [ite_eq_right (show i ∉ s from hn)]
    exact (K i).one_mem⟩

theorem tendsto_truncate (x : Product G K) :
    Tendsto (truncate G K x) atTop (𝓝 x) := by
  let S : Set I := {i | x i ∈ K i}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.mpr x.property
  let y : RestrictedProduct G (fun i ↦ (K i : Set (G i))) (Filter.principal S) :=
    ⟨x, by exact Filter.eventually_principal.mpr (fun i hi ↦ hi)⟩
  let f (s : Finset I) :
      RestrictedProduct G (fun i ↦ (K i : Set (G i))) (Filter.principal S) :=
    ⟨truncate G K x s, by
      apply Filter.eventually_principal.mpr
      intro i hi
      change (if i ∈ s then x i else 1) ∈ K i
      split_ifs
      · exact hi
      · exact (K i).one_mem⟩
  have hf : Tendsto f atTop (𝓝 y) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G)
      (A := fun i ↦ (K i : Set (G i))) (S := S)).tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
    have hi : i ∈ s := hs (Finset.mem_singleton_self i)
    change x i = (if i ∈ s then x i else 1)
    rw [ite_eq_left hi]
  exact (RestrictedProduct.continuous_inclusion (R := G)
    (A := fun i ↦ (K i : Set (G i))) hS).continuousAt.tendsto.comp hf

theorem truncate_insert (x : Product G K) (s : Finset I) (i : I) (hi : i ∉ s) :
    truncate G K x (insert i s) = RestrictedProduct.mulSingle K i (x i) * truncate G K x s := by
  apply RestrictedProduct.ext
  intro j
  by_cases hj : j = i
  · subst j
    change (if i ∈ insert i s then x i else 1) =
      RestrictedProduct.mulSingle K i (x i) i * (if i ∈ s then x i else 1)
    rw [ite_eq_left (Finset.mem_insert_self i s), ite_eq_right hi,
      RestrictedProduct.mulSingle_eq_same, mul_one]
  · change (if j ∈ insert i s then x j else 1) =
      RestrictedProduct.mulSingle K i (x i) j * (if j ∈ s then x j else 1)
    rw [RestrictedProduct.mulSingle_eq_of_ne K _ hj, one_mul]
    simp only [Finset.mem_insert, hj, false_or]

def word (x : Product G K) : List I → Product G K
  | [] => 1
  | i :: l => RestrictedProduct.mulSingle K i (x i) * word x l

theorem truncate_list (x : Product G K) (l : List I) (hl : l.Nodup) :
    truncate G K x l.toFinset = word G K x l := by
  induction l with
  | nil =>
    apply RestrictedProduct.ext
    intro i
    change (if i ∈ ([] : List I).toFinset then x i else 1) = 1
    simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.toFinset_cons, truncate_insert G K x l.toFinset i (by simpa using hl.1),
      ih hl.2]
    rfl

theorem continuous_zero_of_words {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : Product G K → Y) (hf : Continuous f) (c : Y)
    (hz : ∀ x l, l.Nodup → f (word G K x l) = c) : ∀ x, f x = c := by
  intro x
  have hlim := hf.continuousAt.tendsto.comp (tendsto_truncate G K x)
  have he : (fun s : Finset I ↦ f (truncate G K x s)) = fun _ ↦ c := by
    funext s
    have hword := truncate_list G K x s.toList s.nodup_toList
    rw [Finset.toList_toFinset] at hword
    rw [hword]
    exact hz x s.toList s.nodup_toList
  change Tendsto (fun s : Finset I ↦ f (truncate G K x s)) atTop (𝓝 (f x)) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end DedekindZetaZeroFree.WildRestrictedTruncation

end
