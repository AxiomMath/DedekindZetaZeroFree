module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarishChandra.SimplicityAndScalarEndomorphisms

@[expose] public section

noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.RootDerivatives
open KPGlobalResidualConstruction
open KPGlobalResidualConstruction.NativeComplexHCSource

theorem complexHC_algebra_cyclic
    (B : Fin 6 → Module.End ℂ complexCore)
    (hs : IsSimpleOrder (Submodule (algebra B) complexCore))
    (v : complexCore) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun a : algebra B => a.val v)) = ⊤ := by
  let N : Submodule (algebra B) complexCore :=
    { carrier := Submodule.span ℂ (Set.range (fun a : algebra B => a.val v))
      zero_mem' := Submodule.zero_mem _
      add_mem' := Submodule.add_mem _
      smul_mem' := by
        intro a x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          exact Submodule.subset_span ⟨a * b, rfl⟩
        | zero =>
          change a.val 0 ∈ _
          rw [map_zero]
          exact Submodule.zero_mem _
        | add x y hx hy ihx ihy =>
          change a.val (x + y) ∈ _
          rw [map_add]
          exact Submodule.add_mem _ ihx ihy
        | smul c x hx ih =>
          change a.val (c • x) ∈ _
          rw [map_smul]
          exact Submodule.smul_mem _ c ih }
  letI := hs
  have hN : N ≠ ⊥ := by
    intro hN
    have hm : v ∈ N := by
      exact Submodule.subset_span ⟨1, rfl⟩
    exact hv (by simpa only [hN, Submodule.mem_bot] using hm)
  have ht : N = ⊤ := (eq_bot_or_eq_top N).resolve_left hN
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact (show x ∈ N from ht ▸ Submodule.mem_top)

theorem complexHC_recovery {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : Fin 6 → Module.End ℂ complexCore)
    (hcyc : ∀ v : complexCore, v ≠ 0 →
      Submodule.span ℂ (Set.range (fun a : algebra B => a.val v)) = ⊤)
    (L : complexCore →ₗ[ℂ] V) (U : Submodule ℂ V)
    (hcompact : ∀ k x, L x ∈ U → L (complexCoreCompactLinearMap k x) ∈ U)
    (hderiv : ∀ i x, L x ∈ U → L (B i x) ∈ U)
    (v : complexCore) (hv : v ≠ 0) (hm : L v ∈ U) :
    ∀ z : complexCore, L z ∈ U := by
  let A : Subalgebra ℂ (Module.End ℂ complexCore) :=
    { carrier := {a | ∀ x, L x ∈ U → L (a x) ∈ U}
      zero_mem' := by intros; simpa using U.zero_mem
      one_mem' := by intros x hx; exact hx
      add_mem' := by
        intro a b ha hb x hx
        simpa only [LinearMap.add_apply, map_add] using U.add_mem (ha x hx) (hb x hx)
      mul_mem' := by
        intro a b ha hb x hx
        exact ha _ (hb x hx)
      algebraMap_mem' := by
        intro c x hx
        change L (c • x) ∈ U
        simpa only [map_smul] using U.smul_mem c hx }
  have hA : algebra B ≤ A := by
    apply Algebra.adjoin_le
    rintro a (⟨k,rfl⟩ | ⟨i,rfl⟩)
    · exact hcompact k
    · exact hderiv i
  intro z
  have hz : z ∈ Submodule.span ℂ (Set.range (fun a : algebra B => a.val v)) := by
    rw [hcyc v hv]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    exact hA a.property v hm
  | zero => simpa using U.zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using U.add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using U.smul_mem c ih

end DedekindZetaZeroFree.RootDerivatives

end
