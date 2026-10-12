module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped Classical

private lemma hasSum_finset_sum {ι X M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] (t : Finset ι) (f : ι → X → M) (g : ι → M)
    (h : ∀ i ∈ t, HasSum (f i) (g i)) :
    HasSum (fun x => ∑ i ∈ t, f i x) (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using hasSum_zero (α := M) (β := X)
  | insert i t hi ih =>
      have h1 : HasSum (f i) (g i) := h i (Finset.mem_insert_self i t)
      have h2 : HasSum (fun x => ∑ j ∈ t, f j x) (∑ j ∈ t, g j) :=
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert hi] using h1.add h2

theorem finiteCharacterEntireAssembly
    {A G : Type*} [Group G] [Fintype G]
    (q : A → Option G) (w : A → ℂ → ℂ)
    (ψ : G →* ℂ) (hψ : ψ ≠ 1)
    (ρ : ℂ) (F : G → ℂ → ℂ)
    (hF : ∀ c, Differentiable ℂ (F c))
    (hpartial : ∀ c s, 1 < s.re →
      HasSum (fun a => if q a = some c then w a s else 0)
        (F c s + ρ / (s - 1))) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ s, 1 < s.re →
        HasSum (fun a => (match q a with
          | none => 0
          | some c => ψ c) * w a s) (f s) := by
  classical
  refine ⟨fun s => ∑ c : G, ψ c * F c s, ?_, ?_⟩
  · convert Differentiable.sum (u := Finset.univ)
        (A := fun c : G => fun s : ℂ => ψ c * F c s)
        (fun c _ => (hF c).const_mul (ψ c)) using 1
    ext s
    simp only [Finset.sum_apply]
  · intro s hs

    have hpt : (fun a => (match q a with
          | none => 0
          | some c => ψ c) * w a s)
        = fun a => ∑ c : G, ψ c * (if q a = some c then w a s else 0) := by
      funext a
      rcases hq : q a with _ | c₀
      · simp [hq]
      · simp [hq]

    have hsum := hasSum_finset_sum Finset.univ
        (fun c a => ψ c * (if q a = some c then w a s else 0))
        (fun c => ψ c * (F c s + ρ / (s - 1)))
        (fun c _ => (hpartial c s hs).mul_left (ψ c))

    have hval : (∑ c : G, ψ c * (F c s + ρ / (s - 1))) = ∑ c : G, ψ c * F c s := by
      rw [show (∑ c : G, ψ c * (F c s + ρ / (s - 1)))
          = ∑ c : G, (ψ c * F c s + ψ c * (ρ / (s - 1))) from
            Finset.sum_congr rfl fun c _ => mul_add _ _ _]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_hom_units_eq_zero ψ hψ,
        zero_mul, add_zero]
    rw [hpt]
    change HasSum (fun a => ∑ c : G, ψ c * (if q a = some c then w a s else 0))
      (∑ c : G, ψ c * F c s)
    rw [← hval]
    exact hsum

end DedekindZetaZeroFree.AbelianQuotient
