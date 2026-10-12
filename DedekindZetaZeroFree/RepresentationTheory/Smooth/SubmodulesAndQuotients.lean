module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Topology

def smoothSubmodule {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ V :=
  Submodule.span ℂ {v : V | SmoothVector ρ v}

@[simp] theorem mem_smoothSubmodule {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    v ∈ smoothSubmodule ρ ↔ SmoothVector ρ v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨⊤, by simp⟩
    | add x y hx hy hxsm hysm =>
      rcases hxsm with ⟨J, hJ⟩
      rcases hysm with ⟨K, hK⟩
      exact ⟨J ⊓ K, fun j hj => by simp [hJ j hj.1, hK j hj.2]⟩
    | smul a x hx hxsm =>
      rcases hxsm with ⟨J, hJ⟩
      exact ⟨J, fun j hj => by simp [hJ j hj]⟩
  · intro hv
    exact Submodule.subset_span hv

theorem smoothSubmodule_stable {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    smoothSubmodule ρ ≤ (smoothSubmodule ρ).comap (ρ g) := by
  intro v hv
  rw [Submodule.mem_comap, mem_smoothSubmodule]
  rcases (mem_smoothSubmodule ρ v).mp hv with ⟨J, hJ⟩
  refine ⟨J.comap (MulAut.conj g⁻¹).toMonoidHom
    (IsTopologicalGroup.continuous_conj g⁻¹), ?_⟩
  intro j hj
  have hfix := hJ (g⁻¹ * j * g) (by simpa [MulAut.conj_apply] using hj)
  have heq : j * g = g * (g⁻¹ * j * g) := by group
  calc
    ρ j (ρ g v) = ρ (j * g) v := by simp [map_mul, Module.End.mul_apply]
    _ = ρ g (ρ (g⁻¹ * j * g) v) := by rw [heq]; simp [map_mul, Module.End.mul_apply]
    _ = ρ g v := by rw [hfix]

def smoothPart {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (smoothSubmodule ρ) :=
  ρ.subrepresentation (smoothSubmodule ρ) (smoothSubmodule_stable ρ)

theorem smoothPart_smooth {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : SmoothRepresentation (smoothPart ρ) := by
  intro v
  rcases (mem_smoothSubmodule ρ v.val).mp v.property with ⟨J, hJ⟩
  exact ⟨J, fun j hj => Subtype.ext (hJ j hj)⟩

theorem smoothVector_iff_compactOpen_fixed {G V : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hcompactOpen : ∀ U ∈ 𝓝 (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ U)
    (ρ : Representation ℂ G V) (v : V) :
    SmoothVector ρ v ↔ ∃ J : CompactOpenLevel G,
      v ∈ fixedSubmodule ρ (J.toOpenSubgroup : Subgroup G) := by
  constructor
  · rintro ⟨U, hU⟩
    obtain ⟨J, hJ⟩ := hcompactOpen (U : Set G) U.mem_nhds_one
    exact ⟨J, fun j => hU j (hJ j.property)⟩
  · rintro ⟨J, hJ⟩
    exact ⟨J.toOpenSubgroup, fun j hj => hJ ⟨j, hj⟩⟩

theorem smoothRepresentation_subrepresentation {G V : Type*} [Group G]
    [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ)
    (W : Submodule ℂ V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) :
    SmoothRepresentation (ρ.subrepresentation W hW) := by
  intro v
  rcases hρ v.val with ⟨J, hJ⟩
  exact ⟨J, fun j hj => Subtype.ext (hJ j hj)⟩

theorem smoothRepresentation_quotient {G V : Type*} [Group G]
    [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : SmoothRepresentation ρ)
    (W : Submodule ℂ V) (hW : ∀ g : G, W ≤ W.comap (ρ g)) :
    SmoothRepresentation (ρ.quotient W hW) := by
  intro v
  obtain ⟨w, rfl⟩ := W.mkQ_surjective v
  rcases hρ w with ⟨J, hJ⟩
  refine ⟨J, fun j hj => ?_⟩
  change W.mapQ W (ρ j) (hW j) (Submodule.Quotient.mk w) = Submodule.Quotient.mk w
  rw [Submodule.mapQ_apply, hJ j hj]

theorem intertwiningMap_fixedSubmodule {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : Representation.IntertwiningMap ρ σ) (J : Subgroup G) :
    (fixedSubmodule ρ J).map f.toLinearMap ≤ fixedSubmodule σ J := by
  rintro v ⟨w, hw, rfl⟩
  intro j
  change σ j (f w) = f w
  rw [← f.isIntertwining, hw j]

end DedekindZetaZeroFree
