module

public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

section

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeRepresentationAlgebra

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

def algebra (ρ : Representation ℂ G V) : Subalgebra ℂ (Module.End ℂ V) :=
  Algebra.adjoin ℂ (Set.range ρ)

instance (ρ : Representation ℂ G V) : Module (algebra ρ) V :=
  Module.compHom V (algebra ρ).val.toRingHom

instance (ρ : Representation ℂ G V) : IsScalarTower ℂ (algebra ρ) V where
  smul_assoc c a v := rfl

instance (ρ : Representation ℂ G V) : SMulCommClass (algebra ρ) ℂ V where
  smul_comm a c v := a.val.map_smul c v

theorem simple (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsSimpleOrder (Submodule (algebra ρ) V) := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  apply (isSimpleOrder_iff _).mpr
  refine ⟨(Submodule.nontrivial_iff _).mpr inferInstance, fun N => ?_⟩
  let S : Subrepresentation ρ :=
    { toSubmodule := N.restrictScalars ℂ
      apply_mem_toSubmodule := by
        intro g v hv
        exact N.smul_mem ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ hv }
  rcases eq_bot_or_eq_top S with h | h
  · left
    ext v
    change v ∈ S ↔ v ∈ (⊥ : Submodule (algebra ρ) V)
    rw [h]
    rfl
  · right
    ext v
    change v ∈ S ↔ v ∈ (⊤ : Submodule (algebra ρ) V)
    rw [h]
    rfl

def intertwiner (ρ : Representation ℂ G V) (T : Module.End (algebra ρ) V) :
    ρ.IntertwiningMap ρ where
  toLinearMap := T.restrictScalars ℂ
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact T.map_smul ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩⟩ v

theorem scalar_commutant (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (U : Subgroup G) [Module.Finite ℂ (fixedSubmodule ρ U)]
    (hne : fixedSubmodule ρ U ≠ ⊥) :
    ∀ T : Module.End (algebra ρ) V, ∃ c : ℂ, ∀ v, T v = c • v := by
  letI := simple ρ
  letI : IsSimpleModule (algebra ρ) V := (isSimpleModule_iff (algebra ρ) V).mpr inferInstance
  apply RestrictedTensorSimple.scalarCommutant_of_finiteLevel
    (algebra ρ) V (fixedSubmodule ρ U) hne
  intro T v hv
  intro u
  have ht := (intertwiner ρ T).isIntertwining' u.val
  have hh := LinearMap.congr_fun ht v
  change T (ρ u.val v) = ρ u.val (T v) at hh
  rw [hv u] at hh
  exact hh.symm

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeRepresentationAlgebra

end

end

section
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeRepresentationAlgebra
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

theorem scalar_commutant_of_compact_sublevels
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (K : CompactOpenLevel G)
    (hfinite : ∀ J : CompactOpenLevel G, J.toOpenSubgroup ≤ K.toOpenSubgroup →
      Module.Finite ℂ (fixedSubmodule ρ J.toOpenSubgroup.toSubgroup)) :
    ∀ T : Module.End (algebra ρ) V, ∃ c : ℂ, ∀ v, T v = c • v := by
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨U, hU⟩ := hρ v
  let J : CompactOpenLevel G :=
    ⟨U ⊓ K.toOpenSubgroup, by
      change IsCompact ((U : Set G) ∩ (K.toOpenSubgroup : Set G))
      exact K.isCompact.inter_left U.isClosed⟩
  have hJK : J.toOpenSubgroup ≤ K.toOpenSubgroup := inf_le_right
  letI := hfinite J hJK
  apply scalar_commutant ρ J.toOpenSubgroup.toSubgroup
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v, ?_, hv⟩
  intro u
  exact hU u.val u.property.1

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeRepresentationAlgebra

end

end
