module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalAndAdelicCovers
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPSmoothCofinalNormalLevels

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteSubgroup : Subgroup (KPCubicCoverConstruction.AdelicGL2Cover F ζ hζ) :=
  ⨅ w : InfinitePlace F,
    ((KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)).comp
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ)).ker

abbrev FiniteGL2Cover := ↥(finiteSubgroup F ζ hζ)

open Filter Set
open scoped Topology

private theorem countable_nhds_local {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [FirstCountableTopology Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (x : X) : (𝓝 x).IsCountablyGenerated := by
  obtain ⟨U, hU, he⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x
  letI : FirstCountableTopology U := he.isEmbedding.firstCountableTopology
  let xU : U := ⟨x, mem_of_mem_nhds hU⟩
  have hm : map (Subtype.val : U → X) (𝓝 xU) = 𝓝 x := by
    rw [Topology.IsEmbedding.subtypeVal.map_nhds_eq, Subtype.range_val]
    exact nhdsWithin_eq_nhds.mpr hU
  rw [← hm]
  infer_instance

theorem adelicGL2Cover_firstCountableTopology :
    FirstCountableTopology (KPCubicCoverConstruction.AdelicGL2Cover F ζ hζ) := by
  let M := Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F)
  letI : FirstCountableTopology M :=
    inferInstanceAs (FirstCountableTopology
      (Fin 2 → Fin 2 → KPAdelicCoverRestrictedProduct.Adeles F))
  letI : FirstCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.firstCountableTopology
  letI : FirstCountableTopology (KPAdelicCoverRestrictedProduct.AdelicGL2 F) :=
    Units.isEmbedding_embedProduct.firstCountableTopology
  exact ⟨countable_nhds_local
    (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2⟩

instance finiteGL2Cover_firstCountableTopology :
    FirstCountableTopology (FiniteGL2Cover F ζ hζ) := by
  letI := adelicGL2Cover_firstCountableTopology F ζ hζ
  exact Topology.IsEmbedding.subtypeVal.firstCountableTopology

structure NormalCofinalLevels where
  U₀ : CompactOpenLevel (FiniteGL2Cover F ζ hζ)
  level : ℕ → CompactOpenLevel (FiniteGL2Cover F ζ hζ)
  level_zero : level 0 = U₀
  contained : ∀ n,
    (level n).toOpenSubgroup.toSubgroup ≤ U₀.toOpenSubgroup.toSubgroup
  decreasing : Antitone (fun n => (level n).toOpenSubgroup.toSubgroup)
  normal : ∀ n,
    ((level n).toOpenSubgroup.toSubgroup.subgroupOf
      U₀.toOpenSubgroup.toSubgroup).Normal
  finite_quotient : ∀ n,
    Finite (U₀.toOpenSubgroup.toSubgroup ⧸
      (level n).toOpenSubgroup.toSubgroup.subgroupOf U₀.toOpenSubgroup.toSubgroup)
  cofinal : ∀ U : CompactOpenLevel (FiniteGL2Cover F ζ hζ),
    ∃ n, (level n).toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup
  compact_conjugation : ∀ S : Set (FiniteGL2Cover F ζ hζ), IsCompact S →
    ∀ n, ∃ m, ∀ g ∈ S, ∀ u ∈ (level m).toOpenSubgroup,
      g⁻¹ * u * g ∈ (level n).toOpenSubgroup

section NormalCoreHelpers

open Filter Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compact_conjugation_nhds (S : Set G) (hS : IsCompact S)
    (U : OpenSubgroup G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ g ∈ S, ∀ u ∈ W, g⁻¹ * u * g ∈ U := by
  have h : ∀ᶠ u in 𝓝 (1 : G), ∀ g ∈ S, g⁻¹ * u * g ∈ U := by
    apply hS.eventually_forall_of_forall_eventually
    intro g hg
    have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1 * p.2) :=
      (continuous_snd.inv.mul continuous_fst).mul continuous_snd
    have hu : g⁻¹ * (1 : G) * g ∈ U := by simp
    exact hc.continuousAt.eventually (U.isOpen.mem_nhds hu)
  exact ⟨{u | ∀ g ∈ S, g⁻¹ * u * g ∈ U}, h, by tauto⟩

end NormalCoreHelpers

section CountableBasisHelpers
open Filter Set
open scoped Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end CountableBasisHelpers

section ActualFiniteTopology
open Filter Set Topology
open scoped Topology

end ActualFiniteTopology

section ActualCompactOpenBasis
open Filter Set Topology
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ActualCompactOpenBasis

def pglMatrixEval (v : KPHilbert.Place F) :
    KPAdelicCoverRestrictedProduct.AdelicPGL2 F →* KPPGLLocalCover.LocalPGL2 F v :=
  QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    ((KPPGLLocalCover.baseQuotient F v).comp
      (KPAdelicCoverRestrictedProduct.matrixEval F v)) (by
    rintro x ⟨z, rfl⟩
    change KPPGLLocalCover.baseQuotient F v
      (Matrix.GeneralLinearGroup.map (KPAdelicCoverRestrictedProduct.adeleEval F v)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) = 1
    rw [Matrix.GeneralLinearGroup.map_scalar]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩)

def localPGLKernel (v : KPHilbert.Place F) :
    Subgroup (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) :=
  ((pglMatrixEval F v).comp
    (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)).ker

def finitePGLSubgroup : Subgroup (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) :=
  ⨅ w : InfinitePlace F, localPGLKernel F ζ hζ (Sum.inl w)

abbrev FinitePGL2Cover := ↥(finitePGLSubgroup F ζ hζ)

theorem adelicPGL2Cover_firstCountableTopology :
    FirstCountableTopology (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ) := by
  letI := adelicGL2Cover_firstCountableTopology F ζ hζ
  letI : IsTopologicalGroup (KPCubicCoverConstruction.AdelicGL2Cover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.1
  exact inferInstanceAs (FirstCountableTopology
    (KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ ⧸
      KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ))

instance finitePGL2Cover_firstCountableTopology :
    FirstCountableTopology (FinitePGL2Cover F ζ hζ) := by
  letI := adelicPGL2Cover_firstCountableTopology F ζ hζ
  exact Topology.IsEmbedding.subtypeVal.firstCountableTopology

structure NormalCofinalPGLLevels where
  U₀ : CompactOpenLevel (FinitePGL2Cover F ζ hζ)
  level : ℕ → CompactOpenLevel (FinitePGL2Cover F ζ hζ)
  level_zero : level 0 = U₀
  contained : ∀ n,
    (level n).toOpenSubgroup.toSubgroup ≤ U₀.toOpenSubgroup.toSubgroup
  decreasing : Antitone (fun n => (level n).toOpenSubgroup.toSubgroup)
  normal : ∀ n,
    ((level n).toOpenSubgroup.toSubgroup.subgroupOf
      U₀.toOpenSubgroup.toSubgroup).Normal
  finite_quotient : ∀ n,
    Finite (U₀.toOpenSubgroup.toSubgroup ⧸
      (level n).toOpenSubgroup.toSubgroup.subgroupOf U₀.toOpenSubgroup.toSubgroup)
  cofinal : ∀ U : CompactOpenLevel (FinitePGL2Cover F ζ hζ),
    ∃ n, (level n).toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup
  compact_conjugation : ∀ S : Set (FinitePGL2Cover F ζ hζ), IsCompact S →
    ∀ n, ∃ m, ∀ g ∈ S, ∀ u ∈ (level m).toOpenSubgroup,
      g⁻¹ * u * g ∈ (level n).toOpenSubgroup

end
end DedekindZetaZeroFree.KPSmoothCofinalNormalLevels
