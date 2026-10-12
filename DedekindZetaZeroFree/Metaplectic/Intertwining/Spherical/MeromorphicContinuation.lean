module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ContinuedOperatorFamilies
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TameSphericalFactor

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Valued Classical
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneRootParameter KPRankOneShellContinuation KPRankOneTameSphericalFactor
open KPRankOneShellRepair

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
  {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
  {T : LocalHeisenbergData H D}

 theorem compact_extension_value
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ)
    (φ : compactPicture A P I ε) (k : I.compact.toOpenSubgroup) :
    (compactTrivialization A P I ε s φ).val (k : G) = φ.val k := by
  change inducingAction A P ε s (I.borelPart (k : G))
    (φ.val (I.compactPart (k : G))) = _
  rw [I.borelPart_compact, I.compactPart_compact]
  simp

theorem spherical_vector_mem_level
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (φ : compactPicture A P I ε)
    (hφ : IsSphericalVector K A P I ε φ) :
    φ ∈ compactLevel A P I ε I.compact := by
  apply (compact_level_identification A P I ε I.compact le_rfl 0 φ).mpr
  intro k
  exact hφ.2 0 k

theorem is_spherical_vector_iff
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (φ : compactPicture A P I ε) :
    IsSphericalVector K A P I ε φ ↔
      φ ∈ compactLevel A P I ε I.compact ∧ (φ.val 1).val 1 = 1 := by
  constructor
  · intro hφ
    refine ⟨spherical_vector_mem_level K A P I ε φ hφ, ?_⟩
    have hh := hφ.1 0
    have hv := compact_extension_value K A P I ε 0 φ 1
    have hv' := congrArg (fun v : InducedModule P => v.val 1) hv
    exact hv'.symm.trans hh
  · rintro ⟨hlevel, hnorm⟩
    constructor
    · intro s
      have hv := compact_extension_value K A P I ε s φ 1
      exact (congrArg (fun v : InducedModule P => v.val 1) hv).trans hnorm
    · intro s k
      exact (compact_level_identification A P I ε I.compact le_rfl s φ).mp hlevel k

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
