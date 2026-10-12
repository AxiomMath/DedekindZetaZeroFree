module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

theorem compact_kernel_representatives
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U) :
    ∃ B : Set (KPCuspCharts.Horizontal F), IsCompact B ∧
      ∀ z : KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a,
        ∃ x ∈ B, (QuotientAddGroup.mk x :
          KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a) = z := by
  let T := KPContFlatCuspIncomingEvaluation.KernelTorus F ζ hζ C R P H U a
  letI := (KPContFlatCuspIncomingEvaluation.monodromy F ζ hζ C R P H U a).compact
  have hrep : ∀ z : T, ∃ x : KPCuspCharts.Horizontal F, (QuotientAddGroup.mk x : T) = z :=
    fun z => Quotient.exists_rep z
  choose x hx using hrep
  choose B hB hBn using fun z : T => exists_compact_mem_nhds (x z)
  have hn : ∀ z : T, (QuotientAddGroup.mk : KPCuspCharts.Horizontal F → T) '' B z ∈ 𝓝 z := by
    intro z
    have hh : (QuotientAddGroup.mk : KPCuspCharts.Horizontal F → T) '' B z ∈
        𝓝 (QuotientAddGroup.mk (x z) : T) :=
      QuotientAddGroup.isOpenMap_coe.image_mem_nhds (hBn z)
    simpa only [hx z] using hh
  obtain ⟨J, hJ⟩ := finite_cover_nhds hn
  refine ⟨⋃ z ∈ J, B z, ?_, ?_⟩
  · exact J.finite_toSet.isCompact_biUnion (fun z _ => hB z)
  · intro z
    have hz : z ∈ ⋃ y ∈ J, (QuotientAddGroup.mk : KPCuspCharts.Horizontal F → T) '' B y := by
      rw [hJ]; trivial
    simp only [Set.mem_iUnion] at hz
    obtain ⟨y, hy, v, hv, he⟩ := hz
    exact ⟨v, Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hv⟩⟩, he⟩

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
