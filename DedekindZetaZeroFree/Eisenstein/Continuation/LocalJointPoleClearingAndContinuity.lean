module

public import DedekindZetaZeroFree.Theta.Periods.MeromorphicContinuationAndResidues
public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds

@[expose] public section

section

noncomputable section
open scoped Topology
open MeasureTheory Complex Metric

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.SpatialRegularity.LocalLaurent

end DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.SpatialRegularity.LocalLaurent

end

end

section

noncomputable section
open scoped Topology
open Filter

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.SpatialRegularity.LocalLaurent

variable {G V J : Type*} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem native_powerSeries_joint_continuousOn
    (D : J → V →ₗ[ℂ] C(G, ℂ)) (j : J)
    (s : ℂ) (ρ r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ)
    (a : ℕ → V) (f : ℂ → V)
    (ha : KPGlobalEisensteinData.SmoothPowerSeriesOn D s ρ a f)
    (K : Set G) (hK : IsCompact K) :
    ContinuousOn (fun p : ℂ × G => D j (f p.1) p.2)
      (Metric.closedBall s r ×ˢ K) := by
  let i : KPGlobalEisensteinData.DifferentialCompact G J := ⟨K, hK, j⟩
  letI : CompactSpace i.compact := isCompact_iff_compactSpace.mp i.isCompact
  have hlim : TendstoUniformlyOn
      (fun M (p : ℂ × G) => ∑ q ∈ Finset.range M, (p.1 - s)^q * D j (a q) p.2)
      (fun p : ℂ × G => D j (f p.1) p.2)
      atTop (Metric.closedBall s r ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := ha i r hr hrρ ε hε
    filter_upwards [eventually_ge_atTop N] with M hM
    intro p hp
    have hbound : ‖D j ((∑ q ∈ Finset.range M, (p.1-s)^q • a q) - f p.1) p.2‖ ≤
        KPGlobalEisensteinData.smoothSeminorm D i
          ((∑ q ∈ Finset.range M, (p.1-s)^q • a q) - f p.1) :=
      (KPGlobalEisensteinData.derivativeRestriction D i _).norm_coe_le_norm ⟨p.2, hp.2⟩
    have h := lt_of_le_of_lt hbound (hN M hM p.1 hp.1)
    simpa only [map_sub, map_sum, map_smul, ContinuousMap.sub_apply,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      dist_eq_norm, norm_sub_rev] using h
  apply hlim.continuousOn
  exact (Eventually.of_forall (fun M => (by fun_prop : Continuous
    (fun p : ℂ × G => ∑ q ∈ Finset.range M, (p.1-s)^q * D j (a q) p.2)).continuousOn)).frequently

end DedekindZetaZeroFree.KPGlobalResidualKernel.ResidualChamberConstruction.SpatialRegularity.LocalLaurent

end

end
