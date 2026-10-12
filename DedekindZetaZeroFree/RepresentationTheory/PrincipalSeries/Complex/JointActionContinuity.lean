module

public import DedekindZetaZeroFree.Analysis.Jets.EvaluationContinuity

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesJointBS
open Set Filter Topology
variable {P V : Type*} [TopologicalSpace P] [WeaklyLocallyCompactSpace P]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [BarrelledSpace ℂ V]

lemma joint_continuous {ι : Type*} (p : SeminormFamily ℂ V ι) (hp : WithSeminorms p)
    (T : P → V →ₗ[ℂ] V) (hT : ∀ g, Continuous (T g))
    (horbit : ∀ v, Continuous (fun g => T g v)) :
    Continuous (fun z : P × V => T z.1 z.2) := by
  letI := hp.isTopologicalAddGroup
  have hbound : ∀ g i, ∃ q : Seminorm ℂ V, Continuous q ∧
      ∀ᶠ h in 𝓝 g, ∀ v, p i (T h v) ≤ q v := by
    intro g i
    obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
    have hb : BddAbove (range (fun k : K => (p i).comp (T k))) := by
      rw [Seminorm.bddAbove_range_iff]
      intro v
      obtain ⟨C, hC⟩ := hK.bddAbove_image ((hp.continuous_seminorm i).comp (horbit v)).continuousOn
      refine ⟨C, ?_⟩
      rintro _ ⟨k,rfl⟩
      exact hC ⟨k,k.property,rfl⟩
    let qs : K → Seminorm ℂ V := fun k => (p i).comp (T k)
    let q : Seminorm ℂ V := iSup qs
    have hc (k : K) : Continuous ((p i).comp (T k)) :=
      (hp.continuous_seminorm i).comp (hT k)
    have hq : Continuous q := by
      rw [show (q : V → ℝ) = ⨆ k, (qs k : V → ℝ) from Seminorm.coe_iSup_eq hb]
      exact Seminorm.continuous_iSup qs hc hb
    refine ⟨q, hq, ?_⟩
    filter_upwards [hKg] with h hh
    intro v
    exact (Seminorm.le_def.mp (le_ciSup hb ⟨h,hh⟩)) v
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, v⟩
  apply (hp.tendsto_nhds _ _).mpr
  intro i ε hε
  obtain ⟨q, hq, hb⟩ := hbound g i
  have hqzero : ContinuousAt (fun z : P × V => q (z.2 - v)) (g, v) :=
    (hq.comp (continuous_snd.sub continuous_const)).continuousAt
  have hsmall : ∀ᶠ z : P × V in 𝓝 (g, v), q (z.2 - v) < ε / 2 := by
    simpa using hqzero.eventually (Iio_mem_nhds (show q (v - v) < ε / 2 by
      simpa using half_pos hε))
  have ho : ∀ᶠ h in 𝓝 g, p i (T h v - T g v) < ε / 2 :=
    (hp.tendsto_nhds _ _).mp (horbit v).continuousAt i (ε / 2) (half_pos hε)
  have hb' : ∀ᶠ z : P × V in 𝓝 (g, v), ∀ w, p i (T z.1 w) ≤ q w :=
    (continuous_fst.continuousAt (x := (g, v))).tendsto.eventually hb
  have ho' : ∀ᶠ z : P × V in 𝓝 (g, v), p i (T z.1 v - T g v) < ε / 2 :=
    (continuous_fst.continuousAt (x := (g, v))).tendsto.eventually ho
  filter_upwards [hsmall, hb', ho'] with z hz hzb hzo
  have heq : T z.1 z.2 - T g v = T z.1 (z.2 - v) + (T z.1 v - T g v) := by
    rw [map_sub]
    abel
  rw [heq]
  exact map_add_le_add (p i) _ _ |>.trans_lt (by linarith [hzb (z.2 - v)])
end DedekindZetaZeroFree.KPCplxPrincipalSeriesJointBS
