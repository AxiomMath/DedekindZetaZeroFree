module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent
public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod
open MomentSources KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem cleared_chart_joint_continuousOn (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) (C : Set (ArchCoordinates F)) (hC : IsCompact C)
    (hCd : C ⊆ archDomain F) (r : ℝ) (hr : 0 < r) (hrR : r < T.radius) :
    ContinuousOn (fun p : ℂ × ArchCoordinates F =>
      T.cleared v p.1 (g * archChart F R.A.zeta12 R.A.primitive_zeta12 p.2))
      (Metric.closedBall (0 : ℂ) r ×ˢ C) := by
  let P : ℕ → ℂ × ArchCoordinates F → ℂ := fun M p =>
    ∑ n ∈ Finset.range M, p.1 ^ n * T.coefficients v n
      (g * archChart F R.A.zeta12 R.A.primitive_zeta12 p.2)
  have ht : TendstoUniformlyOn P (fun p : ℂ × ArchCoordinates F =>
      T.cleared v p.1 (g * archChart F R.A.zeta12 R.A.primitive_zeta12 p.2)) atTop
      (Metric.closedBall (0 : ℂ) r ×ˢ C) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := T.compact_smooth_taylor v g 0 C hC hCd r hr hrR ε hε
    filter_upwards [eventually_ge_atTop N] with M hM p hp
    rw [dist_eq_norm]
    simpa only [norm_iteratedFDeriv_zero, P] using
      hN M hM p.1 (by simpa using hp.1) p.2 hp.2
  have hP (M : ℕ) : ContinuousOn (P M) (Metric.closedBall (0 : ℂ) r ×ˢ C) := by
    apply continuousOn_finset_sum
    intro n hn
    have hc := (T.coefficients_smooth v n).2.1 g
    exact (continuous_fst.pow n).continuousOn.mul
      (hc.continuousOn.mono hCd |>.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  exact ht.continuousOn (Eventually.of_forall hP).frequently

theorem cleared_joint_continuous (T : Realization R Q) (v : R.A.UnitQuotient) :
    Continuous (fun p : Metric.ball (0 : ℂ) T.radius × Group R => T.cleared v p.1.val p.2) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨V, hVo, hbV, hVD, _, _, _, hthick, _⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product
      F R.A.zeta12 R.A.primitive_zeta12
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨r, hsr, hrR⟩ := exists_between (show ‖p.1.val‖ < T.radius by simpa only [Metric.mem_ball, dist_zero_right] using p.1.property)
  have hr : 0 < r := (norm_nonneg _).trans_lt hsr
  obtain ⟨δ, hδ, hδV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hVo.mem_nhds hbV)
  have hCd : Metric.closedBall (archBase F) δ ⊆ archDomain F := hδV.trans hVD
  have hc := cleared_chart_joint_continuousOn T v p.2 _ (isCompact_closedBall _ _) hCd r hr hrR
  have hcp : (p.1.val, archBase F) ∈ Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (archBase F) δ :=
    ⟨by simpa using hsr.le, Metric.mem_closedBall_self hδ.le⟩
  have hcn : Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (archBase F) δ ∈
      𝓝 (p.1.val, archBase F) := by
    rw [nhds_prod_eq]
    have hsN : Metric.closedBall (0 : ℂ) r ∈ 𝓝 p.1.val :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_zero_right] using hsr))
        Metric.ball_subset_closedBall
    exact prod_mem_prod hsN (Metric.closedBall_mem_nhds _ hδ)
  have hcAt := (hc _ hcp).continuousAt hcn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ q : ℂ × ArchCoordinates F in 𝓝 (p.1.val, archBase F),
      dist (T.cleared v q.1 (p.2 * archChart F R.A.zeta12 R.A.primitive_zeta12 q.2))
        (T.cleared v p.1.val p.2) < ε := by
    simpa only [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] using
      (Metric.tendsto_nhds.mp hcAt ε hε)
  change {q : ℂ × ArchCoordinates F | dist
    (T.cleared v q.1 (p.2 * archChart F R.A.zeta12 R.A.primitive_zeta12 q.2))
    (T.cleared v p.1.val p.2) < ε} ∈ 𝓝 (p.1.val, archBase F) at he
  rw [nhds_prod_eq, Filter.mem_prod_iff] at he
  obtain ⟨A, hA, B, hB, hAB⟩ := he
  obtain ⟨W, hWB, hWo, hbW⟩ := mem_nhds_iff.mp (inter_mem hB (hVo.mem_nhds hbV))
  have hWb : W ⊆ B := hWB.trans Set.inter_subset_left
  have hWV : W ⊆ V := hWB.trans Set.inter_subset_right
  have hgN := hthick W hWo hbW hWV Q.level
  have hsN : ∀ᶠ q : Metric.ball (0 : ℂ) T.radius × Group R in 𝓝 p, q.1.val ∈ A :=
    ((continuous_subtype_val.comp continuous_fst).continuousAt).preimage_mem_nhds hA
  have hgN' : ∀ᶠ q : Metric.ball (0 : ℂ) T.radius × Group R in 𝓝 p,
      p.2⁻¹ * q.2 ∈ {g | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel
        F R.A.zeta12 R.A.primitive_zeta12 Q.level,
        g = archChart F R.A.zeta12 R.A.primitive_zeta12 y * u} := by
    exact (show Continuous (fun q : Metric.ball (0 : ℂ) T.radius × Group R => p.2⁻¹ * q.2)
      from continuous_const.mul continuous_snd).continuousAt.preimage_mem_nhds
        (by simpa using hgN)
  filter_upwards [hsN, hgN'] with q hqA hqG
  obtain ⟨y, hy, u, hu, heq⟩ := hqG
  have hq : q.2 = (p.2 * archChart F R.A.zeta12 R.A.primitive_zeta12 y) * u := by
    calc
      q.2 = p.2 * (p.2⁻¹ * q.2) := by simp
      _ = _ := by rw [heq, mul_assoc]
  rw [hq, T.common_cleared_level v q.1.val q.1.property _ u hu]
  exact hAB (show (q.1.val, y) ∈ A ×ˢ B from ⟨hqA, hWb hy⟩)

theorem cleared_quotient_joint_continuous (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    Continuous (fun p : Metric.ball (0 : ℂ) T.radius × KPAdditiveQuotient F =>
      T.cleared v p.1.val
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.2) * g)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id (X := Metric.ball (0 : ℂ) T.radius)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
  have hc : Continuous (fun p : Metric.ball (0 : ℂ) T.radius × KPAdeles F =>
      T.cleared v p.1.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 p.2 * g)) :=
    (cleared_joint_continuous T v).comp
    (continuous_fst.prodMk
      (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
        F R.A.zeta12 R.A.primitive_zeta12).comp
        (continuous_snd : Continuous (Prod.snd : Metric.ball (0 : ℂ) T.radius × KPAdeles F → KPAdeles F))).mul continuous_const))
  simpa only [Function.comp_def, Prod.map, id_eq, cleared_integrand_mk T v _ (Subtype.property _),
    Pi.mul_apply] using hc

theorem upper_cleared_continuousOn (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    ContinuousOn (fun s => upper R Q.dq (T.cleared v s) g) (Metric.ball (0 : ℂ) T.radius) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun s : Metric.ball (0 : ℂ) T.radius => ∫ q : KPAdditiveQuotient F,
    T.cleared v s.val
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) ∂Q.dq)
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
  · exact (cleared_quotient_joint_continuous T v g).continuousOn
  · intro p x hp hx
    exact False.elim (hx (Set.mem_univ x))

theorem upper_cleared_continuousAt_zero (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    ContinuousAt (fun s => upper R Q.dq (T.cleared v s) g) 0 :=
  (upper_cleared_continuousOn T v g 0 (Metric.mem_ball_self T.radius_pos)).continuousAt
    (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos)

end DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

end
