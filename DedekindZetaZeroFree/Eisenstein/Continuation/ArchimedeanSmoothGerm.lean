module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteLevelSmoothGerm

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff BigOperators
open Filter
namespace DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource
open MomentSources ArchSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q} {v : R.A.UnitQuotient}

theorem constructed_arch_germ (H : ScalarGerm C v) :
    ∃ (f : ℂ → ArchSeries.space F R.A.zeta12 R.A.primitive_zeta12) (r : ℝ),
      0 < r ∧ r ≤ H.radius ∧
      KPGlobalEisensteinData.SmoothHolomorphicOn
        (ArchSeries.jets F R.A.zeta12 R.A.primitive_zeta12) f (Metric.ball 0 r) ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, (f s).val = (H.cleared s : Functions R) := by
  letI : T2Space (Group R) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
    F R.A.zeta12 R.A.primitive_zeta12).1
  letI : LocallyCompactSpace (Group R) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
    F R.A.zeta12 R.A.primitive_zeta12).2.1
  letI : IsTopologicalGroup (Group R) := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
    F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  obtain ⟨D,hD,hpositive,P,⟨L⟩⟩ := kp_ms_fixed_haar_disintegration F R.A.zeta12
    R.A.primitive_zeta12 (MeasureTheory.Measure.haar : MeasureTheory.Measure (Group R)) inferInstance
  obtain ⟨L₀⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data
    F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨I,_⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists
    F R.A.zeta12 R.A.primitive_zeta12 L₀
  obtain ⟨d,E,T,t,hd,hd0,hE,hEc,ht,hb,hdne,hclear,hT⟩ :=
    ArchSeries.finite_germ F R.A.zeta12 R.A.primitive_zeta12 I D P L Q.K Q.iwasawa (Q.flat v)
  let r := min t H.radius
  have hr : 0 < r := lt_min ht H.radius_pos
  have hrt : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 t := Metric.ball_subset_ball (min_le_left _ _)
  have hrH : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 H.radius := Metric.ball_subset_ball (min_le_right _ _)
  let f := fun s => (d s)⁻¹ • T s
  have hf : KPGlobalEisensteinData.SmoothHolomorphicOn
      (ArchSeries.jets F R.A.zeta12 R.A.primitive_zeta12) f (Metric.ball 0 r) := by
    apply KPGlobalResidualConstruction.AnalyticScalarMultiplication.holomorphic_smul
      _ Metric.isOpen_ball
    · exact (hd.mono (hrt.trans hb)).inv (fun s hs => hdne s (hrt hs))
    · intro s hs
      obtain ⟨a,ha,haO,b,hb⟩ := hT s (hrt hs)
      obtain ⟨c,hc,hcO⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball s hs
      exact ⟨min a c,lt_min ha hc,(Metric.ball_subset_ball (min_le_right _ _)).trans hcO,b,
        KPGlobalResidualConstruction.SmoothSeriesAlgebra.powerSeries_mono _ hb (min_le_left _ _)⟩
  refine ⟨f,r,hr,min_le_right _ _,hf,?_⟩
  intro s hs
  funext g
  have he : (fun z => E z g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => d z * C.E v z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (hE g) (hd.meromorphicOn.mul (C.meromorphic v g))
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain ⟨1,by norm_num⟩ ?_
      (by norm_num [KPContinuation.spectralDomain])
    intro z hz
    change E z g = d z * C.E v z g
    rw [hEc z hz, C.chamber v z hz]
  have hen : (fun z => (f z).val g) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => H.cleared z g) := by
    filter_upwards [he,nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hzball hzne
    have ht := congrFun (hclear z (hrt hzball) hzne) g
    have hh := congrFun (H.clears z (hrH hzball) hzne) g
    change (T z).val g = z * E z g at ht
    change H.cleared z g = z * C.E v z g at hh
    change (d z)⁻¹ * (T z).val g = H.cleared z g
    rw [ht,hz,hh]
    field_simp [hdne z (hrt hzball)]
  exact (ArchSeries.holomorphic_scalar _ _ _ hf g).eqOn_of_preconnected_of_frequently_eq
    ((H.analytic g).mono hrH) (convex_ball (0 : ℂ) r).isPreconnected
    (Metric.mem_ball_self hr) hen.frequently hs

end DedekindZetaZeroFree.EisensteinSmoothGerms.SmoothSource

end
