module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AdelicAction.TwoSidedJets
public import DedekindZetaZeroFree.Eisenstein.Residues.SmoothOrbitsAndRightJets
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory Filter
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources KPGlobalResidualConstruction
open CanonicalComplexSmoothAction.TranslatedGenerators.NativeApproximation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem theta_quotient_joint_continuous (T : Realization R Q) (v : R.A.UnitQuotient) :
    Continuous (fun p : KPAdditiveQuotient F × Group R => T.theta v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out p.1) * p.2)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((QuotientAddGroup.isOpenQuotientMap_mk
    (N := AdeleRing.principalSubgroup (𝓞 F) F)).prodMap
    (IsOpenQuotientMap.id (X := Group R))).continuous_comp_iff.mp
  have hc := (T.smooth v 0 (Metric.mem_ball_self T.radius_pos)).1.comp
    (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).comp
        (continuous_fst : Continuous (Prod.fst : KPAdeles F × Group R → KPAdeles F))).mul continuous_snd)
  simpa only [Function.comp_def, Prod.map, id_eq, Realization.theta, Pi.mul_apply,
    CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0 (Metric.mem_ball_self T.radius_pos)] using hc

def thetaQuotientChart (T : Realization R Q) (v : R.A.UnitQuotient)
    (g a : Group R) (x : ArchCoordinates F) : C(KPAdditiveQuotient F, ℂ) :=
  ⟨fun q => T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * a)),
    CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_continuous T v 0
      (Metric.mem_ball_self T.radius_pos) _⟩

theorem theta_quotient_chart_jets (T : Realization R Q) (v : R.A.UnitQuotient)
    (g a : Group R) (n : ℕ) :
    ContinuousOn (fun p : ArchCoordinates F × KPAdditiveQuotient F => iteratedFDeriv ℝ n
      (fun x => T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out p.2) * ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * a))) p.1)
      (archDomain F ×ˢ Set.univ) := by
  let q : KPAdeles F → KPAdditiveQuotient F := QuotientAddGroup.mk
  let H := fun p : archDomain F × KPAdditiveQuotient F => iteratedFDeriv ℝ n
    (fun x => T.theta v (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out p.2) * ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * a))) p.1.val
  have hc := two_sided_adelic_spatial_jets F R.A.zeta12 R.A.primitive_zeta12
    (T.theta v) (T.smooth v 0 (Metric.mem_ball_self T.radius_pos))
    (fun b : KPAdeles F => KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 b * g)
    (fun _ => a)
    ((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).mul continuous_const) continuous_const n
  have hH : Continuous H := by
    apply (((IsOpenQuotientMap.id (X := archDomain F)).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk
        (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff (g := H)).mp
    have hs := hc.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
      (show Set.MapsTo (fun p : archDomain F × KPAdeles F => (p.1.val, p.2)) Set.univ
        (archDomain F ×ˢ Set.univ) from fun p _ => ⟨p.1.property, Set.mem_univ _⟩)
    have he : H ∘ Prod.map id q = (fun p : archDomain F × KPAdeles F => iteratedFDeriv ℝ n
      (fun x => T.theta v ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 p.2 * g) *
        archChart F R.A.zeta12 R.A.primitive_zeta12 x * a)) p.1.val) := by
      funext p
      change iteratedFDeriv ℝ n _ p.1.val = iteratedFDeriv ℝ n _ p.1.val
      apply congrArg (fun f : ArchCoordinates F → ℂ => iteratedFDeriv ℝ n f p.1.val)
      funext x
      simpa only [H, q, Prod.map, id_eq, Function.comp_def, Realization.theta, mul_assoc] using
        CompactPeriodAnalyticity.CompactPeriod.cleared_integrand_mk T v 0 (Metric.mem_ball_self T.radius_pos) p.2
          ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * a)
    rw [he]
    simpa only [Function.comp_def, Prod.map, id_eq, continuousOn_univ] using hs
  let e : (archDomain F ×ˢ (Set.univ : Set (KPAdditiveQuotient F))) →
      archDomain F × KPAdditiveQuotient F := fun p => (⟨p.val.1, p.property.1⟩, p.val.2)
  have he : Continuous e := by
    apply Continuous.prodMk
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1)
    · exact continuous_snd.comp continuous_subtype_val
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (H ∘ e)
  exact hH.comp he

theorem thetaQuotientChart_contDiffOn (T : Realization R Q) (v : R.A.UnitQuotient)
    (g a : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (thetaQuotientChart T v g a) (archDomain F) := by
  apply ActualNativeActionGeometry.compact_family_contDiffOn_of_joint_jets
    _ _ (ActualDifferentialData.archDomain_isOpen F)
  · intro q
    have hs := KPLiteralPeriod.NonzeroResidue.smooth_right_translate
      F R.A.zeta12 R.A.primitive_zeta12 (T.theta v)
      (T.smooth v 0 (Metric.mem_ball_self T.radius_pos)) a
    have h := hs.2.1 (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun x => T.theta v
      ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        archChart F R.A.zeta12 R.A.primitive_zeta12 x * a)) (archDomain F) at h
    simpa only [thetaQuotientChart, ContinuousMap.coe_mk, mul_assoc] using h
  · exact theta_quotient_chart_jets T v g a

def fourierExtraction (R : PrincipalMellin.ActualRecipe S η)
    (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq] :
    C(KPAdditiveQuotient F, ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ q, h q * star (adelicTraceQuotientCharacter F q : ℂ) ∂dq
      map_add' := fun h k => by
        simp only [ContinuousMap.add_apply, add_mul]
        apply integral_add
        all_goals
          exact (Continuous.mul (by fun_prop)
            ((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
      map_smul' := fun c h => by
        simp only [ContinuousMap.smul_apply, smul_mul_assoc]
        exact integral_smul c _ }
    (dq.real Set.univ) (fun h => by
      change ‖∫ q, h q * star (adelicTraceQuotientCharacter F q : ℂ) ∂dq‖ ≤ dq.real Set.univ * ‖h‖
      rw [mul_comm]
      apply norm_integral_le_of_norm_le_const
      apply Eventually.of_forall
      intro q
      simpa only [norm_mul, norm_star, Circle.norm_coe, mul_one] using h.norm_coe_le_norm q)

theorem fourier_chart_contDiffOn (T : Realization R Q) (v : R.A.UnitQuotient)
    (g a : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fourier R Q.dq (T.theta v)
      ((g * archChart F R.A.zeta12 R.A.primitive_zeta12 x) * a)) (archDomain F) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact (fourierExtraction R Q.dq).contDiff.comp_contDiffOn (thetaQuotientChart_contDiffOn T v g a)

theorem fourier_continuous (T : Realization R Q) (v : R.A.UnitQuotient) :
    Continuous (fourier R Q.dq (T.theta v)) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
  · exact (((theta_quotient_joint_continuous T v).comp continuous_swap).mul
      (((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star).comp continuous_snd)).continuousOn
  · intro p x hp hx
    exact False.elim (hx (Set.mem_univ x))
end DedekindZetaZeroFree.SheetRescaling

end
