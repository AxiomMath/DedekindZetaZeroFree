module

public import DedekindZetaZeroFree.Theta.Periods.CompactOpenAdditiveLevel
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory KPGlobalResidualConstruction KPLiteralChamber
open scoped NumberField Classical Topology ContDiff
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem theta_left_chart_contDiffOn {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    ContDiffOn ℝ ∞ (fun x => T.theta v
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F R.A.zeta12
        R.A.primitive_zeta12 x * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqD, he⟩ :=
    literal_group_chart_local_transition F R.A.zeta12 R.A.primitive_zeta12 g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  exact (((T.smooth v 0 (Metric.mem_ball_self T.radius_pos)).2.1
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F R.A.zeta12
      R.A.primitive_zeta12 x₀ * g)).comp hq hqD).congr
      (fun x hx => congrArg (T.theta v) (he x hx)) |>.mono Set.inter_subset_right

theorem upperArch_eq_leftChart (x : mixedEmbedding.mixedSpace F) :
    KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) : KPAdeles F) =
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F R.A.zeta12
      R.A.primitive_zeta12 (fun w i =>
        if i = 0 then 0 else if i = 1 then 1 else
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w))
              ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x w)) := by
  unfold KPGlobalTorusFunctionData.N KPGlobalTorusBorelTwistCompatibility.groupArchChart
  congr 2
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inr p =>
    change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F R.A.zeta12 R.A.primitive_zeta12 _
  | inl w =>
    change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x w) = _
    simp [KPGlobalTorusBorelTwistCompatibility.groupArchTuple,
      KPStandardLocalRootLifts.LowerN_zero, KPStandardLocalRootLifts.A_one]
    congr 1
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm_apply_apply _).symm

theorem mixed_upper_coordinate (w : InfinitePlace F) (x : mixedEmbedding.mixedSpace F) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w))
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x w) =
      x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩ := by
  have h := congrArg (fun y : mixedEmbedding.mixedSpace F =>
    y.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
  exact h

theorem thetaFiber_arch_lift_contDiff {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    ContDiff ℝ ∞ (fun x : mixedEmbedding.mixedSpace F =>
      thetaFiber R T v g (smoothArchInclusion F x)) := by
  let c : mixedEmbedding.mixedSpace F → KPGlobalTorusBorelTwistCompatibility.GroupArch F :=
    fun x w i => if i = 0 then 0 else if i = 1 then 1 else
      x.2 ⟨w, KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w⟩
  have hc : ContDiff ℝ ∞ c := by
    apply contDiff_pi.mpr
    intro w
    apply contDiff_pi.mpr
    intro i
    dsimp only [c]
    split_ifs <;> fun_prop
  have hcd : Set.MapsTo c Set.univ (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    intro x _ w
    simp [c]
  have hs := (theta_left_chart_contDiffOn R T v g).comp hc.contDiffOn hcd
  apply contDiffOn_univ.mp
  convert hs using 1
  funext x
  rw [smoothArchInclusion, thetaFiber_mk, upperArch_eq_leftChart]
  congr 2
  congr 1
  funext w i
  dsimp only [c]
  split_ifs <;> try rfl
  exact mixed_upper_coordinate R w x

theorem thetaFiber_isArchSmooth {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    IsArchSmooth (thetaFiber R T v g) := by
  obtain ⟨K, hKc, hKo, hlev⟩ := thetaFiber_exists_compact_open_level R T v g
  apply (finiteLevel_smooth_iff K hKc hKo _ hlev).mpr
  unfold IsLevelTorusSmooth
  simpa only [smoothLevelPullback_mk K _ hlev] using thetaFiber_arch_lift_contDiff R T v g

end DedekindZetaZeroFree.OrbitExpansion

end
