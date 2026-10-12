module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.ArchimedeanInsertion
public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.RadialRelationTransport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology NNReal ENNReal
namespace DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource
open KPMsActualAngularSource KPMsActualAngularDomainSource

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

open KPMsActualAngularFixedRadiusRelationSource KPMsActualAngularDescentSource

private theorem positive_diagonal_action (c : ℝ) (hc : 0 < c) (q : KPArch.H3) :
    KPArch.action (KubotaRankTwo.d ℂ (Units.mk0 (c : ℂ) (by exact_mod_cast hc.ne')) 1) q =
      ((c : ℂ) * q.1, q.2 + Real.log c) := by
  apply Prod.ext
  · simp [KPArch.action, KPArch.actionDenominator, KubotaRankTwo.coe_d]
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KubotaRankTwo.coe_d, Matrix.det_fin_two]
    rw [abs_of_pos hc, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp, add_comm]
 def radialArch (w : NumberField.InfinitePlace F)
    (r : KPMsFixedHaarDisintegration.Radius) : KPSmoothActualFlowData.GInfinity F :=
  fun v => Matrix.ProjGenLinGroup.mk
    (KubotaRankTwo.d ℂ (Units.mk0
      (KPMsFixedHaarDisintegration.positiveSlots F w r v) (by
        unfold KPMsFixedHaarDisintegration.positiveSlots
        split_ifs
        · exact_mod_cast (Real.sqrt_pos.mpr r.property).ne'
        · exact one_ne_zero)) 1)

 theorem radialArch_insertion (w : NumberField.InfinitePlace F)
    (r : KPMsFixedHaarDisintegration.Radius) :
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (radialArch w r) =
      KPMsFixedHaarDisintegration.radialSection F ζ hζ w r := by
  apply KPContinuation.ChamberFlatCasimir.arch_diagonal_insertion

def radialCross (w : NumberField.InfinitePlace F)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (r : KPMsFixedHaarDisintegration.Radius) (p : KPCuspCharts.Cross F) : KPCuspCharts.Cross F :=
  (fun i => KPMsFixedHaarDisintegration.positiveSlots F w r (KPCusp.complexPlace F i) * p.1 i,
    p.2 + KPMsFixedHaarDisintegration.sectionShape F hF w r)

 theorem radialArch_action (w : NumberField.InfinitePlace F)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (r : KPMsFixedHaarDisintegration.Radius) (p : KPCuspCharts.Cross F) (t : ℝ) :
    (fun i => KPArch.action (radialArch w r (KPCusp.complexPlace F i)).out
      (KPCuspCharts.toArch F (p,t) i)) =
      KPCuspCharts.toArch F
        (radialCross w hF r p, t + KPMsFixedHaarDisintegration.logHeight (F := F) r.val) := by
  funext i
  rw [radialArch, projective_action_mk]
  by_cases hi : KPCusp.complexPlace F i = w
  · have hv : KPMsFixedHaarDisintegration.positiveSlots F w r (KPCusp.complexPlace F i) =
        (Real.sqrt r.val : ℂ) := by simp [KPMsFixedHaarDisintegration.positiveSlots, hi]
    simp only [hv]
    rw [positive_diagonal_action _ (Real.sqrt_pos.mpr r.property)]
    apply Prod.ext
    · simp [KPCuspCharts.toArch, radialCross, hv]
    · change t + (p.2 : _ → ℝ) i + Real.log (Real.sqrt r.val) =
        t + KPMsFixedHaarDisintegration.logHeight (F := F) r.val +
          ((p.2 : _ → ℝ) i + (KPMsFixedHaarDisintegration.sectionShape F hF w r : _ → ℝ) i)
      simp only [KPMsFixedHaarDisintegration.sectionShape,
        KPMsFixedHaarDisintegration.logHeight, hi, ite_true]
      rw [Real.log_sqrt r.property.le]
      ring
  · have hv : KPMsFixedHaarDisintegration.positiveSlots F w r (KPCusp.complexPlace F i) =
        (1 : ℂ) := by simp [KPMsFixedHaarDisintegration.positiveSlots, hi]
    simp only [hv]
    have he := positive_diagonal_action 1 (by norm_num : (0 : ℝ) < 1)
      (KPCuspCharts.toArch F (p,t) i)
    simp only [Complex.ofReal_one] at he
    rw [he]
    apply Prod.ext
    · simp [KPCuspCharts.toArch, radialCross, hv]
    · change t + (p.2 : _ → ℝ) i + Real.log 1 =
        t + KPMsFixedHaarDisintegration.logHeight (F := F) r.val +
          ((p.2 : _ → ℝ) i + (KPMsFixedHaarDisintegration.sectionShape F hF w r : _ → ℝ) i)
      simp only [KPMsFixedHaarDisintegration.sectionShape,
        KPMsFixedHaarDisintegration.logHeight, hi, ite_false, Real.log_one]
      ring

 theorem archBasepoint_radial_rescale
    (σ : KPCuspArithmetic.PGL2 F) (a : KPSmoothActualFlowData.GInfinity F)
    (w : NumberField.InfinitePlace F) (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (r : KPMsFixedHaarDisintegration.Radius) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    KPMsFixedHaarDisintegration.archBasepoint F
      (archRational σ * radialArch w r * (archRational σ)⁻¹ * a) =
        KPCuspSiegel.action F σ (KPCuspCharts.toArch F
          (radialCross w hF r p, t + KPMsFixedHaarDisintegration.logHeight (F := F) r.val)) := by
  rw [← archRational_action] at ha ⊢
  funext i
  rw [archBasepoint_mul]
  change KPArch.action ((archRational σ (KPCusp.complexPlace F i) *
    radialArch w r (KPCusp.complexPlace F i)) *
    (archRational σ (KPCusp.complexPlace F i))⁻¹).out
    (KPMsFixedHaarDisintegration.archBasepoint F a i) = _
  rw [ha, projective_action_mul, projective_action_mul, projective_action_inv_cancel]
  exact congrArg (KPArch.action (archRational σ (KPCusp.complexPlace F i)).out)
    (congrFun (radialArch_action w hF r p t) i)

 theorem radial_conjugation_split
    (σ : KPCuspArithmetic.PGL2 F) (w : NumberField.InfinitePlace F)
    (r : KPMsFixedHaarDisintegration.Radius) :
    KPMsActualCuspSource.rationalLift F ζ hζ σ * KPMsFixedHaarDisintegration.radialSection F ζ hζ w r *
      (KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (archRational σ * radialArch w r * (archRational σ)⁻¹) := by
  obtain ⟨v,hv⟩ := rationalLift_split F ζ hζ σ
  change KPMsActualCuspSource.rationalLift F ζ hζ σ = _ at hv
  rw [hv, ← radialArch_insertion (ζ := ζ) (hζ := hζ)]
  have hc := insertion_commutes_cover F ζ hζ (radialArch w r) v
  have hmul := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  let I : KPSmoothActualFlowData.GInfinity F →* KPSmoothActualFlowData.G F ζ hζ :=
    { toFun := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      map_one' := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
      map_mul' := hmul }
  have hinv (a : KPSmoothActualFlowData.GInfinity F) :
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a⁻¹ =
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)⁻¹ := map_inv I a
  simp only [hmul, hinv]
  calc
    _ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ) *
      (v.val * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (radialArch w r)) *
      (v.val⁻¹ * (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational σ))⁻¹) := by group
    _ = _ := by rw [← hc.eq]; group

 theorem sectionShape_mul
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) (r t : KPMsFixedHaarDisintegration.Radius) :
    KPMsFixedHaarDisintegration.sectionShape F hF w
      ⟨r.val * t.val, mul_pos r.property t.property⟩ =
      KPMsFixedHaarDisintegration.sectionShape F hF w r +
        KPMsFixedHaarDisintegration.sectionShape F hF w t := by
  apply Subtype.ext
  funext i
  change ((if KPCusp.complexPlace F i = w then Real.log (r.val * t.val) / 2 else 0) -
    Real.log (r.val * t.val) / (2 * (KPCuspLogShape.dimension F : ℝ))) =
    ((if KPCusp.complexPlace F i = w then Real.log r.val / 2 else 0) -
      Real.log r.val / (2 * (KPCuspLogShape.dimension F : ℝ))) +
    ((if KPCusp.complexPlace F i = w then Real.log t.val / 2 else 0) -
      Real.log t.val / (2 * (KPCuspLogShape.dimension F : ℝ)))
  rw [Real.log_mul r.property.ne' t.property.ne']
  split_ifs <;> ring

end DedekindZetaZeroFree.KPMsActualAngularRadialShapeSource

end
