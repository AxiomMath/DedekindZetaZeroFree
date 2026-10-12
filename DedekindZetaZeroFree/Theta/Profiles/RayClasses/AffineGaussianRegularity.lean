module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffineResiduePackets
public import DedekindZetaZeroFree.Theta.Profiles.GaussianSeriesContinuity
public import DedekindZetaZeroFree.Arithmetic.Ideals.TracePhaseAnnihilator

@[expose] public section

section

noncomputable section
open scoped NumberField nonZeroDivisors
open Classical MeasureTheory DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta
variable {F : Type} [Field F] [NumberField F]

private theorem summable_traceGaussian (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (z : NumberField.mixedEmbedding.euclidean.mixedSpace F) {a : ℝ} (ha : 0 < a) :
    Summable (fun l : {l : F // l ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
      Real.exp (-a * ‖z + Theta.traceEmbedding F l.val‖ ^ 2)) := by
  let f : {l : F // l ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} → Theta.traceIdealLattice F J :=
    fun l => ⟨Theta.traceEmbedding F l.val,
      (Theta.traceEmbedding_mem_traceIdealLattice F J).mpr l.property⟩
  have hf : Function.Injective f := by
    intro l k h
    apply Subtype.ext
    apply NumberField.mixedEmbedding_injective F
    exact (Theta.traceToMixed F).symm.injective (congrArg Subtype.val h)
  have hs := DedekindZetaZeroFree.summable_shiftedGaussian (Theta.traceIdealLattice F J) z ha
  have hs' := hs.comp_injective (i := f) hf
  exact hs'

private theorem summable_scaledTraceGaussian (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : F) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Summable (fun l : {l : F // l ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
      Real.exp (-a * ‖r • Theta.traceEmbedding F (x + l.val)‖ ^ 2)) := by
  have hs := summable_traceGaussian J (Theta.traceEmbedding F x)
    (mul_pos ha (sq_pos_of_pos hr))
  convert hs using 1
  ext l
  rw [← Theta.traceEmbeddingIntLinearMap_apply, map_add]
  simp only [Theta.traceEmbeddingIntLinearMap_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_pow]
  congr 1
  ring

private theorem affineResidueScale_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    0 < affineResidueScale I := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (show 0 < FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) from
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm
      (mt FractionalIdeal.absNorm_eq_zero_iff.mp (Units.ne_zero I))))

section Affine
variable (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (hu : 0 < u)
local notation "L" => {l : F // l ∈
  ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}
local notation "D" => {β : F // β ∈
  (Theta.traceDualIdealUnit F (I * rayIdealFractionalIdeal F m hm) :
    FractionalIdeal (𝓞 F)⁰ F)}
include hu

theorem affineResidueTheta_summable_norm (h : RayCoset.logHyperplane F) :
    Summable (fun l : L => ‖RayParity.gδ F ∅
      (RayParity.Q F (RayTheta.q F u h)
        (affineResidueScale I • Theta.traceEmbedding F (x.val + l.val)))‖) := by
  obtain ⟨P, c, hP, hc, hb⟩ := DedekindZetaZeroFree.thetaParityShapeBounds F ∅
    {h} (isCompact_singleton)
  have ha : 0 < c * u ^ (2 / (Module.finrank ℚ F : ℝ)) :=
    mul_pos hc (Real.rpow_pos_of_pos hu _)
  have hs := (summable_scaledTraceGaussian (I * rayIdealFractionalIdeal F m hm)
    x.val (affineResidueScale_pos I) ha).mul_left P
  apply hs.of_norm_bounded
  intro l
  unfold RayTheta.q
  simpa only [Real.norm_eq_abs, abs_norm, neg_mul, mul_assoc, one_div] using
    (hb u hu h (Set.mem_singleton h) (affineResidueScale I •
      Theta.traceEmbedding F (x.val + l.val))).1

theorem affineResidueDualTheta_summable_norm (h : RayCoset.logHyperplane F) :
    Summable (fun β : D => ‖rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)) *
      RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
        ((affineResidueScale I)⁻¹ •
          Theta.traceConjugation F (Theta.traceEmbedding F β.val)))‖) := by
  obtain ⟨P, c, hP, hc, hb⟩ := DedekindZetaZeroFree.thetaParityShapeBounds F ∅
    {h} isCompact_singleton
  have ha : 0 < c * u ^ (2 / (Module.finrank ℚ F : ℝ)) :=
    mul_pos hc (Real.rpow_pos_of_pos hu _)
  have hs := (summable_scaledTraceGaussian
    (Theta.traceDualIdealUnit F (I * rayIdealFractionalIdeal F m hm))
    0 (inv_pos.mpr (affineResidueScale_pos I)) ha).mul_left P
  apply hs.of_norm_bounded
  intro β
  have he : ‖(affineResidueScale I)⁻¹ • Theta.traceConjugation F
      (Theta.traceEmbedding F β.val)‖ =
      ‖(affineResidueScale I)⁻¹ • Theta.traceEmbedding F (0 + β.val)‖ := by
    simp only [zero_add, norm_smul, LinearIsometryEquiv.norm_map]
  unfold RayTheta.q
  simpa only [norm_mul, norm_rationalTracePhase, one_mul, Real.norm_eq_abs,
    abs_norm, neg_mul, mul_assoc, he, one_div] using
    (hb u hu h (Set.mem_singleton h) ((affineResidueScale I)⁻¹ •
      Theta.traceConjugation F (Theta.traceEmbedding F β.val))).2

theorem affineResidueTheta_continuous : Continuous (affineResidueTheta m hm I x u) := by
  have hs : ∀ a : ℝ, 0 < a → Summable (fun l : L =>
      Real.exp (-a * ‖affineResidueScale I • Theta.traceEmbedding F (x.val + l.val)‖ ^ 2)) :=
    fun a ha => summable_scaledTraceGaussian (I * rayIdealFractionalIdeal F m hm)
      x.val (affineResidueScale_pos I) ha
  have hc := AnalyticTailHelper.continuous_tsum_thetaParityShape F ∅ u hu
    (fun l : L => affineResidueScale I • Theta.traceEmbedding F (x.val + l.val))
    hs (fun _ => (1 : ℂ)) (C := 1) (by positivity) (by intro l; simp)
  unfold affineResidueTheta
  simpa only [one_mul] using hc

theorem affineResidueDualTheta_continuous :
    Continuous (affineResidueDualTheta m hm I x u) := by
  have hs : ∀ a : ℝ, 0 < a → Summable (fun β : D => Real.exp (-a *
      ‖(affineResidueScale I)⁻¹ • Theta.traceConjugation F (Theta.traceEmbedding F β.val)‖ ^ 2)) := by
    intro a ha
    simpa only [zero_add, norm_smul, LinearIsometryEquiv.norm_map] using
      summable_scaledTraceGaussian
        (Theta.traceDualIdealUnit F (I * rayIdealFractionalIdeal F m hm))
        0 (inv_pos.mpr (affineResidueScale_pos I)) ha
  have hc := AnalyticTailHelper.continuous_tsum_thetaParityShape F ∅ u hu
    (fun β : D => (affineResidueScale I)⁻¹ •
      Theta.traceConjugation F (Theta.traceEmbedding F β.val))
    hs (fun β => rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)))
    (C := 1) (by positivity) (by intro β; rw [norm_rationalTracePhase])
  exact hc.comp continuous_neg

theorem affineResidueTheta_integrableOn :
    IntegrableOn (affineResidueTheta m hm I x u)
      (RayCoset.rayUnitHalfOpenDomain F m hm) (Theta.normalizedLogHaar F) := by
  exact ((affineResidueTheta_continuous m hm I x u hu).continuousOn.integrableOn_compact
    (RayCoset.isCompact_closure_rayUnitHalfOpenDomain F m hm)).mono_set subset_closure

theorem affineResidueDualTheta_integrableOn :
    IntegrableOn (affineResidueDualTheta m hm I x u)
      (RayCoset.rayUnitHalfOpenDomain F m hm) (Theta.normalizedLogHaar F) := by
  exact ((affineResidueDualTheta_continuous m hm I x u hu).continuousOn.integrableOn_compact
    (RayCoset.isCompact_closure_rayUnitHalfOpenDomain F m hm)).mono_set subset_closure

theorem affineResidueTheta_congr
    (y : {y : F // y ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F))
    (h : RayCoset.logHyperplane F) :
    affineResidueTheta m hm I x u h = affineResidueTheta m hm I y u h := by
  let J := ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)
  let e : L ≃ L :=
    { toFun := fun l => ⟨l.val - (x.val - y.val), J.coeToSubmodule.sub_mem l.property hxy⟩
      invFun := fun l => ⟨l.val + (x.val - y.val), J.coeToSubmodule.add_mem l.property hxy⟩
      left_inv := fun l => Subtype.ext (sub_add_cancel l.val _)
      right_inv := fun l => Subtype.ext (add_sub_cancel_right l.val _) }
  unfold affineResidueTheta
  rw [← e.tsum_eq]
  apply tsum_congr
  intro l
  congr 4
  change x.val + (l.val - (x.val - y.val)) = y.val + l.val
  ring

theorem affineResidueDualTheta_congr
    (y : {y : F // y ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F))
    (h : RayCoset.logHyperplane F) :
    affineResidueDualTheta m hm I x u h = affineResidueDualTheta m hm I y u h := by
  unfold affineResidueDualTheta
  apply tsum_congr
  intro β
  congr 1
  have hp := tracePhase_eq_one_of_mem_dual
    ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)
    (Units.ne_zero (I * rayIdealFractionalIdeal F m hm)) hxy β.property
  have ht : Algebra.trace ℚ F (x.val * β.val) =
      Algebra.trace ℚ F ((x.val - y.val) * β.val) +
        Algebra.trace ℚ F (y.val * β.val) := by
    rw [← map_add]
    congr 1
    ring
  rw [ht, AddChar.map_add_eq_mul, hp, one_mul]

theorem affineResidueAverage_congr
    (y : {y : F // y ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)) :
    affineResidueAverage m hm I x u = affineResidueAverage m hm I y u := by
  unfold affineResidueAverage
  exact setIntegral_congr_fun (RayCoset.measurableSet_rayUnitHalfOpenDomain F m hm)
    (fun h _ => affineResidueTheta_congr m hm I x u hu y hxy h)

theorem affineResidueDualAverage_congr
    (y : {y : F // y ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)) :
    affineResidueDualAverage m hm I x u = affineResidueDualAverage m hm I y u := by
  unfold affineResidueDualAverage
  exact setIntegral_congr_fun (RayCoset.measurableSet_rayUnitHalfOpenDomain F m hm)
    (fun h _ => affineResidueDualTheta_congr m hm I x u hu y hxy h)
end Affine

section Weighted
variable (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) (hu : 0 < u)
include hF hm hmt hu

theorem weightedIdealBlock_summable_norm (h : RayCoset.logHyperplane F) :
    Summable (fun x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} =>
      ‖η (integralElementIdeal I x) *
        RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
          ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
            (-1 / (Module.finrank ℚ F : ℝ)) • Theta.traceEmbedding F x.val))‖) := by
  have ht : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hz : (0 : F) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := I.val.coeToSubmodule.zero_mem
  have hs := affineResidueTheta_summable_norm (⊤ : Ideal (𝓞 F)) ht I ⟨0, hz⟩ u hu h
  have hM : (I * rayIdealFractionalIdeal F (⊤ : Ideal (𝓞 F)) ht :
      FractionalIdeal (𝓞 F)⁰ F) = I.val := by simp
  let f : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} →
      {x : F // x ∈ ((I * rayIdealFractionalIdeal F ⊤ ht) : FractionalIdeal (𝓞 F)⁰ F)} :=
    fun x => ⟨x.val, hM.symm ▸ x.property⟩
  have hfi : Function.Injective f := by
   intro x y h
   apply Subtype.ext
   exact congrArg (fun z => z.val) h
  have hs' := hs.comp_injective hfi
  simp only [Function.comp_def, zero_add] at hs'
  apply Summable.of_nonneg_of_le (fun x => norm_nonneg _) _ hs'
  intro x
  rw [norm_mul]
  have hc := rayCharacter_norm_le_one F m hm η (integralElementIdeal I x)
  simpa [affineResidueScale, neg_div, one_div] using
    mul_le_mul_of_nonneg_right hc (norm_nonneg (RayParity.gδ F ∅
     (RayParity.Q F (RayTheta.q F u h) (affineResidueScale I • Theta.traceEmbedding F x.val))))

end Weighted

end DedekindZetaZeroFree.Hecke.Theta

end

end
