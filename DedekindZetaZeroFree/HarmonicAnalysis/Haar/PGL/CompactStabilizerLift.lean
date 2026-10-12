module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLHyperbolic.CompactStabilizer

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

noncomputable section
open scoped Classical ENNReal
open MeasureTheory

 def cocycle (d : ℕ) (a : G d) (x : X d) : K d :=
  ⟨(KPArithmeticAction.productProjectiveSection d (a • x))⁻¹ * a *
    KPArithmeticAction.productProjectiveSection d x, by
    change ((KPArithmeticAction.productProjectiveSection d (a • x))⁻¹ * a *
      KPArithmeticAction.productProjectiveSection d x) • o d = o d
    rw [mul_smul, mul_smul]
    change (KPArithmeticAction.productProjectiveSection d (a • x))⁻¹ •
      (a • (KPArithmeticAction.productProjectiveSection d x • (fun _ => (0, 0)))) = _
    rw [KPArithmeticAction.productProjectiveSection_action]
    apply inv_smul_eq_iff.mpr
    exact (KPArithmeticAction.productProjectiveSection_action d (a • x)).symm⟩

set_option maxHeartbeats 800000 in
 theorem cocycle_continuous (d : ℕ) (a : G d) : Continuous (cocycle d a) := by
  have hc : Continuous (fun x : X d =>
      (KPArithmeticAction.productProjectiveSection d (a • x))⁻¹ * a *
        KPArithmeticAction.productProjectiveSection d x) := by
    have hs := KPArithmeticAction.productProjectiveSection_continuous d
    have ha : Continuous (fun x : X d => a • x) := continuous_const_smul a
    have hb : Continuous (fun x : X d =>
      (KPArithmeticAction.productProjectiveSection d (a • x))⁻¹) := (hs.comp ha).inv
    have hm : Continuous (fun x : X d =>
      (KPArithmeticAction.productProjectiveSection d (a • x))⁻¹ * a) := hb.mul_const a
    exact hm.mul hs
  exact hc.subtype_mk (fun x => (cocycle d a x).property)

set_option maxHeartbeats 800000 in

theorem compact_fiber_lift_isHaar (d : ℕ)
    (e : G d ≃ₜ (X d × K d))
    (he : ∀ x k, e.symm (x, k) =
      KPArithmeticAction.productProjectiveSection d x * (k : G d))
    (ν : Measure (X d))
    (hfinite : IsFiniteMeasureOnCompacts ν)
    (hpositive : ν.IsOpenPosMeasure)
    (hinvariant : SMulInvariantMeasure (G d) (X d) ν)
    (dk : Measure (K d)) (hdk : dk.IsHaarMeasure)
    (hprob : IsProbabilityMeasure dk) :
    (Measure.map e.symm (ν.prod dk)).IsHaarMeasure := by
  have :=  hfinite
  have :=  hpositive
  have :=  hinvariant
  have :=  hdk
  have :=  hprob
  have : IsFiniteMeasureOnCompacts (Measure.map e.symm (ν.prod dk)) :=
    Measure.IsFiniteMeasureOnCompacts.map (ν.prod dk) e.symm
  have : (Measure.map e.symm (ν.prod dk)).IsOpenPosMeasure :=
    e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  refine { map_mul_left_eq_self := fun a => ?_ }
  have hgm : Measurable (Function.uncurry (fun x k => cocycle d a x * k)) := by
    exact (((cocycle_continuous d a).comp continuous_fst).mul continuous_snd).measurable
  have hp := (measurePreserving_smul a ν).skew_product hgm
    (Filter.Eventually.of_forall (fun x => map_mul_left_eq_self dk (cocycle d a x)))
  have hh : (fun p : X d × K d => e.symm (a • p.1, cocycle d a p.1 * p.2)) =
      (fun p : X d × K d => a * e.symm p) := by
    funext p
    rw [he, he]
    change KPArithmeticAction.productProjectiveSection d (a • p.1) *
      (((KPArithmeticAction.productProjectiveSection d (a • p.1))⁻¹ * a *
        KPArithmeticAction.productProjectiveSection d p.1) * (p.2 : G d)) = _
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [Measure.map_map (measurable_const_mul a) e.symm.measurable]
  have hh' := congrArg (Measure.map e.symm) hp.map_eq
  rw [Measure.map_map e.symm.measurable hp.measurable] at hh'
  simpa only [Function.comp_def, hh] using hh'

end

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
