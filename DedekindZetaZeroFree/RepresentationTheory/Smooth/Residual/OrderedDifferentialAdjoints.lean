module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.DifferentialWords.SmoothL2Space
public import DedekindZetaZeroFree.Analysis.InvariantFlows.L2IntegrationByParts

@[expose] public section

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPMsClearedTruncationL2
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy renaming word_flow_hasDerivAt → word_flow_hasDerivAt
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow → nativeFlow
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow_zero → nativeFlow_zero
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow_add → nativeFlow_add
private theorem continuous_slice {Y : Type*} [TopologicalSpace Y]
    (q : ℝ → Y → Y) (hq : Continuous (Function.uncurry q)) (t : ℝ) :
    Continuous (q t) := hq.comp (continuous_const.prodMk continuous_id)
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev adjointWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem smooth_word_adjoint_transfer
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (f g : smoothAllWordL2 R)
    (w₁ w₂ : List (KPSmoothActualFlowData.B F)) (b : KPSmoothActualFlowData.B F)
 :
    (∫ x, star (adjointWordDerivative (b :: w₁) f.val x) * adjointWordDerivative w₂ g.val x ∂ R.quotientHaar) =
      -(∫ x, star (adjointWordDerivative w₁ f.val x) * adjointWordDerivative (b :: w₂) g.val x ∂ R.quotientHaar) := by

  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : BorelSpace (X F ζ hζ) := ⟨rfl⟩
  let Γ := KPSmoothActualFlowData.rationalSubgroup F ζ hζ
  have hopen : IsOpenQuotientMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    MulAction.isOpenQuotientMap_quotientMk
  have hΓ : IsClosed (Γ : Set (G F ζ hζ)) :=
    (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1
  letI : T2Space (X F ζ hζ) :=
    (t2Space_iff_of_isOpenQuotientMap hopen).mpr (by
      convert hΓ.preimage (continuous_snd.mul continuous_fst.inv) using 1
      ext p
      exact Quotient.eq.trans (QuotientGroup.rightRel_apply (s := Γ)))
  letI : IsFiniteMeasureOnCompacts R.quotientHaar := ⟨fun K hK =>
    lt_top_iff_ne_top.mpr
      (KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry.quotientHaar_compact_ne_top R K hK)⟩
  letI : SecondCountableTopology (G F ζ hζ) := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : ContinuousConstSMul Γ (G F ζ hζ) := ⟨fun γ => continuous_const.mul continuous_id⟩
  letI : SecondCountableTopology (X F ζ hζ) := ContinuousConstSMul.secondCountableTopology
  letI : SigmaCompactSpace (X F ζ hζ) := by
    letI : SigmaCompactSpace (G F ζ hζ) := sigmaCompactSpace_of_locallyCompact_secondCountable
    rw [← isSigmaCompact_univ_iff]
    have hh := isSigmaCompact_range (continuous_quot_mk :
      Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ))
    change IsSigmaCompact (Set.range (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)) at hh
    rw [show Set.range (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) = Set.univ from
      Set.range_eq_univ.mpr Quotient.mk_surjective] at hh
    exact hh
  letI : SigmaFinite R.quotientHaar := SigmaFinite.of_isFiniteMeasureOnCompacts _
  let q : ℝ → X F ζ hζ → X F ζ hζ := nativeFlow (F := F) (ζ := ζ) (hζ := hζ) b.1 b.2
  have hq : Continuous (Function.uncurry q) :=
    (KPSmoothQuotientTranslationFlow.continuous_rightTranslation Γ).comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (KPSmoothActualFlowData.flow_properties F b).2.2).comp continuous_fst |>.prodMk continuous_snd)
  have qzero (x : X F ζ hζ) : q 0 x = x := nativeFlow_zero b.1 b.2 x
  have qadd (s t : ℝ) (x : X F ζ hζ) : q (s+t) x = q t (q s x) :=
    nativeFlow_add b.1 b.2 s t x
  have qleft (t : ℝ) (x : X F ζ hζ) : q (-t) (q t x) = x := by
    exact (qadd t (-t) x).symm.trans ((congrArg (fun s => q s x) (add_neg_cancel t)).trans (qzero x))
  have qright (t : ℝ) (x : X F ζ hζ) : q t (q (-t) x) = x := by
    exact (qadd (-t) t x).symm.trans ((congrArg (fun s => q s x) (neg_add_cancel t)).trans (qzero x))
  have qc (t : ℝ) : Continuous (q t) := continuous_slice q hq t
  let a : ℝ → X F ζ hζ ≃ₜ X F ζ hζ := fun t =>
    { toFun := q t
      invFun := q (-t)
      left_inv := qleft t
      right_inv := qright t
      continuous_toFun := qc t
      continuous_invFun := qc (-t) }
  exact ResidualGlobalFlowIBP.invariant_flow_l2_ibp (μ := R.quotientHaar) a hq
    (fun x => nativeFlow_zero b.1 b.2 x)
    (fun t => KPMsGreenFlux.ActualSharpStokes.quotient_flow_measurePreserving R b.1 b.2 t)
    (adjointWordDerivative w₁ f.val) (adjointWordDerivative (b :: w₁) f.val) (adjointWordDerivative w₂ g.val) (adjointWordDerivative (b :: w₂) g.val)
    (f.property w₁).1.1
    (f.property (b :: w₁)).1.1
    (g.property w₂).1.1
    (g.property (b :: w₂)).1.1
    (f.property w₁).2 (f.property (b :: w₁)).2 (g.property w₂).2 (g.property (b :: w₂)).2
    (fun t x => word_flow_hasDerivAt f.val (f.property []).1 w₁ b x t)
    (fun t x => word_flow_hasDerivAt g.val (g.property []).1 w₂ b x t)

theorem smooth_ordered_word_adjoint
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (f g : smoothAllWordL2 R) (w v : List (KPSmoothActualFlowData.B F)) :
    (∫ x, star (adjointWordDerivative w f.val x) * adjointWordDerivative v g.val x ∂ R.quotientHaar) =
      (-1 : ℂ)^w.length *
        (∫ x, star (f.val x) * adjointWordDerivative (w.reverse ++ v) g.val x ∂ R.quotientHaar) := by
  induction w generalizing v with
  | nil => simp [adjointWordDerivative, KPSmoothActualFlowData.wordDerivative]
  | cons b w ih =>
    rw [smooth_word_adjoint_transfer R f g w v b, ih]
    simp only [List.length_cons, pow_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    ring

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
