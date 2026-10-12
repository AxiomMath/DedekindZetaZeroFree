module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.LipschitzCutoffExhaustion
public import DedekindZetaZeroFree.Analysis.EnergyEstimates.WeakDiagonalEnergy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPMsClearedTruncationL2
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeWeakEnergy renaming weak_diagonal_energy_finite → weak_diagonal_energy_finite
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeCutoffExhaustion renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeCutoffExhaustion renaming cutoff_regular → cutoff_regular
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.NativeCutoffExhaustion renaming cutoff_tendsto_one → cutoff_tendsto_one
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow → nativeFlow
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow_zero → nativeFlow_zero
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes.WeakCutoffSources renaming nativeFlow_add → nativeFlow_add
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
 abbrev cutoffEnergyWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ
 abbrev FD := KPSmoothActualFlowData.flowDerivative F ζ hζ

 theorem word_flow_hasDerivAt (f : X F ζ hζ → ℂ)
    (hf : KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f)
    (word : List (KPSmoothActualFlowData.B F)) (b : KPSmoothActualFlowData.B F)
    (x : X F ζ hζ) (t : ℝ) :
    HasDerivAt (fun s => cutoffEnergyWordDerivative word f (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b s)) x))
      (cutoffEnergyWordDerivative (b :: word) f (KPSmoothActualFlowData.rightTranslate F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (KPSmoothActualFlowData.flow F b t)) x)) t := by
  let q : ℝ → X F ζ hζ → X F ζ hζ := fun s y =>
    KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F b s)) y
  have hadd (s t : ℝ) (y : X F ζ hζ) : q (s+t) y = q t (q s y) := by
    dsimp [q]
    rw [(KPSmoothActualFlowData.flow_properties F b).2.1,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    exact congrFun (KPSmoothQuotientTranslationFlow.rightTranslation_mul
      (KPSmoothActualFlowData.rationalSubgroup F ζ hζ) _ _) y
  have hsm (y : X F ζ hζ) : ContDiff ℝ (⊤ : ℕ∞) (fun s => cutoffEnergyWordDerivative word f (q s y)) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun s : ℝ => fun c : KPSmoothActualFlowData.B F => if c = b then s else 0) := by
      apply contDiff_pi.mpr
      intro c
      split_ifs <;> fun_prop
    exact (ActualWordLinearity.word_orbit_contDiff F ζ hζ f hf word y).comp hc
  exact KPSmoothQuotientTranslationFlow.scalar_orbit_derivative q hadd (cutoffEnergyWordDerivative word f) hsm x t

theorem original_diagonal_energy_finite
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    {U₀ : Level F ζ hζ} (f : smoothSpace F ζ hζ U₀)
    (c : KPSmoothActualFlowData.B F → ℝ) (hc : ∀ b, 0 ≤ c b)
    (hf2 : MemLp f.val 2 R.quotientHaar)
    (hv2 : MemLp (fun x => ∑ b, (c b : ℂ) * cutoffEnergyWordDerivative [b,b] f.val x) 2 R.quotientHaar) :
    (∫⁻ x, ENNReal.ofReal (∑ b, c b * ‖FD b f.val x‖ ^ 2) ∂ R.quotientHaar) < ⊤ := by
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
  let q : KPSmoothActualFlowData.B F → ℝ → X F ζ hζ → X F ζ hζ := fun b => nativeFlow b.1 b.2
  have hq (b : KPSmoothActualFlowData.B F) : Continuous (Function.uncurry (q b)) :=
    (KPSmoothQuotientTranslationFlow.continuous_rightTranslation Γ).comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        (KPSmoothActualFlowData.flow_properties F b).2.2).comp continuous_fst |>.prodMk continuous_snd)
  let χ : ℕ → X F ζ hζ → ℝ := fun n x => (cutoff A R P D Y n x).re
  have hχeq (n : ℕ) (x : X F ζ hζ) : (χ n x : ℂ) = cutoff A R P D Y n x := by
    rfl
  have hχ (n : ℕ) : Continuous (χ n) := Complex.continuous_re.comp (cutoff_regular A R P D Y hY n).1
  have hχc (n : ℕ) : HasCompactSupport (χ n) :=
    (cutoff_regular A R P D Y hY n).2.1.comp_left (show Complex.re 0 = 0 by rfl)
  have hχb (n : ℕ) (x : X F ζ hζ) : |χ n x| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans ((cutoff_regular A R P D Y hY n).2.2.1 x)
  have hχlim (x : X F ζ hζ) : Filter.Tendsto (fun n => χ n x) Filter.atTop (𝓝 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp (cutoff_tendsto_one A R P D Y hY x) using 1
    funext n; rfl
  have hLip (n : ℕ) (b : KPSmoothActualFlowData.B F) (x : X F ζ hζ) :
      LipschitzWith 8 (fun t => (χ n (q b t x) : ℂ)) := by
    simp_rw [hχeq]
    exact (cutoff_regular A R P D Y hY n).2.2.2 b.1 b.2 x
  have hw (w : List (KPSmoothActualFlowData.B F)) : Continuous (cutoffEnergyWordDerivative w f.val) :=
    (smoothDerivatives F ζ hζ U₀ w f).continuous
  exact weak_diagonal_energy_finite q hq
    (fun b t => KPMsGreenFlux.ActualSharpStokes.quotient_flow_measurePreserving R b.1 b.2 t)
    (fun b => nativeFlow_zero b.1 b.2) (fun b => nativeFlow_add b.1 b.2)
    c hc f.val (fun x => ∑ b, (c b : ℂ) * cutoffEnergyWordDerivative [b,b] f.val x)
    (fun b => FD b f.val) (fun b => cutoffEnergyWordDerivative [b,b] f.val)
    f.property.1.1 (fun b => hw [b]) (fun b => hw [b,b])
    (fun b x t => word_flow_hasDerivAt f.val f.property.1 [] b x t)
    (fun b x t => word_flow_hasDerivAt f.val f.property.1 [b] b x t)
    (fun x => rfl) hf2 hv2 χ hχ hχc hχb hχlim 8 hLip
end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
