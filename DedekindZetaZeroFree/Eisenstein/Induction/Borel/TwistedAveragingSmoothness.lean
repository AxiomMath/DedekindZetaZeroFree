module

public import DedekindZetaZeroFree.Metaplectic.Torus.Averaging.WeightedChartExtension
public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingContinuity

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Topology ContDiff

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

theorem integral_contDiffOn_of_locally_dominated_jets
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (F : E → X → ℂ) (S : Set E) (hS : IsOpen S)
    (hsmooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (fun u => F u x) S)
    (hmeas : ∀ n : ℕ, ∀ u ∈ S,
      AEStronglyMeasurable (fun x => iteratedFDerivWithin ℝ n (fun v => F v x) S u) μ)
    (hbound : ∀ n : ℕ, ∀ u ∈ S, ∃ (s : Set E) (b : X → ℝ),
      s ∈ nhds u ∧ s ⊆ S ∧ Integrable b μ ∧
        ∀ᵐ x ∂μ, ∀ v ∈ s, ‖iteratedFDerivWithin ℝ n (fun w => F w x) S v‖ ≤ b x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u => ∫ x, F u x ∂μ) S ∧
      ∀ n : ℕ, ∀ u ∈ S,
        iteratedFDerivWithin ℝ n (fun v => ∫ x, F v x ∂μ) S u =
          ∫ x, iteratedFDerivWithin ℝ n (fun v => F v x) S u ∂μ := by
  have hint (n : ℕ) (u : E) (hu : u ∈ S) :
      Integrable (fun x => iteratedFDerivWithin ℝ n (fun v => F v x) S u) μ := by
    obtain ⟨s, b, hs, _, hb, h⟩ := hbound n u hu
    exact hb.mono' (hmeas n u hu) (h.mono fun x hx => hx u (mem_of_mem_nhds hs))
  let A (n : ℕ) (u : E) := ∫ x, iteratedFDerivWithin ℝ n (fun v => F v x) S u ∂μ
  have hd (n : ℕ) (u : E) (hu : u ∈ S) : HasFDerivAt (A n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ) (A (n + 1) u)) u := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    obtain ⟨s, b, hs, hsS, hb, h⟩ := hbound (n + 1) u hu
    have hf'm : AEStronglyMeasurable (fun x =>
        fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun v => F v x) S) S u) μ := by
      exact L.continuous.comp_aestronglyMeasurable (hmeas (n + 1) u hu)
    have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F := fun v x => iteratedFDerivWithin ℝ n (fun w => F w x) S v)
      (F' := fun v x => fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun w => F w x) S) S v)
      hs (Filter.eventually_of_mem (hS.mem_nhds hu) (fun v hv => hmeas n v hv)) (hint n u hu) hf'm
      (h.mono fun x hx v hv => by
        change ‖L (iteratedFDerivWithin ℝ (n + 1) (fun w => F w x) S v)‖ ≤ b x
        rw [L.norm_map]
        exact hx v hv) hb
      (Eventually.of_forall fun x v hv =>
        (((hsmooth x).differentiableOn_iteratedFDerivWithin (m := n)
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) hS.uniqueDiffOn v (hsS hv)).hasFDerivWithinAt
          |>.hasFDerivAt (hS.mem_nhds (hsS hv))))
    have heq : (∫ x, fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun v => F v x) S) S u ∂μ) =
        L (A (n + 1) u) := by
      letI : TopologicalSpace (E [×(n + 1)]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E [×(n + 1)]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      let Lc : (E [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        { toLinearMap := L.toLinearEquiv.toLinearMap
          cont := by convert L.continuous using 1 }
      exact @ContinuousLinearMap.integral_comp_comm X (E [×(n + 1)]→L[ℝ] ℂ)
        (E →L[ℝ] E [×n]→L[ℝ] ℂ) _ μ ℝ _ _ _ _ _ _ _ _ _ Lc _ (hint (n + 1) u hu)
    rw [heq] at hh
    exact hh
  have heq (n : ℕ) : Set.EqOn (iteratedFDerivWithin ℝ n (fun u => ∫ x, F u x ∂μ) S) (A n) S := by
    induction n with
    | zero =>
      intro u hu
      simpa [A, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply] using
        ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (μ := μ) (F u)).symm
    | succ n ih =>
      intro u hu
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
        fderivWithin_congr ih (ih hu), (hd n u hu).hasFDerivWithinAt.fderivWithin (hS.uniqueDiffOn u hu)]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ).symm_apply_apply _
  refine ⟨?_, fun n u hu => heq n hu⟩
  apply (contDiffOn_iff_continuousOn_differentiableOn hS.uniqueDiffOn).mpr
  constructor
  · intro n hn
    have hA : ContinuousOn (A n) S := fun u hu => (hd n u hu).continuousAt.continuousWithinAt
    exact hA.congr (heq n)
  · intro n hn
    have hA : DifferentiableOn ℝ (A n) S := fun u hu => (hd n u hu).differentiableAt.differentiableWithinAt
    exact hA.congr (heq n)

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem functionsQ_chart_integral (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    ((functionsQ F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1 =
      ∫ x, twistedIntegrand F ζ hζ C s r
        (f.val (groupArchChart F ζ hζ z * g)) 1 x
        ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  exact twistedQ_formula F ζ hζ C s r
    (f.val (groupArchChart F ζ hζ z * g)) 1

theorem functionsQ_right_level (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
    (functionsQ F ζ hζ C s f).val (g * j.val) =
      (functionsQ F ζ hζ C s f).val g := by
  change twistedQ F ζ hζ C s (f.val (g * j.val)) = twistedQ F ζ hζ C s (f.val g)
  rw [hf.2 g j]

theorem functionsQ_chart_contDiff_of_local_extension (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ)
    (hlocal : ∀ z ∈ groupArchDomain F,
      ∃ U : Set (GroupArch F), IsOpen U ∧ z ∈ U ∧ U ⊆ groupArchDomain F ∧
        ∃ A : GroupArch F → KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C → ℂ,
          (∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun y => A y x)) ∧
          (∀ n : ℕ, Continuous
            (fun p : GroupArch F × KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C =>
              iteratedFDeriv ℝ n (fun y => A y p.2) p.1)) ∧
          ∀ y ∈ U, ∀ x, A y x = twistedIntegrand F ζ hζ C s r
            (f.val (groupArchChart F ζ hζ y * g)) 1 x) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((functionsQ F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro z hz
  obtain ⟨U, hU, hzU, _hUD, A, hA, hAj, hEq⟩ := hlocal z hz
  refine ⟨U, hU, hzU, ?_⟩
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ∫ x, A y x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
      Set.univ := by
    refine (integral_contDiffOn_of_locally_dominated_jets
      (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) A Set.univ isOpen_univ
      (fun x => (hA x).contDiffOn) ?_ ?_).1
    · intro n y _
      simpa only [iteratedFDerivWithin_univ, Function.comp_def, id_eq] using
        ((hAj n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
    · intro n y _
      obtain ⟨B, hB⟩ := ((isCompact_closedBall y 1).prod (isCompact_univ : IsCompact
        (Set.univ : Set (KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)))).exists_bound_of_continuousOn
          (hAj n).continuousOn
      refine ⟨Metric.closedBall y 1, (fun _ => B), Metric.closedBall_mem_nhds _ zero_lt_one,
        Set.subset_univ _, integrable_const B, Filter.Eventually.of_forall ?_⟩
      intro x v hv
      simpa only [iteratedFDerivWithin_univ] using hB (v, x) ⟨hv, Set.mem_univ x⟩
  apply (hsm.mono (Set.subset_univ _)).congr
  intro y hy
  rw [functionsQ_chart_integral F ζ hζ C s r f g y]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (hEq y hy.2 x).symm)

theorem functionsQ_preserves_level (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J) :
    functionsQ F ζ hζ C s f ∈
      InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J := by
  constructor
  · intro g
    let r := Classical.choice
      (KPGlobalTorusPeriodizationInverse.averaging_representatives_exist F ζ hζ C)
    apply functionsQ_chart_contDiff_of_local_extension F ζ hζ C s f r g
    intro z hz
    obtain ⟨U, hU, hzU, hUD, A, hA, hAj, hEq⟩ :=
      TorusChartTransport.weightedChart_local_extension F ζ hζ C s J f hf r g z hz
    refine ⟨U, hU, hzU, hUD, A, hA, hAj, ?_⟩
    intro y hy x
    rw [hEq y hy x, TorusChartTransport.weightedChartIntegrand_eq F ζ hζ C s r f g y]
  · exact functionsQ_right_level F ζ hζ C s J f hf

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
