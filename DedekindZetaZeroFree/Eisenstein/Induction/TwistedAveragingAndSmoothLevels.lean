module

public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingSmoothness
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalPeriodizationJetEstimates

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open scoped Topology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance functionsQLevelFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)
local instance functionsQLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

theorem functionsQ_level_continuous_of_isBounded (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hbound : Seminorm.IsBounded
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J i.1 i.2.1 i.2.2)
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J)) :
    @Continuous
      (InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J) := by
  letI := inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J
  letI := inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J
  have hp : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J i.1 i.2.1 i.2.2) :=
    ⟨rfl⟩
  have hq : WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2) :=
    ⟨rfl⟩
  exact WithSeminorms.continuous_of_isBounded hp hq _ hbound

theorem functionsQ_chart_integral_jets (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g : G F ζ hζ) (n : ℕ) (z : GroupArch F) (hz : z ∈ groupArchDomain F) :
    iteratedFDerivWithin ℝ n
      (fun y => ((functionsQ F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z =
    ∫ x, iteratedFDerivWithin ℝ n
      (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
      (groupArchDomain F) z
      ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C := by
  obtain ⟨U, hU, hzU, hUD, A, hA, hAj, hEq⟩ :=
    TorusChartTransport.weightedChart_local_extension F ζ hζ C s J f.val f.property r g z hz
  have hj := (integral_contDiffOn_of_locally_dominated_jets
    (KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) A Set.univ isOpen_univ
    (fun x => (hA x).contDiffOn) (by
      intro m y _
      simpa only [iteratedFDerivWithin_univ, Function.comp_def, id_eq] using
        ((hAj m).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace)
    (by
      intro m y _
      obtain ⟨B, hB⟩ := ((isCompact_closedBall y 1).prod (isCompact_univ : IsCompact
        (Set.univ : Set (KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)))).exists_bound_of_continuousOn
          (hAj m).continuousOn
      refine ⟨Metric.closedBall y 1, (fun _ => B), Metric.closedBall_mem_nhds _ zero_lt_one,
        Set.subset_univ _, integrable_const B, Filter.Eventually.of_forall ?_⟩
      intro x v hv
      simpa only [iteratedFDerivWithin_univ] using hB (v, x) ⟨hv, Set.mem_univ x⟩)).2 n z (Set.mem_univ z)
  have heq : (fun y => ((functionsQ F ζ hζ C s f.val).val
      (groupArchChart F ζ hζ y * g)).val.val 1) =ᶠ[nhds z]
      (fun y => ∫ x, A y x ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C) := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    change (twistedQ F ζ hζ C s (f.val.val (groupArchChart F ζ hζ y * g))).val.val 1 = _
    rw [← TorusChartTransport.weightedChart_integral_eq F ζ hζ C s r f.val g y]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (hEq y hy x).symm))
  have hset : groupArchDomain F =ᶠ[nhds z] (Set.univ : Set (GroupArch F)) :=
    Filter.eventually_of_mem ((groupArchDomain_open F).mem_nhds hz)
      (fun y hy => by simp [hy])
  rw [iteratedFDerivWithin_congr_set (𝕜 := ℝ)
    (f := fun y => ((functionsQ F ζ hζ C s f.val).val
      (groupArchChart F ζ hζ y * g)).val.val 1) hset n]
  refine ((heq.filter_mono (nhdsWithin_le_nhds (s := Set.univ))).iteratedFDerivWithin_eq
    (𝕜 := ℝ) heq.eq_of_nhds n).trans (hj.trans ?_)
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hex : (fun y => A y x) =ᶠ[nhds z]
      (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x) :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) (fun y hy => hEq y hy x)
  change iteratedFDerivWithin ℝ n (fun y => A y x) Set.univ z = _
  exact ((hex.filter_mono (nhdsWithin_le_nhds (s := Set.univ))).iteratedFDerivWithin_eq
    (𝕜 := ℝ) hex.eq_of_nhds n).trans
    (iteratedFDerivWithin_congr_set (𝕜 := ℝ)
      (f := fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
      hset.symm n)

theorem functionsQ_jet_le_of_integral_jets (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (B : ℝ) (hB : 0 ≤ B)
    (hjets : ∀ z ∈ K.set,
      iteratedFDerivWithin ℝ n
        (fun y => ((functionsQ F ζ hζ C s f.val).val
          (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z =
      ∫ x, iteratedFDerivWithin ℝ n
        (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
        (groupArchDomain F) z
        ∂KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
    (hbound : ∀ z ∈ K.set, ∀ x,
      ‖iteratedFDerivWithin ℝ n
        (fun y => TorusChartTransport.weightedChartIntegrand F ζ hζ C s r f.val g y x)
        (groupArchDomain F) z‖ ≤ B) :
    inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J g n K
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J f) ≤ B := by
  change inducedJetBound F ζ hζ _ J g n K _ ≤ B
  unfold inducedJetBound
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro _ ⟨z, hz, rfl⟩
    change ‖iteratedFDerivWithin ℝ n
      (fun y => ((functionsQ F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z‖ ≤ B
    rw [hjets z hz]
    simpa using norm_integral_le_of_norm_le_const
      (μ := KPGlobalTorusPeriodizationInverse.probabilityHaar F ζ hζ C)
      (Filter.Eventually.of_forall (hbound z hz))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simpa only [hE, Set.image_empty, Real.sSup_empty] using hB

theorem functionsQ_level_continuous (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous
      (InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (levelMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
        (functionsQ_preserves_level F ζ hζ C s) J) := by
  apply functionsQ_level_continuous_of_isBounded F ζ hζ C s J
  apply Seminorm.IsBounded.of_real
  intro i
  let r := Classical.choice
    (KPGlobalTorusPeriodizationInverse.averaging_representatives_exist F ζ hζ C)
  let h := TorusChartTransport.weightedChart_source_jet_bound F ζ hζ C s J r i.1 i.2.1 i.2.2
  let S := h.choose
  let B := h.choose_spec.choose
  have hB : 0 ≤ B := h.choose_spec.choose_spec.1
  have hb := h.choose_spec.choose_spec.2
  refine ⟨S, B, fun f => ?_⟩
  apply functionsQ_jet_le_of_integral_jets F ζ hζ C s J r i.1 i.2.1 i.2.2 f
  · exact mul_nonneg hB (apply_nonneg _ _)
  · intro z hz
    exact functionsQ_chart_integral_jets F ζ hζ C s J r f i.1 i.2.1 z (i.2.2.inside hz)
  · exact hb f

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
open KPGlobalTorusBorelTwistCompatibilityBorelInduction
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology3 (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

local instance inducedTop3 (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  inducedTopology F ζ hζ P

def borelFunctionsMap (P Q : Polarization F ζ hζ)
    (L : Smooth F ζ hζ P →ₗ[ℂ] Smooth F ζ hζ Q)
    (hL : ∀ (a : E F ζ hζ) (v : Smooth F ζ hζ P),
      L (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P a v) =
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ Q a (L v)) :
    InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q where
  toFun f := ⟨fun g => L (f.val g), by
    intro t x g
    change L (f.val ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)) = _
    rw [f.property t x g, map_smul, hL]⟩
  map_add' := by
    intro f k
    apply Subtype.ext
    funext g
    exact L.map_add _ _
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext g
    exact L.map_smul _ _
def borelFunctionsP (C : ModelData F ζ hζ) (s : ℂ) :=
  borelFunctionsMap F ζ hζ _ _ (twistedP F ζ hζ C s).toLinearMap
    (twistedP_intertwines F ζ hζ C s)
def borelFunctionsQ (C : ModelData F ζ hζ) (s : ℂ) :=
  borelFunctionsMap F ζ hζ _ _ (twistedQ F ζ hζ C s).toLinearMap
    (twistedQ_intertwines F ζ hζ C s)

def inducedMapOfLevels (P Q : Polarization F ζ hζ)
    (L : InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q)
    (hL : ∀ J, ∀ f ∈ InducedLevel F ζ hζ P J,
      L f ∈ InducedLevel F ζ hζ Q J) :
    Induced F ζ hζ P →ₗ[ℂ] Induced F ζ hζ Q :=
  L.restrict (by
    have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ Q).comap L := by
      apply iSup_le
      intro J f hf
      exact Submodule.mem_iSup_of_mem J (hL J f hf)
    exact fun f hf => hle hf)

local instance inducedFunctionsAddGroup3 (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)
local instance inducedLevelAddGroup3 (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)
local instance inducedAddGroup3 (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

theorem inducedStageContinuous (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous _ _ (inducedLevelTopology F ζ hζ P J) (inducedTopology F ζ hζ P)
      (inducedStageInclusion F ζ hζ P J) := by
  letI := inducedLevelTopology F ζ hζ P J
  have hp : WithSeminorms (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  apply Seminorm.continuous_of_continuous_comp
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq
    (inducedStageInclusion F ζ hζ P J)
  intro q
  exact q.property J

theorem inducedMapOfLevels_continuous (P Q : Polarization F ζ hζ)
    (L : InducedFunctions F ζ hζ P →ₗ[ℂ] InducedFunctions F ζ hζ Q)
    (hL : ∀ J, ∀ f ∈ InducedLevel F ζ hζ P J,
      L f ∈ InducedLevel F ζ hζ Q J)
    (hc : ∀ J, @Continuous _ _
      (inducedLevelTopology F ζ hζ P J) (inducedLevelTopology F ζ hζ Q J)
      (L.restrict (hL J))) :
    Continuous (inducedMapOfLevels F ζ hζ P Q L hL) := by
  have hp : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  have hq : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ Q => q.val) := ⟨rfl⟩
  let m := inducedMapOfLevels F ζ hζ P Q L hL
  apply Seminorm.continuous_of_continuous_comp
    (𝕝 := ℂ) (𝕝₂ := ℂ) (τ₁₂ := RingHom.id ℂ) hq m
  intro q
  let r : Seminorm ℂ (Induced F ζ hζ P) := q.val.comp m
  have hr : ∀ J, @Continuous _ _ (inducedLevelTopology F ζ hζ P J) inferInstance
      (r ∘ inducedStageInclusion F ζ hζ P J) := by
    intro J
    letI := inducedLevelTopology F ζ hζ P J
    letI := inducedLevelTopology F ζ hζ Q J
    have he : r ∘ inducedStageInclusion F ζ hζ P J =
        q.val ∘ inducedStageInclusion F ζ hζ Q J ∘ L.restrict (hL J) := by
      rfl
    rw [he]
    exact (q.property J).comp (hc J)
  exact hp.continuous_seminorm ⟨r, hr⟩

theorem induced_continuous_of_stages (P Q : Polarization F ζ hζ)
    (A : Induced F ζ hζ P →ₗ[ℂ] Induced F ζ hζ Q)
    (hA : ∀ J, @Continuous _ _ (inducedLevelTopology F ζ hζ P J)
      (inducedTopology F ζ hζ Q) (A ∘ inducedStageInclusion F ζ hζ P J)) :
    Continuous A := by
  have hp : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ P => q.val) := ⟨rfl⟩
  have hq : WithSeminorms (fun q : inducedFinalSeminorms F ζ hζ Q => q.val) := ⟨rfl⟩
  letI := hp.isTopologicalAddGroup
  apply hq.continuous_of_continuous_comp
  intro q
  let p : inducedFinalSeminorms F ζ hζ P := ⟨q.val.comp A, by
    intro J
    letI := inducedLevelTopology F ζ hζ P J
    exact (hq.continuous_seminorm q).comp (hA J)⟩
  exact hp.continuous_seminorm p

theorem borelFunctionsP_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (g : G F ζ hζ) :
    (borelFunctionsP F ζ hζ C s f).val g = twistedP F ζ hζ C s (f.val g) := rfl

theorem borelFunctionsQ_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) :
    (borelFunctionsQ F ζ hζ C s f).val g = twistedQ F ζ hζ C s (f.val g) := rfl

theorem borelFunctionsP_borelFunctionsQ (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelFunctionsP F ζ hζ C s (borelFunctionsQ F ζ hζ C s f) = f := by
  apply Subtype.ext
  funext g
  exact twistedP_twistedQ F ζ hζ C s (f.val g)

theorem borelFunctionsQ_borelFunctionsP (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelFunctionsQ F ζ hζ C s (borelFunctionsP F ζ hζ C s f) = f := by
  apply Subtype.ext
  funext g
  exact twistedQ_twistedP F ζ hζ C s (f.val g)

def borelP (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) :=
  ⟨unionMap F ζ hζ _ _ (functionsP F ζ hζ C s)
      (functionsP_preserves_level F ζ hζ C s),
    unionMap_continuous F ζ hζ _ _ (functionsP F ζ hζ C s)
      (functionsP_preserves_level F ζ hζ C s)
      (functionsP_level_continuous F ζ hζ C s)⟩

def borelQ (C : ModelData F ζ hζ) (s : ℂ) :
    Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) →L[ℂ]
      Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) :=
  ⟨unionMap F ζ hζ _ _ (functionsQ F ζ hζ C s)
      (functionsQ_preserves_level F ζ hζ C s),
    unionMap_continuous F ζ hζ _ _ (functionsQ F ζ hζ C s)
      (functionsQ_preserves_level F ζ hζ C s)
      (functionsQ_level_continuous F ζ hζ C s)⟩

 theorem borelP_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) (g : G F ζ hζ) :
    (borelP F ζ hζ C s f).val.val g = twistedP F ζ hζ C s (f.val.val g) := by rfl

 theorem borelQ_fiberwise (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) (g : G F ζ hζ) :
    (borelQ F ζ hζ C s f).val.val g = twistedQ F ζ hζ C s (f.val.val g) := by rfl

 theorem borelP_borelQ (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelP F ζ hζ C s (borelQ F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelP_fiberwise, borelQ_fiberwise, twistedP_twistedQ]

 theorem borelQ_borelP (C : ModelData F ζ hζ) (s : ℂ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelQ F ζ hζ C s (borelP F ζ hζ C s f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [borelQ_fiberwise, borelP_fiberwise, twistedQ_twistedP]

 theorem finitePart_normal : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
  unfold KPGlobalTorusFunctionData.finitePart
  apply Subgroup.Normal.map (Subgroup.normal_iInf_normal fun w => inferInstance)
  change Function.Surjective (fun x => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x))
  exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

 def finiteConj (a : G F ζ hζ) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨(MulAut.conjNormal a).toEquiv, ?_, ?_⟩
  · apply Continuous.subtype_mk
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => a * x.val * a⁻¹)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · apply Continuous.subtype_mk
    have he : (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a).symm = MulAut.conjNormal a⁻¹ := by
      change (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart F ζ hζ) a)⁻¹ = _
      rw [map_inv]
    change Continuous (fun x : KPGlobalTorusFunctionData.finitePart F ζ hζ => ((MulAut.conjNormal a).symm x).val)
    rw [he]
    simp only [MulAut.conjNormal_apply, inv_inv]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

 def conjLevel (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ := by
  letI := finitePart_normal F ζ hζ
  exact ⟨J.toOpenSubgroup.comap (MulAut.conjNormal a⁻¹).toMonoidHom (by
      change Continuous (finiteConj F ζ hζ a⁻¹)
      exact (finiteConj F ζ hζ a⁻¹).continuous),
    (finiteConj F ζ hζ a⁻¹).isCompact_preimage.mpr J.isCompact⟩

 def inducedFunctionsTranslation (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (InducedFunctions F ζ hζ P) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro t x g
        simpa only [mul_assoc] using f.property t x (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

private theorem induced_translate_level (P : Polarization F ζ hζ)
    (a : G F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ InducedLevel F ζ hζ P J) :
    inducedFunctionsTranslation F ζ hζ P a f ∈
      InducedLevel F ζ hζ P (conjLevel F ζ hζ a J) := by
  constructor
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val ((groupArchChart F ζ hζ z * g) * a)).val.val 1) _
    simpa only [mul_assoc] using hf.1 (g * a)
  · intro g j
    have hj : a⁻¹ * j.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
      obtain ⟨k, hk, he⟩ := j.property
      have hk' : a⁻¹ * k.val * a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
        letI := finitePart_normal F ζ hζ
        apply Subgroup.mem_map.mpr
        exact ⟨MulAut.conjNormal a⁻¹ k, hk, by simp only [Subgroup.subtype_apply, MulAut.conjNormal_apply, inv_inv]⟩
      change k.val = j.val at he
      rw [← he]
      exact hk'
    have hh := hf.2 (g * a) ⟨a⁻¹ * j.val * a, hj⟩
    change f.val ((g * j.val) * a) = f.val (g * a)
    have he : (g * a) * (a⁻¹ * j.val * a) = (g * j.val) * a := by group
    change f.val ((g * a) * (a⁻¹ * j.val * a)) = f.val (g * a) at hh
    rwa [he] at hh

 theorem induced_translate_union (P : Polarization F ζ hζ) (a : G F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (hf : f ∈ Induced F ζ hζ P) :
    inducedFunctionsTranslation F ζ hζ P a f ∈ Induced F ζ hζ P := by
  have hle : Induced F ζ hζ P ≤ (Induced F ζ hζ P).comap
      (inducedFunctionsTranslation F ζ hζ P a) := by
    apply iSup_le
    intro J x hx
    exact Submodule.mem_iSup_of_mem (conjLevel F ζ hζ a J)
      (induced_translate_level F ζ hζ P a J x hx)
  exact hle hf

def inducedRightAction (P : Polarization F ζ hζ) :
    Representation ℂ (G F ζ hζ) (Induced F ζ hζ P) where
  toFun a := (inducedFunctionsTranslation F ζ hζ P a).restrict
    (induced_translate_union F ζ hζ P a)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * 1) = f.val.val g
    exact congrArg f.val.val (mul_one g)
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change f.val.val (g * (a * b)) = f.val.val ((g * a) * b)
    exact congrArg f.val.val (mul_assoc g a b).symm

 theorem inducedRightAction_formula (P : Polarization F ζ hζ)
    (a g : G F ζ hζ) (f : Induced F ζ hζ P) :
    (inducedRightAction F ζ hζ P a f).val.val g = f.val.val (g * a) := by rfl

 theorem borelP_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s)) :
    borelP F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a
        (borelP F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  calc
    _ = twistedP F ζ hζ C s
        ((inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a f).val.val g) :=
      borelP_fiberwise F ζ hζ C s _ g
    _ = twistedP F ζ hζ C s (f.val.val (g * a)) :=
      congrArg (twistedP F ζ hζ C s)
        (inducedRightAction_formula F ζ hζ _ a g f)
    _ = (borelP F ζ hζ C s f).val.val (g * a) :=
      (borelP_fiberwise F ζ hζ C s f (g * a)).symm
    _ = _ := (inducedRightAction_formula F ζ hζ _ a g _).symm

 theorem borelQ_intertwines (C : ModelData F ζ hζ) (s : ℂ) (a : G F ζ hζ)
    (f : Induced F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)) :
    borelQ F ζ hζ C s
        (inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a f) =
      inducedRightAction F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) a
        (borelQ F ζ hζ C s f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  calc
    _ = twistedQ F ζ hζ C s
        ((inducedRightAction F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) a f).val.val g) :=
      borelQ_fiberwise F ζ hζ C s _ g
    _ = twistedQ F ζ hζ C s (f.val.val (g * a)) :=
      congrArg (twistedQ F ζ hζ C s)
        (inducedRightAction_formula F ζ hζ _ a g f)
    _ = (borelQ F ζ hζ C s f).val.val (g * a) :=
      (borelQ_fiberwise F ζ hζ C s f (g * a)).symm
    _ = _ := (inducedRightAction_formula F ζ hζ _ a g _).symm

def scalarSection (P : Polarization F ζ hζ) :
    Induced F ζ hζ P →ₗ[ℂ] KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P where
  toFun f := ⟨fun g => (f.val.val g).val.val 1, by
    intro h x g
    have hc := f.val.property h.val x g
    have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hc
    have ht : (f.val.val g).val.val h.val =
        (P.character h : ℂ) * (f.val.val g).val.val 1 := by
      have hp := (f.val.val g).val.property h 1
      change (f.val.val g).val.val (h.val * 1) =
        (P.character h : ℂ) * (f.val.val g).val.val 1 at hp
      simpa only [mul_one] using hp
    simpa only [KPGlobalTorusPeriodizationInverse.rightAction_formula,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one_mul,
      ht, mul_assoc] using he⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

 theorem scalarSection_formula (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) :
    (scalarSection F ζ hζ P f).val g = (f.val.val g).val.val 1 := by rfl

 theorem scalar_transitivity (P : Polarization F ζ hζ)
    (f : Induced F ζ hζ P) (g : G F ζ hζ) (t : E F ζ hζ) :
    (f.val.val g).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (scalarSection F ζ hζ P f).val (t.val * g) := by
  have hc := f.val.property t 0 g
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hc
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (NNReal.coe_pos.2 (pos_iff_ne_zero.2 (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))))))
  rw [scalarSection_formula]
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 := by
    exact (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simp only [hn, mul_one, KPGlobalTorusPeriodizationInverse.rightAction_formula,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one_mul] at he
  calc
    _ = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t * (f.val.val g).val.val t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = _ := congrArg (fun z : ℂ => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * z) he.symm

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport

end
