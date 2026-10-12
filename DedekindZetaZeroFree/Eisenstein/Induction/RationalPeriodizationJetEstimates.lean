module

public import DedekindZetaZeroFree.Metaplectic.Torus.Charts.TwistedPeriodization

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem contDiffOn_tsum_of_chart_locally_finite
    (C : ModelData F ζ hζ)
    (φ : GroupArch F → ℂ)
    (T : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C → GroupArch F → ℂ)
    (hφ : ∀ z, φ z = ∑' a, T a z)
    (hsmooth : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (T a) (groupArchDomain F))
    (hfin : ∀ K : Set (GroupArch F), IsCompact K → K ⊆ groupArchDomain F →
      ∃ S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C),
        ∀ z ∈ K, ∀ a ∉ S, T a z = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) φ (groupArchDomain F) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (groupArchDomain_open F) x hx
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  refine ⟨interior (Metric.closedBall x (r / 2)), isOpen_interior, ?_, ?_⟩
  · exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr2)
  · obtain ⟨S, hS⟩ := hfin (Metric.closedBall x (r / 2)) (isCompact_closedBall x (r / 2))
      ((Metric.closedBall_subset_ball (by linarith)).trans hrsub)
    have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z => ∑ a ∈ S, T a z) (groupArchDomain F) :=
      ContDiffOn.sum (fun a _ => hsmooth a)
    refine (hsum.mono Set.inter_subset_left).congr ?_
    intro z hz
    have hzK : z ∈ Metric.closedBall x (r / 2) := interior_subset hz.2
    rw [hφ z, tsum_eq_sum (fun a ha => hS z hzK a ha)]

theorem functionsP_chart_contDiff (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((functionsP F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1)
      (groupArchDomain F) := by
  refine contDiffOn_tsum_of_chart_locally_finite F ζ hζ C
    (fun z => ((functionsP F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1)
    (TorusChartTransport.chartTerm F ζ hζ C s f g)
    (fun z => TorusChartTransport.functionsP_chart_tsum F ζ hζ C s f g z)
    (fun a => TorusChartTransport.chartTerm_contDiffOn F ζ hζ C s J f hf g a)
    (fun K hK hKU => TorusChartTransport.chartTerm_eventually_zero F ζ hζ C s J f hf g K hK hKU)

theorem functionsP_preserves_level (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J) :
    functionsP F ζ hζ C s f ∈
      InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J := by
  constructor
  · intro g
    exact functionsP_chart_contDiff F ζ hζ C s J f hf g
  · intro g j
    change twistedP F ζ hζ C s (f.val (g * j.val)) = twistedP F ζ hζ C s (f.val g)
    rw [hf.2 g j]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.Continuity
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

theorem inducedLevelTopology_withSeminorms (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    letI := inducedLevelTopology F ζ hζ P J
    WithSeminorms (fun i : G F ζ hζ × ℕ ×
      KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2) := by
  exact WithSeminorms.mk (topology := inducedLevelTopology F ζ hζ P J) rfl

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.Continuity

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.Continuity
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance criterionFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance criterionLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

theorem continuous_of_inducedJet_isBounded
    (P Q : Polarization F ζ hζ)
    (J J' : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (T : InducedLevel F ζ hζ P J →ₗ[ℂ] InducedLevel F ζ hζ Q J')
    (hp : letI := inducedLevelTopology F ζ hζ P J
      WithSeminorms (fun i : G F ζ hζ × ℕ ×
        KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ P J i.1 i.2.1 i.2.2))
    (hq : letI := inducedLevelTopology F ζ hζ Q J'
      WithSeminorms (fun i : G F ζ hζ × ℕ ×
        KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ Q J' i.1 i.2.1 i.2.2))
    (hT : Seminorm.IsBounded
      (fun i : G F ζ hζ × ℕ ×
        KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)
      (fun i : G F ζ hζ × ℕ ×
        KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ Q J' i.1 i.2.1 i.2.2) T) :
    @Continuous (InducedLevel F ζ hζ P J) (InducedLevel F ζ hζ Q J')
      (inducedLevelTopology F ζ hζ P J) (inducedLevelTopology F ζ hζ Q J') T := by
  letI := inducedLevelTopology F ζ hζ P J
  letI := inducedLevelTopology F ζ hζ Q J'
  exact WithSeminorms.continuous_of_isBounded hp hq T hT

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.Continuity

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalArchUnits (y : Fˣ) (w : InfinitePlace F) : ℂˣ :=
  Units.map ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      (algebraMap F (KPHilbert.Completion F (Sum.inl w)))) y

theorem rationalLift_split (y : Fˣ) :
    ∃ b : G F ζ hζ, b ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ ∧
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y).val.val =
        KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * b := by
  let r := KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F y 1)
  let a := KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ
    (fun w => (rationalArchUnits F ζ hζ y w : ℂ))
  let q := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
  refine ⟨q (a⁻¹ * r), ?_, ?_⟩
  · refine ⟨a⁻¹ * r, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change (a (Sum.inl w))⁻¹ * r (Sum.inl w) = 1
    have he : a (Sum.inl w) = r (Sum.inl w) := by
      change KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ _ (Sum.inl w) =
        KPAdelicCoverRestrictedProduct.rationalCoordinates F ζ hζ _ (Sum.inl w)
      rw [KPAdelicCoverRestrictedProduct.rationalCoordinates_A]
      change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : (rationalArchUnits F ζ hζ y w : ℂ) = 0 then 1 else
          Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm (rationalArchUnits F ζ hζ y w)) _) = _
      simp only [Units.ne_zero, ↓reduceDIte]
      congr 1
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w))
              (algebraMap F (KPHilbert.Completion F (Sum.inl w)) y.val)) = _
      exact RingEquiv.symm_apply_apply _ _
    change (a (Sum.inl w))⁻¹ * r (Sum.inl w) = 1
    rw [he, inv_mul_cancel]
  · change q r = q a * q (a⁻¹ * r)
    simp

theorem chartTerm_transport (C : ModelData F ζ hζ) (s : ℂ)
    (g : G F ζ hζ) (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    ∃ (u : InfinitePlace F → ℂˣ) (b : G F ζ hζ),
      ∀ (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
        (z : GroupArch F), z ∈ groupArchDomain F →
        TorusChartTransport.chartTerm F ζ hζ C s f g a z =
          (f.val (groupArchChart F ζ hζ (TorusChartTransport.groupArchDiagonalTransport F u z) * b)).val.val 1 := by
  obtain ⟨y, hy⟩ := TorusChartTransport.rationalRep_rational F ζ hζ C a
  obtain ⟨b, hb, he⟩ := rationalLift_split F ζ hζ y
  refine ⟨rationalArchUnits F ζ hζ y, b * g, ?_⟩
  intro f z hz
  unfold TorusChartTransport.chartTerm
  rw [TorusChartTransport.inducedFunctions_fiber_eval, hy]
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y).val = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf,
      KPGlobalTorusPeriodizationInverse.rationalLift, delta_rational]
  rw [hhalf, inv_one, one_mul, he]
  have hc := (TorusChartTransport.groupArchChart_commutes_finite F ζ hζ b hb z).eq
  have hm : (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * b) *
        (groupArchChart F ζ hζ z * g) =
      (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * groupArchChart F ζ hζ z) * (b * g) := by
    rw [mul_assoc, ← mul_assoc b, ← hc]
    group
  rw [hm, TorusChartTransport.groupArchDiagonalTransport_absorption F ζ hζ _ z hz]

theorem chartTerm_contDiffOn_from_transport (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
    (g : G F ζ hζ) (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    ContDiffOn ℝ (⊤ : ℕ∞) (TorusChartTransport.chartTerm F ζ hζ C s f.val g a)
      (groupArchDomain F) := by
  obtain ⟨u, b, he⟩ := chartTerm_transport F ζ hζ C s g a
  have hc := (f.property.1 b).comp
    (TorusChartTransport.groupArchDiagonalTransport_contDiff F u).contDiffOn
    (fun z hz => (TorusChartTransport.groupArchDiagonalTransport_domain F u z).2 hz)
  exact hc.congr (fun z hz => he f.val z hz)

theorem chartTerm_jet_bound (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    ∃ (b : G F ζ hζ) (L : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
      (B : ℝ), 0 ≤ B ∧
      ∀ (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
        (z : GroupArch F), z ∈ K.set →
        ‖iteratedFDerivWithin ℝ n (TorusChartTransport.chartTerm F ζ hζ C s f.val g a)
          (groupArchDomain F) z‖ ≤
          B * inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J b n L f := by
  obtain ⟨u, b, he⟩ := chartTerm_transport F ζ hζ C s g a
  refine ⟨b, TorusChartTransport.groupArchDiagonalTransport_compact F u K,
    ‖TorusChartTransport.groupArchDiagonalTransportCLM F u‖ ^ n,
    pow_nonneg (norm_nonneg _) n, ?_⟩
  intro f z hz
  have he' : (TorusChartTransport.chartTerm F ζ hζ C s f.val g a) =ᶠ[nhdsWithin z (groupArchDomain F)]
      (fun y => (f.val.val (groupArchChart F ζ hζ
        (TorusChartTransport.groupArchDiagonalTransport F u y) * b)).val.val 1) :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => he f.val y hy)
  rw [he'.iteratedFDerivWithin_eq (he f.val z (K.inside hz)) n]
  exact TorusChartTransport.groupArchDiagonalTransport_jet_bound F ζ hζ u _ J b n K f z hz

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance functionsPLevelFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) :=
  @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance functionsPLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) :=
  @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
    inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

theorem functionsP_jet_le_of_finite_chart_terms (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
    (S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C))
    (B : ℝ) (hB : 0 ≤ B)
    (hfin : ∀ z ∈ K.set, ∀ᶠ y in nhdsWithin z (groupArchDomain F),
      ∀ a ∉ S, TorusChartTransport.chartTerm F ζ hζ C s f.val g a y = 0)
    (hsmooth : ∀ z ∈ K.set, ∀ a ∈ S, ContDiffWithinAt ℝ n
      (TorusChartTransport.chartTerm F ζ hζ C s f.val g a) (groupArchDomain F) z)
    (hbound : ∀ z ∈ K.set, ∀ a ∈ S,
      ‖iteratedFDerivWithin ℝ n (TorusChartTransport.chartTerm F ζ hζ C s f.val g a)
        (groupArchDomain F) z‖ ≤ B) :
    inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J g n K
      (levelMap F ζ hζ _ _ (functionsP F ζ hζ C s)
        (functionsP_preserves_level F ζ hζ C s) J f) ≤ (S.card : ℝ) * B := by
  change inducedJetBound F ζ hζ _ J g n K _ ≤ _
  unfold inducedJetBound
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro r ⟨z, hz, rfl⟩
    have hzU := K.inside hz
    have heq : (fun y => ((functionsP F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) =ᶠ[nhdsWithin z (groupArchDomain F)]
        (fun y => ∑ a ∈ S, TorusChartTransport.chartTerm F ζ hζ C s f.val g a y) := by
      filter_upwards [hfin z hz] with y hy
      rw [TorusChartTransport.functionsP_chart_tsum F ζ hζ C s f.val g y]
      exact tsum_eq_sum hy
    have heqz := heq.eq_of_nhdsWithin hzU
    change ‖iteratedFDerivWithin ℝ n
      (fun y => ((functionsP F ζ hζ C s f.val).val
        (groupArchChart F ζ hζ y * g)).val.val 1) (groupArchDomain F) z‖ ≤ _
    rw [heq.iteratedFDerivWithin_eq heqz n,
      iteratedFDerivWithin_fun_sum_apply (groupArchDomain_open F).uniqueDiffOn hzU
        (hsmooth z hz)]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (hbound z hz)).trans_eq
      (by simp))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp only [hE, Set.image_empty, Real.sSup_empty]
    positivity

theorem functionsP_level_isBounded (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Seminorm.IsBounded
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2)
      (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
        inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J i.1 i.2.1 i.2.2)
      (levelMap F ζ hζ _ _ (functionsP F ζ hζ C s)
        (functionsP_preserves_level F ζ hζ C s) J) := by
  apply Seminorm.IsBounded.of_real
  rintro ⟨g, n, K⟩
  change ∃ (A : Finset (G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)))
    (B : ℝ), ∀ f : InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J,
      inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J g n K
        (levelMap F ζ hζ _ _ (functionsP F ζ hζ C s)
          (functionsP_preserves_level F ζ hζ C s) J f) ≤
      B * (A.sup (fun i => inducedJet F ζ hζ
        (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2)) f
  obtain ⟨S, hS⟩ := UniformFiberLevel.exists_uniform_chart_support F ζ hζ C s J g
  choose b L B hB hb using (UniformFiberLevel.chartTerm_jet_bound F ζ hζ C s J g n K)
  let A := S.image (fun a => (b a, n, L a))
  let p := fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
    inducedJet F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J i.1 i.2.1 i.2.2
  let D := ∑ a ∈ S, B a
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hB a)
  refine ⟨A, (S.card : ℝ) * D, ?_⟩
  intro f
  have hjet (a) (ha : a ∈ S) (z) (hz : z ∈ K.set) :
      ‖iteratedFDerivWithin ℝ n (TorusChartTransport.chartTerm F ζ hζ C s f.val g a)
        (groupArchDomain F) z‖ ≤ D * (A.sup p) f := by
    have hBa : B a ≤ D := Finset.single_le_sum (fun a _ => hB a) ha
    have hp : p (b a, n, L a) f ≤ (A.sup p) f :=
      Finset.le_sup (s := A) (f := p) (Finset.mem_image.mpr ⟨a, ha, rfl⟩) f
    exact (hb a f z hz).trans (mul_le_mul hBa hp (apply_nonneg _ _) hD)
  have ht := functionsP_jet_le_of_finite_chart_terms F ζ hζ C s J g n K f S
    (D * (A.sup p) f) (mul_nonneg hD (apply_nonneg _ _))
    (fun z _ => Filter.Eventually.of_forall (fun y a ha => hS f y a ha))
    (fun z hz a _ => (UniformFiberLevel.chartTerm_contDiffOn_from_transport F ζ hζ C s J
      f g a z (K.inside hz)).of_le (by simp))
    (fun z hz a ha => hjet a ha z hz)
  exact ht.trans_eq (by ring)

theorem functionsP_level_continuous (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    @Continuous
      (InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
      (inducedLevelTopology F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
      (levelMap F ζ hζ _ _ (functionsP F ζ hζ C s)
        (functionsP_preserves_level F ζ hζ C s) J) := by
  exact Continuity.continuous_of_inducedJet_isBounded F ζ hζ _ _ J J _
    (Continuity.inducedLevelTopology_withSeminorms F ζ hζ _ J)
    (Continuity.inducedLevelTopology_withSeminorms F ζ hζ _ J)
    (functionsP_level_isBounded F ζ hζ C s J)

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction

end
