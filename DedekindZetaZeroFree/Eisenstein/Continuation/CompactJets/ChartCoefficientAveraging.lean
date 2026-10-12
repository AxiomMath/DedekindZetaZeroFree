module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.CubicRootChartGeometry

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

section CompactZeroExtension
variable {X Y G : Type*} [TopologicalSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [Group G] [Fintype G] [MulAction G X]
variable (Q : X → Y) (hQ : Continuous Q)
  (horbit : ∀ x y, Q x = Q y ↔ ∃ g : G, g • x = y)
  (hact : ∀ g : G, Continuous (fun x : X => g • x))
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

 def globalAvg (f : ContinuousMap X ℂ) (y : Y) : ℂ :=
  if hy : y ∈ Set.range Q then
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,hy⟩)
  else 0

include hQ horbit hact in
private lemma globalAvg_meas (f : ContinuousMap X ℂ) : Measurable (globalAvg (G := G) Q f) := by
  have hc : IsCompact (Set.range Q) := by simpa using isCompact_univ.image hQ
  have hd : Measurable (fun y : Set.range Q =>
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) y)) := by

    have hm : Measurable (fun x : X => (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • x)) :=
      measurable_const.mul (Finset.measurable_sum _ (fun g _ => (f.continuous.comp (hact g)).measurable))
    apply ((hQ.subtype_mk _).measurable.measurable_comp_iff_of_surjective
      (Set.rangeFactorization_surjective (f := Q))).mp
    convert hm using 1
    funext x
    obtain ⟨g,hg⟩ := (horbit x (Function.surjInv (Set.rangeFactorization_surjective (f := Q))
      (Set.rangeFactorization Q x))).mp (congrArg Subtype.val
        (Function.surjInv_eq (Set.rangeFactorization_surjective (f := Q)) (Set.rangeFactorization Q x))).symm
    change (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • Function.surjInv
      (Set.rangeFactorization_surjective (f := Q)) (Set.rangeFactorization Q x)) = _
    rw [← hg]
    simp_rw [← mul_smul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => rfl)
  exact hd.dite measurable_const hc.isClosed.measurableSet

private lemma globalAvg_bound (f : ContinuousMap X ℂ) (y : Y) :
    ‖globalAvg (G := G) Q f y‖ ≤ ‖f‖ * ‖((Set.range Q).indicator (fun _ : Y => (1 : ℂ))) y‖ := by
  by_cases hy : y ∈ Set.range Q
  · simp only [globalAvg, dite_eq_left hy, Set.indicator_of_mem hy, norm_one, mul_one]
    have hn : (Fintype.card G : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
    calc
      _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g : G, f (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,hy⟩)‖ := by simp
      _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,hy⟩)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
      _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
        exact Finset.sum_le_sum (fun g _ => ContinuousMap.norm_coe_le_norm f _)
      _ = ‖f‖ := by simp [ne_of_gt hn]
  · simp [globalAvg, hy]

include hQ in
 lemma indicator_mem : MemLp ((Set.range Q).indicator (fun _ : Y => (1 : ℂ))) 2 μ := by
  have hc : IsCompact (Set.range Q) := by simpa using isCompact_univ.image hQ
  exact memLp_indicator_const 2 hc.isClosed.measurableSet.nullMeasurableSet 1 (Or.inr hc.measure_lt_top.ne)

include hQ horbit hact in
 lemma globalAvg_memLp (f : ContinuousMap X ℂ) : MemLp (globalAvg (G := G) Q f) 2 μ := by
  exact (indicator_mem Q hQ μ).of_le_mul
    (globalAvg_meas Q hQ horbit hact f).aestronglyMeasurable
    (Filter.Eventually.of_forall (globalAvg_bound Q f))

 def globalAvgLinear : ContinuousMap X ℂ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (globalAvg_memLp Q hQ horbit hact μ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ (f+g)),
      MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ f),
      MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ g),
      Lp.coeFn_add ((globalAvg_memLp Q hQ horbit hact μ f).toLp _) ((globalAvg_memLp Q hQ horbit hact μ g).toLp _)] with y hfg hf hg hadd
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hfg, hf, hg]
    by_cases hy : y ∈ Set.range Q <;> simp [globalAvg, hy, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ (c • f)),
      MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ f),
      Lp.coeFn_smul c ((globalAvg_memLp Q hQ horbit hact μ f).toLp _)] with y hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hcf, hf]
    by_cases hy : y ∈ Set.range Q <;> simp [globalAvg, hy, smul_eq_mul, ← Finset.mul_sum, mul_left_comm]

 lemma globalAvgLinear_bound (f : ContinuousMap X ℂ) :
    ‖globalAvgLinear Q hQ horbit hact μ f‖ ≤ ‖(indicator_mem Q hQ μ).toLp _‖ * ‖f‖ := by
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (globalAvg_memLp Q hQ horbit hact μ f).aestronglyMeasurable
    (Filter.Eventually.of_forall (globalAvg_bound Q f)) 2
  change ‖(globalAvg_memLp Q hQ horbit hact μ f).toLp _‖ ≤ ‖(indicator_mem Q hQ μ).toLp _‖ * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_toLp, mul_comm]
  calc
    _ ≤ (ENNReal.ofReal ‖f‖ * eLpNorm ((Set.range Q).indicator (fun _ : Y => (1 : ℂ))) 2 μ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (indicator_mem Q hQ μ).eLpNorm_lt_top.ne) he
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]

 def globalAvgCLM : ContinuousMap X ℂ →L[ℂ] Lp ℂ 2 μ :=
  (globalAvgLinear Q hQ horbit hact μ).mkContinuous ‖(indicator_mem Q hQ μ).toLp _‖
    (globalAvgLinear_bound Q hQ horbit hact μ)

private lemma globalAvgCLM_matches (f : ContinuousMap X ℂ) (u : Y → ℂ)
    (hf : ∀ x, f x = u (Q x)) :
    (globalAvgCLM Q hQ horbit hact μ f : Y → ℂ) =ᵐ[μ] (Set.range Q).indicator u := by
  filter_upwards [MemLp.coeFn_toLp (globalAvg_memLp Q hQ horbit hact μ f)] with y hy
  change ((globalAvg_memLp Q hQ horbit hact μ f).toLp _) y = _
  rw [hy]
  by_cases h : y ∈ Set.range Q
  · simp only [globalAvg, dite_eq_left h, Set.indicator_of_mem h]
    have hqg : ∀ g : G, Q (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,h⟩) = y := by
      intro g
      calc Q (g • Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,h⟩) =
          Q (Function.surjInv (Set.rangeFactorization_surjective (f := Q)) ⟨y,h⟩) :=
            (horbit _ _).mpr ⟨g⁻¹, inv_smul_smul g _⟩
        _ = y := congrArg Subtype.val (Function.surjInv_eq (Set.rangeFactorization_surjective (f := Q)) ⟨y,h⟩)
    simp_rw [hf, hqg]
    have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hn]
  · simp [globalAvg, h]
end CompactZeroExtension

section FiniteAverage
variable {X B G : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  [TopologicalSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [Group G] [Fintype G] [MulAction G X]
variable (Q : X → B) (hQ : Continuous Q) (hsurj : Function.Surjective Q)
  (horbit : ∀ x y, Q x = Q y ↔ ∃ g : G, g • x = y)
  (hact : ∀ g : G, Continuous (fun x : X => g • x))

 def average (f : ContinuousMap X ℂ) (x : X) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • x)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X] in
private theorem average_invariant (f : ContinuousMap X ℂ) (g : G) (x : X) :
    average (G := G) f (g • x) = average (G := G) f x := by
  unfold average
  congr 1
  simp_rw [← mul_smul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => rfl)

omit [MeasurableSpace X] [BorelSpace X] [PolishSpace X] in
private theorem average_bound (f : ContinuousMap X ℂ) (x : X) :
    ‖average (G := G) f x‖ ≤ ‖f‖ := by
  have hn : (Fintype.card G : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  calc
    ‖average (G := G) f x‖ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g : G, f (g • x)‖ := by
      simp [average]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (g • x)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      exact Finset.sum_le_sum (fun g _ => ContinuousMap.norm_coe_le_norm f _)
    _ = ‖f‖ := by simp [ne_of_gt hn]

 def descendedAverage (f : ContinuousMap X ℂ) (b : B) : ℂ :=
  average (G := G) f (Function.surjInv hsurj b)

include horbit in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  [TopologicalSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] in
private theorem descendedAverage_apply (f : ContinuousMap X ℂ) (x : X) :
    descendedAverage (G := G) Q hsurj f (Q x) = average (G := G) f x := by
  obtain ⟨g, hg⟩ := (horbit x (Function.surjInv hsurj (Q x))).mp
    (Function.surjInv_eq hsurj (Q x)).symm
  rw [descendedAverage, ← hg, average_invariant]

include hQ horbit hact in
private theorem descendedAverage_measurable (f : ContinuousMap X ℂ) :
    Measurable (descendedAverage (G := G) Q hsurj f) := by
  have hm : Measurable (average (G := G) f) := by
    unfold average
    exact measurable_const.mul (Finset.measurable_sum _ (fun g _ =>
      (f.continuous.comp (hact g)).measurable))
  apply (hQ.measurable.measurable_comp_iff_of_surjective hsurj).mp
  convert hm using 1
  funext x
  exact descendedAverage_apply Q hsurj horbit f x

variable (μ : Measure B) [IsFiniteMeasure μ]

include hQ horbit hact in
 theorem descendedAverage_memLp (f : ContinuousMap X ℂ) :
    MemLp (descendedAverage (G := G) Q hsurj f) 2 μ := by
  apply MemLp.of_bound (descendedAverage_measurable Q hQ hsurj horbit hact f).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall (fun b => average_bound (G := G) f _)

 def averageLinear : ContinuousMap X ℂ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (descendedAverage_memLp Q hQ hsurj horbit hact μ f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ (f+g)),
      MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ f),
      MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ g),
      Lp.coeFn_add ((descendedAverage_memLp Q hQ hsurj horbit hact μ f).toLp _)
        ((descendedAverage_memLp Q hQ hsurj horbit hact μ g).toLp _)] with b hfg hf hg hadd
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hfg, hf, hg]
    simp [descendedAverage, average, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ (c • f)),
      MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ f),
      Lp.coeFn_smul c ((descendedAverage_memLp Q hQ hsurj horbit hact μ f).toLp _)] with b hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hsmul]
    simp only [Pi.smul_apply]
    rw [hcf, hf]
    simp [descendedAverage, average, smul_eq_mul, ← Finset.mul_sum, mul_left_comm]

 theorem averageLinear_bound (f : ContinuousMap X ℂ) :
    ‖averageLinear Q hQ hsurj horbit hact μ f‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖f‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg f)
  filter_upwards [MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ f)] with b hb
  change ‖((descendedAverage_memLp Q hQ hsurj horbit hact μ f).toLp _) b‖ ≤ ‖f‖
  rw [hb]
  exact average_bound (G := G) f _

def compactFiniteOrbitAverageToLp : ContinuousMap X ℂ →L[ℂ] Lp ℂ 2 μ :=
  (averageLinear Q hQ hsurj horbit hact μ).mkContinuous
    ((measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹)
    (averageLinear_bound Q hQ hsurj horbit hact μ)

theorem compactFiniteOrbitAverageToLp_ae (f : ContinuousMap X ℂ) :
    (compactFiniteOrbitAverageToLp Q hQ hsurj horbit hact μ f : B → ℂ) =ᵐ[μ]
      fun b => (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (g • Function.surjInv hsurj b) :=
  MemLp.coeFn_toLp (descendedAverage_memLp Q hQ hsurj horbit hact μ f)

theorem compactFiniteOrbitAverageToLp_norm_le :
    ‖compactFiniteOrbitAverageToLp Q hQ hsurj horbit hact μ‖ ≤
      (measureUnivNNReal μ : ℝ) ^ (2 : ENNReal).toReal⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  exact Real.rpow_nonneg (NNReal.coe_nonneg _) _

theorem compactFiniteOrbitAverageToLp_matches (f : ContinuousMap X ℂ) (u : B → ℂ)
    (hf : ∀ x, f x = u (Q x)) :
    (compactFiniteOrbitAverageToLp Q hQ hsurj horbit hact μ f : B → ℂ) =ᵐ[μ] u := by
  filter_upwards [compactFiniteOrbitAverageToLp_ae Q hQ hsurj horbit hact μ f] with b hb
  rw [hb]
  have hqg : ∀ g : G, Q (g • Function.surjInv hsurj b) = b := by
    intro g
    calc Q (g • Function.surjInv hsurj b) = Q (Function.surjInv hsurj b) :=
          (horbit _ _).mpr ⟨g⁻¹, inv_smul_smul g _⟩
      _ = b := Function.surjInv_eq hsurj b
  simp_rw [hf, hqg]
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hn]
end FiniteAverage

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem compact_root_scalar_formula (a : ActualChart (U := U) (H := H))
    (v : Sections F ζ hζ U R P H) (ε : rootsOfUnity 3 F) (x : M F) :
    (scalarRepresentative F ζ hζ U R P H v).val
      (Quotient.mk (coveredRelation F ζ hζ U)
        (labeledA (placeEquiv F ζ hζ) x,
         KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative a.component)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (isotropyChart a).coefficient v x := by
  have he := KPContSectorScalarLineAlgebra.S_apply F ζ hζ U R P H
    (scalarRepresentative F ζ hζ U R P H v) a.component
    (labeledA (placeEquiv F ζ hζ) x)
  have hS : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H v) = v :=
    (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply v
  have hg := (scalarRepresentative F ζ hζ U R P H v).property ε
    (Quotient.mk (coveredRelation F ζ hζ U)
      (labeledA (placeEquiv F ζ hζ) x, (H.atlas U).representative a.component))
  rw [z_mk] at hg
  rw [hg, ← he, hS]
  simp [LiftedChart.coefficient, isotropyChart, ChartKind.representative, chi_coe]

local instance : TopologicalSpace (rootsOfUnity 3 F) := ⊥
local instance : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
local instance : MeasurableSpace (rootsOfUnity 3 F) := ⊤
local instance : BorelSpace (rootsOfUnity 3 F) := ⟨(borel_eq_top_of_discrete).symm⟩

@[instance_reducible]  def rootAction (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hI : ∀ g : Gamma a, (isotropyArrow a g).psi '' C = C) :
    MulAction (Gamma a) (rootsOfUnity 3 F × C) where
  smul g p := (p.1 * g.val.2⁻¹, ⟨(isotropyArrow a g).psi p.2.val, by
    have hh := Set.mem_image_of_mem (isotropyArrow a g).psi p.2.property
    exact (congrArg (fun D : Set (M F) => (isotropyArrow a g).psi p.2.val ∈ D) (hI g)).mp hh⟩)
  one_smul p := by
    apply Prod.ext
    · change p.1 * (1 : rootsOfUnity 3 F)⁻¹ = p.1
      simp
    · apply Subtype.ext
      exact (gammaMulAction a).one_smul p.2.val
  mul_smul g h p := by
    apply Prod.ext
    · change p.1 * (g.val.2 * h.val.2)⁻¹ = (p.1*h.val.2⁻¹)*g.val.2⁻¹
      group
    · apply Subtype.ext
      exact (gammaMulAction a).mul_smul g h p.2.val

private lemma psi_cont (a : ActualChart (U := U) (H := H)) (g : Gamma a) :
    Continuous (isotropyArrow a g).psi := by
  have hA : Continuous (labeledA (placeEquiv F ζ hζ)) := by
    apply continuous_pi
    intro k
    exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
  have hAi : Continuous (labeledAInv (placeEquiv F ζ hζ)) := by
    apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
    exact continuous_pi (fun k => continuous_apply _)
  change Continuous (fun x => labeledAInv (placeEquiv F ζ hζ)
    ((1⁻¹ * g.val.1.val.val * 1) • labeledA (placeEquiv F ζ hζ) x))
  exact hAi.comp ((KPCuspSiegel.continuous_action F _).comp hA)

private lemma rootAction_cont (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hI : ∀ g : Gamma a, (isotropyArrow a g).psi '' C = C) (g : Gamma a) :
    Continuous ((rootAction a C hI).smul g) := by
  apply Continuous.prodMk
  · exact continuous_fst.mul continuous_const
  · exact ((psi_cont a g).comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _

 def rawRootMap (a : ActualChart (U := U) (H := H)) (C : Set (M F)) :
    rootsOfUnity 3 F × C → CoveredSpherical F ζ hζ U := fun p =>
  Quotient.mk (coveredRelation F ζ hζ U)
    (labeledA (placeEquiv F ζ hζ) p.2.val,
     KPCuspGenuineMonodromy.central F ζ hζ p.1 * (H.atlas U).representative a.component)

private lemma rawRootMap_cont (a : ActualChart (U := U) (H := H)) (C : Set (M F)) :
    Continuous (rawRootMap a C) := by
  apply continuous_quotient_mk'.comp
  apply Continuous.prodMk
  · have hA : Continuous (labeledA (placeEquiv F ζ hζ)) := by
      apply continuous_pi
      intro k
      exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous
    exact hA.comp (continuous_subtype_val.comp continuous_snd)
  · apply Continuous.mul _ continuous_const
    exact (continuous_of_discreteTopology).comp continuous_fst

 def rootCoefficient (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (f : ContinuousMap C ℂ) : ContinuousMap (rootsOfUnity 3 F × C) ℂ where
  toFun p := (KPCuspGenuineMonodromy.chi F ζ hζ p.1 : ℂ) * f p.2
  continuous_toFun := by
    apply Continuous.mul _ (f.continuous.comp continuous_snd)
    exact (continuous_of_discreteTopology : Continuous (fun e : rootsOfUnity 3 F =>
      (KPCuspGenuineMonodromy.chi F ζ hζ e : ℂ))).comp continuous_fst

theorem one_chart_compact_coefficient_averaging_source (a : ActualChart (U := U) (H := H))
    (C : Set (M F)) (hC : IsCompact C) (hD : C ⊆ omega a)
    (hI : ∀ g : Gamma a, (isotropyArrow a g).psi '' C = C) :
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    ∃ T : ContinuousMap C ℂ →L[ℂ] KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U,
      (∀ f, ∀ᵐ x ∂coveredMeasure F ζ hζ R U,
        KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x ∉ q a '' C → T f x = 0) ∧
      ∀ (v : Sections F ζ hζ U R P H) (f : ContinuousMap C ℂ),
        (∀ x : C, f x = (isotropyChart a).coefficient v x.val) →
      ∀ b : BorelL2Sections F ζ hζ U R P H, b.val = v →
        (T f : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ) =ᵐ[
          coveredMeasure F ζ hζ R U]
        (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U ⁻¹' (q a '' C)).indicator
          (scalarRepresentative F ζ hζ U R P H v).val := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  letI : Finite (Gamma a) := finite_Gamma a
  letI : Fintype (Gamma a) := Fintype.ofFinite _
  letI : MulAction (Gamma a) (rootsOfUnity 3 F × C) := rootAction a C hI
  letI : IsFiniteMeasureOnCompacts (coveredMeasure F ζ hζ R U) :=
    KPContSectorFixedMeasureLocalFiniteness.coveredMeasure_finiteOnCompacts F ζ hζ R U
  have geom := compact_root_chart_geometry_source a C hC hD hI
  change Set.range (rawRootMap a C) = _ ∧ _ at geom
  have horbit : ∀ p r : rootsOfUnity 3 F × C, rawRootMap a C p = rawRootMap a C r ↔
      ∃ g : Gamma a, (rootAction a C hI).smul g p = r := by
    intro p r
    change rawRootMap a C p = rawRootMap a C r ↔ _
    have hh := geom.2 p r
    change rawRootMap a C p = rawRootMap a C r ↔ _ at hh
    rw [hh]
    constructor
    · rintro ⟨g, hr, hx⟩
      exact ⟨g, Prod.ext hr.symm (Subtype.ext hx.symm)⟩
    · rintro ⟨g, he⟩
      exact ⟨g, (congrArg Prod.fst he).symm, (congrArg (fun p => p.2.val) he).symm⟩
  let L := globalAvgCLM (rawRootMap a C) (rawRootMap_cont a C) horbit
    (rootAction_cont a C hI) (coveredMeasure F ζ hζ R U)
  let J : ContinuousMap C ℂ →ₗ[ℂ] ContinuousMap (rootsOfUnity 3 F × C) ℂ :=
    { toFun := rootCoefficient a C
      map_add' := by intro f g; ext p; simp [rootCoefficient, mul_add]
      map_smul' := by intro c f; ext p; simp [rootCoefficient, smul_eq_mul, mul_left_comm] }
  have hJ : ∀ f, ‖J f‖ ≤ 1 * ‖f‖ := by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le (J f) (norm_nonneg f)).mpr
    intro p
    change ‖(KPCuspGenuineMonodromy.chi F ζ hζ p.1 : ℂ) * f p.2‖ ≤ _
    rw [norm_mul, ← chi_coe, Circle.norm_coe, one_mul]
    exact ContinuousMap.norm_coe_le_norm f _
  let T := L.comp (J.mkContinuous 1 hJ)
  refine ⟨T, ?_, ?_⟩
  · intro f
    filter_upwards [MemLp.coeFn_toLp (globalAvg_memLp (rawRootMap a C) (rawRootMap_cont a C)
      horbit (rootAction_cont a C hI) (coveredMeasure F ζ hζ R U) (rootCoefficient a C f))] with x hx
    intro hnot
    change ((globalAvg_memLp (rawRootMap a C) (rawRootMap_cont a C)
      horbit (rootAction_cont a C hI) (coveredMeasure F ζ hζ R U) (rootCoefficient a C f)).toLp _) x = 0
    rw [hx]
    have hn : x ∉ Set.range (rawRootMap a C) := by rw [geom.1]; exact hnot
    simp [globalAvg, hn]
  · intro v f hf b hb
    have hh := globalAvgCLM_matches (rawRootMap a C) (rawRootMap_cont a C) horbit
      (rootAction_cont a C hI) (coveredMeasure F ζ hζ R U) (rootCoefficient a C f)
      (scalarRepresentative F ζ hζ U R P H v).val (fun p => by
        change (KPCuspGenuineMonodromy.chi F ζ hζ p.1 : ℂ) * f p.2 = _
        rw [hf]
        exact (compact_root_scalar_formula a v p.1 p.2.val).symm)
    change (L (rootCoefficient a C f) : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[_] _
    rw [geom.1] at hh
    exact hh

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
