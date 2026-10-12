module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.CentralHaarInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorFiniteOrbitIntegral

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

include ζ hζ in

theorem card_cubic_center : Nat.card (rootsOfUnity 3 F) = 3 := by
  exact (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ
    (by norm_num : 12 = 4 * 3)).card_rootsOfUnity

private lemma ennreal_inv_mul_eq_inv {o c : ℕ} (h : o * c = 3) :
    (3 : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞) = (o : ℝ≥0∞)⁻¹ := by
  have hcast : (o : ℝ≥0∞) * (c : ℝ≥0∞) = 3 := by
    rw [← Nat.cast_mul, h]; norm_num
  have ho0 : o ≠ 0 := by rintro rfl; simp at h
  have hc0 : c ≠ 0 := by rintro rfl; simp at h
  have ho0' : (o : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr ho0
  have hc0' : (c : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  rw [← hcast, ENNReal.mul_inv (Or.inl ho0') (Or.inr hc0'), mul_assoc,
    ENNReal.inv_mul_cancel hc0' ENNReal.coe_ne_top, mul_one]

private lemma measurable_iff_comp_q (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞) :
    Measurable a ↔ Measurable (a ∘ q F ζ hζ U) := by
  have hmap := Continuous.map_borel_eq
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U)
  rw [show KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU F ζ hζ U =
        borel (KPFiniteCuspAtlas.rawXU F ζ hζ U) from rfl,
      show instMeasurableSpaceCoveredSpherical F ζ hζ U =
        borel (CoveredSpherical F ζ hζ U) from rfl]
  rw [measurable_iff_le_map, measurable_iff_le_map, ← hmap, MeasurableSpace.map_comp]

def centralAverage (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) :
    CoveredSpherical F ζ hζ U → ℝ≥0∞ :=
  fun v => (3 : ℝ≥0∞)⁻¹ * ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)

def distinctOrbitAverage (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (v : CoveredSpherical F ζ hζ U) : ℝ≥0∞ :=
  (Nat.card (MulAction.orbit (rootsOfUnity 3 F) v) : ℝ≥0∞)⁻¹ *
    ∑ w ∈ (Finite.finite_mulAction_orbit (M := rootsOfUnity 3 F) v).toFinset, ψ w

theorem centralAverage_invariant (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U) :
    centralAverage F ζ hζ U ψ (z F ζ hζ U ε v) =
      centralAverage F ζ hζ U ψ v := by
  simp only [centralAverage]
  congr 1
  have h1 : (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U δ (z F ζ hζ U ε v))) =
      ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v) := by
    apply Finset.sum_congr rfl
    intro δ _
    congr 1
    exact (mul_smul δ ε v).symm
  have h2 : (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v)) =
      ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U δ v) := by
    rw [show (∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U (δ * ε) v)) =
        ∑ δ : rootsOfUnity 3 F, ψ (z F ζ hζ U ((Equiv.mulRight ε) δ) v) from rfl]
    rw [Equiv.sum_comp (Equiv.mulRight ε) (fun δ => ψ (z F ζ hζ U δ v))]
  rw [h1, h2]

theorem centralAverage_measurable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    Measurable (centralAverage F ζ hζ U ψ) := by
  show Measurable (fun v => (3 : ℝ≥0∞)⁻¹ *
    ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro ε _
  exact hψ.comp (z F ζ hζ U ε).continuous.measurable

theorem existsUnique_borel_descent (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    ∃! a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞,
      Measurable a ∧ ∀ v, a (q F ζ hζ U v) = centralAverage F ζ hζ U ψ v := by
  have hf : Measurable (centralAverage F ζ hζ U ψ) := centralAverage_measurable F ζ hζ U ψ hψ
  have hfiber : ∀ v w, q F ζ hζ U v = q F ζ hζ U w →
      centralAverage F ζ hζ U ψ v = centralAverage F ζ hζ U ψ w := by
    intro v w hvw
    obtain ⟨ε, rfl⟩ :=
      (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U v w).mp hvw
    exact (centralAverage_invariant F ζ hζ U ψ ε v).symm
  obtain ⟨g, hg⟩ :=
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U).hasRightInverse
  have hgq : ∀ v, q F ζ hζ U (g (q F ζ hζ U v)) = q F ζ hζ U v :=
    fun v => hg (q F ζ hζ U v)
  refine ⟨fun b => centralAverage F ζ hζ U ψ (g b), ⟨?_, ?_⟩, ?_⟩
  · rw [measurable_iff_comp_q F ζ hζ U]
    have hcomp : (fun b => centralAverage F ζ hζ U ψ (g b)) ∘ q F ζ hζ U =
        centralAverage F ζ hζ U ψ := by
      funext v
      exact hfiber (g (q F ζ hζ U v)) v (hgq v)
    rw [hcomp]
    exact hf
  · intro v
    exact hfiber (g (q F ζ hζ U v)) v (hgq v)
  · intro a ha
    funext b
    obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U b
    exact (ha.2 v).trans (hfiber (g (q F ζ hζ U v)) v (hgq v)).symm

def borelDescent (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  Classical.choose (existsUnique_borel_descent F ζ hζ U ψ hψ).exists

theorem borelDescent_measurable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    Measurable (borelDescent F ζ hζ U ψ hψ) :=
  (Classical.choose_spec (existsUnique_borel_descent F ζ hζ U ψ hψ).exists).1

theorem borelDescent_q (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ)
    (v : CoveredSpherical F ζ hζ U) :
    borelDescent F ζ hζ U ψ hψ (q F ζ hζ U v) =
      centralAverage F ζ hζ U ψ v :=
  (Classical.choose_spec (existsUnique_borel_descent F ζ hζ U ψ hψ).exists).2 v

private lemma lintegral_centralAverage
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
  have hcard : Nat.card (rootsOfUnity 3 F) = 3 :=
    (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ
      (by norm_num : 12 = 4 * 3)).card_rootsOfUnity
  have hzmeas : ∀ ε : rootsOfUnity 3 F, Measurable (z F ζ hζ U ε) :=
    fun ε => (z F ζ hζ U ε).continuous.measurable
  have hmp : ∀ ε : rootsOfUnity 3 F,
      (∫⁻ v, ψ (z F ζ hζ U ε v) ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U :=
    fun ε =>
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).lintegral_comp hψ
  have hmeas : Measurable (fun v => ∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)) :=
    Finset.measurable_sum _ (fun ε _ => hψ.comp (hzmeas ε))
  calc
    (∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U)
        = ∫⁻ v, (3 : ℝ≥0∞)⁻¹ * (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
            ∂coveredMeasure F ζ hζ R U := rfl
    _ = (3 : ℝ≥0∞)⁻¹ * ∫⁻ v, (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v))
            ∂coveredMeasure F ζ hζ R U := lintegral_const_mul _ hmeas
    _ = (3 : ℝ≥0∞)⁻¹ * ∑ ε : rootsOfUnity 3 F,
            ∫⁻ v, ψ (z F ζ hζ U ε v) ∂coveredMeasure F ζ hζ R U := by
          rw [lintegral_finsetSum (f := fun ε v => ψ (z F ζ hζ U ε v)) Finset.univ
            (fun ε _ => hψ.comp (hzmeas ε))]
    _ = (3 : ℝ≥0∞)⁻¹ * ∑ _ε : rootsOfUnity 3 F,
            ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
          congr 1
          exact Finset.sum_congr rfl (fun ε _ => hmp ε)
    _ = (3 : ℝ≥0∞)⁻¹ * ((Nat.card (rootsOfUnity 3 F) : ℝ≥0∞) *
            ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) := by
          congr 1
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    _ = ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
          rw [hcard, show (↑(3 : ℕ) : ℝ≥0∞) = 3 from by norm_num, ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem lintegral_borelDescent
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ b, borelDescent F ζ hζ U ψ hψ b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  rw [← map_q_coveredMeasure F ζ hζ R P U]
  rw [lintegral_map (borelDescent_measurable F ζ hζ U ψ hψ)
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable]
  rw [show (∫⁻ v, borelDescent F ζ hζ U ψ hψ (q F ζ hζ U v)
        ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, centralAverage F ζ hζ U ψ v ∂coveredMeasure F ζ hζ R U from
    lintegral_congr (fun v => borelDescent_q F ζ hζ U ψ hψ v)]
  exact (lintegral_centralAverage F ζ hζ R U ψ hψ).symm

theorem orbit_card_mul_stabilizer_card
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (v : CoveredSpherical F ζ hζ U) :
    Nat.card (MulAction.orbit (rootsOfUnity 3 F) v) *
      Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) = 3 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (G := rootsOfUnity 3 F) v)
  rw [Nat.card_prod] at h
  rw [h, (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ (by norm_num : 12 = 4 * 3)).card_rootsOfUnity]

theorem fiber_point_repetitions (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (v w : CoveredSpherical F ζ hζ U) (hw : q F ζ hζ U w = q F ζ hζ U v) :
    Nat.card {ε : rootsOfUnity 3 F // z F ζ hζ U ε v = w} =
      Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) := by
  obtain ⟨ε₀, hε₀⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff F ζ hζ U v w).mp hw.symm
  refine Nat.card_congr ?_
  refine
    { toFun := fun e => ⟨ε₀⁻¹ * e.1, ?_⟩
      invFun := fun h => ⟨ε₀ * h.1, ?_⟩
      left_inv := fun e => Subtype.ext (by
        show (ε₀ : rootsOfUnity 3 F) * (ε₀⁻¹ * (e : rootsOfUnity 3 F)) = (e : rootsOfUnity 3 F)
        rw [← mul_assoc, mul_inv_cancel, one_mul])
      right_inv := fun h => Subtype.ext (by
        show (ε₀ : rootsOfUnity 3 F)⁻¹ * (ε₀ * (h : rootsOfUnity 3 F)) = (h : rootsOfUnity 3 F)
        rw [← mul_assoc, inv_mul_cancel, one_mul]) }
  · rw [MulAction.mem_stabilizer_iff]
    show (ε₀⁻¹ * (e : rootsOfUnity 3 F)) • v = v
    have he : e.1 • v = w := e.2
    rw [mul_smul, he, hε₀, show z F ζ hζ U ε₀ v = ε₀ • v from rfl, ← mul_smul, inv_mul_cancel,
      one_smul]
  · have hh : h.1 • v = v := h.2
    rw [show z F ζ hζ U (ε₀ * (h : rootsOfUnity 3 F)) v =
        (ε₀ * (h : rootsOfUnity 3 F)) • v from rfl, mul_smul, hh, hε₀,
      show z F ζ hζ U ε₀ v = ε₀ • v from rfl]

theorem centralAverage_eq_distinctOrbitAverage
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (v : CoveredSpherical F ζ hζ U) :
    centralAverage F ζ hζ U ψ v = distinctOrbitAverage F ζ hζ U ψ v := by
  rw [centralAverage, distinctOrbitAverage]
  set S := (Finite.finite_mulAction_orbit (M := rootsOfUnity 3 F) v).toFinset with hS_def
  set g : rootsOfUnity 3 F → CoveredSpherical F ζ hζ U :=
    fun ε => z F ζ hζ U ε v with hg_def
  have hS : Finset.univ.image g = S := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hS_def, Set.Finite.mem_toFinset,
      MulAction.mem_orbit_iff, hg_def]
    exact ⟨fun ⟨a, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, h⟩⟩
  have hfiber : ∀ w ∈ S, (Finset.univ.filter (fun ε => g ε = w)).card =
      Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) := by
    intro w hw
    have hwq : q F ζ hζ U w = q F ζ hζ U v := by
      rw [hS_def, Set.Finite.mem_toFinset, MulAction.mem_orbit_iff] at hw
      obtain ⟨ε, hε⟩ := hw
      rw [← hε]
      exact KPContSectorCoveredQuotientVocabulary.q_z F ζ hζ U ε v
    have hcard : (Finset.univ.filter (fun ε => g ε = w)).card =
        Nat.card {ε : rootsOfUnity 3 F // z F ζ hζ U ε v = w} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard, fiber_point_repetitions F ζ hζ U v w hwq]
  have hsum : (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)) =
      (Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) : ℝ≥0∞) * ∑ w ∈ S, ψ w := by
    rw [show (∑ ε : rootsOfUnity 3 F, ψ (z F ζ hζ U ε v)) =
        ∑ ε ∈ Finset.univ, ψ (g ε) from rfl, Finset.sum_comp (fun w => ψ w) g, hS]
    rw [show (∑ w ∈ S,
        (Finset.univ.filter (fun ε => g ε = w)).card • ψ w) =
        ∑ w ∈ S, (Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v) : ℝ≥0∞) * ψ w from
      Finset.sum_congr rfl fun w hw => by rw [hfiber w hw, nsmul_eq_mul]]
    rw [Finset.mul_sum]
  rw [hsum, ← mul_assoc, ennreal_inv_mul_eq_inv (orbit_card_mul_stabilizer_card F ζ hζ U v)]

theorem centralAverage_indicator
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) :
    centralAverage F ζ hζ U ((q F ζ hζ U ⁻¹' E).indicator ψ) =
      (q F ζ hζ U ⁻¹' E).indicator (centralAverage F ζ hζ U ψ) := by
  funext v
  by_cases hv : q F ζ hζ U v ∈ E
  · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hv), centralAverage, centralAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    rw [Set.indicator_of_mem]
    show q F ζ hζ U (z F ζ hζ U ε v) ∈ E
    rw [KPContSectorCoveredQuotientVocabulary.q_z F ζ hζ U ε v]
    exact hv
  · rw [Set.indicator_of_notMem (by simpa using hv), centralAverage]
    have hzero : (∑ ε : rootsOfUnity 3 F,
        ((q F ζ hζ U ⁻¹' E).indicator ψ) (z F ζ hζ U ε v)) = 0 := by
      apply Finset.sum_eq_zero
      intro ε _
      rw [Set.indicator_of_notMem]
      show q F ζ hζ U (z F ζ hζ U ε v) ∉ E
      rw [KPContSectorCoveredQuotientVocabulary.q_z F ζ hζ U ε v]
      exact hv
    rw [hzero, mul_zero]

theorem lintegral_indicator_borelDescent
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
    (∫⁻ v, (q F ζ hζ U ⁻¹' E).indicator ψ v ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ b, E.indicator (borelDescent F ζ hζ U ψ hψ) b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
  have hqm : Measurable (q F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hφ : Measurable ((q F ζ hζ U ⁻¹' E).indicator ψ) := hψ.indicator (hqm hE)
  rw [lintegral_borelDescent F ζ hζ R P U ((q F ζ hζ U ⁻¹' E).indicator ψ) hφ]
  refine lintegral_congr (fun b => ?_)
  obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U b
  rw [borelDescent_q F ζ hζ U ((q F ζ hζ U ⁻¹' E).indicator ψ) hφ v,
    centralAverage_indicator F ζ hζ U ψ E]
  by_cases hv : q F ζ hζ U v ∈ E
  · rw [Set.indicator_of_mem (s := q F ζ hζ U ⁻¹' E) (a := v) (by simpa using hv)
        (centralAverage F ζ hζ U ψ),
      Set.indicator_of_mem (s := E) (a := q F ζ hζ U v) hv (borelDescent F ζ hζ U ψ hψ),
      borelDescent_q F ζ hζ U ψ hψ v]
  · rw [Set.indicator_of_notMem (s := q F ζ hζ U ⁻¹' E) (a := v) (by simpa using hv)
        (centralAverage F ζ hζ U ψ),
      Set.indicator_of_notMem (s := E) (a := q F ζ hζ U v) hv (borelDescent F ζ hζ U ψ hψ)]

end DedekindZetaZeroFree.KPContSectorFiniteOrbitIntegral

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport
open KPContSectorFiniteOrbitIntegral

theorem kp_cont_sector_finite_orbit_integral
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞) (hψ : Measurable ψ) :
    Nat.card (rootsOfUnity 3 F) = 3 ∧
    (∀ (ε : rootsOfUnity 3 F) v,
      centralAverage F ζ hζ U ψ (z F ζ hζ U ε v) = centralAverage F ζ hζ U ψ v) ∧
    (∀ v, centralAverage F ζ hζ U ψ v = distinctOrbitAverage F ζ hζ U ψ v) ∧
    (∀ (v w : CoveredSpherical F ζ hζ U), q F ζ hζ U w = q F ζ hζ U v →
      Nat.card {ε : rootsOfUnity 3 F // z F ζ hζ U ε v = w} =
        Nat.card (MulAction.stabilizer (rootsOfUnity 3 F) v)) ∧
    ∃! a : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞,
      Measurable a ∧
      (∀ v, a (q F ζ hζ U v) = centralAverage F ζ hζ U ψ v) ∧
      ((∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ b, a b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) ∧
      (∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
        (∫⁻ v, (q F ζ hζ U ⁻¹' E).indicator ψ v ∂coveredMeasure F ζ hζ R U) =
          ∫⁻ b, E.indicator a b
            ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (IsPrimitiveRoot.pow (by norm_num : 0 < 12) hζ
      (by norm_num : 12 = 4 * 3)).card_rootsOfUnity
  · intro ε v
    exact centralAverage_invariant F ζ hζ U ψ ε v
  · intro v
    exact centralAverage_eq_distinctOrbitAverage F ζ hζ U ψ v
  · intro v w hw
    exact fiber_point_repetitions F ζ hζ U v w hw
  · refine ⟨borelDescent F ζ hζ U ψ hψ, ⟨borelDescent_measurable F ζ hζ U ψ hψ,
      borelDescent_q F ζ hζ U ψ hψ, lintegral_borelDescent F ζ hζ R P U ψ hψ,
      fun E hE => lintegral_indicator_borelDescent F ζ hζ R P U ψ hψ E hE⟩, ?_⟩
    intro a ha
    exact (existsUnique_borel_descent F ζ hζ U ψ hψ).unique ⟨ha.1, ha.2.1⟩
      ⟨borelDescent_measurable F ζ hζ U ψ hψ, borelDescent_q F ζ hζ U ψ hψ⟩

end DedekindZetaZeroFree

end
