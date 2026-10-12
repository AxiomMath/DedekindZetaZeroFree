module

public import DedekindZetaZeroFree.Adeles.Quotients.CotangentCharts.MeasurableScalarDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentMeasurableFamilies

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev Coefficients (F : Type) [Field F] [NumberField F] :=
  EuclideanSpace ℂ (Fin (d F) × Fin 3)

abbrev Chart := ShrunkChart F ζ hζ U R P H

abbrev ChartFields (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :=
  ∀ a : ShrunkChart F ζ hζ U R P H, omega a → Coefficients F

theorem omega_subset_larger (a : Chart (U := U) (H := H)) :
    omega a ⊆ (isotropyChart a).omega := by
  intro x hx
  exact a.closure_subset (subset_closure hx)

theorem isotropy_mem (a : Chart (U := U) (H := H)) (γ : Gamma a)
    (x : M F) (hx : x ∈ omega a) : (isotropyArrow a γ).psi x ∈ omega a := by
  have hm := (a.action γ.val.1 ⟨labeledA (placeEquiv F ζ hζ) x, hx⟩).property
  change labeledA (placeEquiv F ζ hζ)
    (coordinateMap (isotropyChart a) (isotropyChart a) γ.val.1.val x) ∈ a.domain
  simp only [coordinateMap, isotropyChart, ChartKind.representative,
    inv_one, one_mul, mul_one]
  have hr (places) (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA places (labeledAInv places y) = y := by
    funext k
    simp [labeledA, labeledAInv]
  rw [hr]
  exact hm

def IsMeasurableCotangentFamily (v : ChartFields F ζ hζ U R P H) : Prop :=
  (∀ a, Measurable (v a)) ∧
  (∀ (a : Chart (U := U) (H := H)) (γ : Gamma a) (x : M F) (hx : x ∈ omega a),
    v a ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      T (isotropyArrow a γ) x (omega_subset_larger a hx) (v a ⟨x, hx⟩)) ∧
  (∀ (a b : Chart (U := U) (H := H)) (e : ActualBranch a b) (x : M F)
      (hx : x ∈ e.arrow.domain),
    v b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      T e.arrow x hx (v a ⟨x, e.source_shrinking hx⟩))

def familySubmodule : Submodule ℂ (ChartFields F ζ hζ U R P H) where
  carrier := {v | IsMeasurableCotangentFamily v}
  zero_mem' := by
    refine ⟨fun a => measurable_const, ?_, ?_⟩
    · intro a γ x hx
      simp only [Pi.zero_apply, map_zero]
    · intro a b e x hx
      simp only [Pi.zero_apply, map_zero]
  add_mem' := by
    intro v w hv hw
    refine ⟨fun a => (hv.1 a).add (hw.1 a), ?_, ?_⟩
    · intro a γ x hx
      simp only [Pi.add_apply, hv.2.1 a γ x hx, hw.2.1 a γ x hx, map_add]
    · intro a b e x hx
      simp only [Pi.add_apply, hv.2.2 a b e x hx, hw.2.2 a b e x hx, map_add]
  smul_mem' := by
    intro c v hv
    refine ⟨fun a => (hv.1 a).const_smul c, ?_, ?_⟩
    · intro a γ x hx
      simp only [Pi.smul_apply, hv.2.1 a γ x hx, map_smul]
    · intro a b e x hx
      simp only [Pi.smul_apply, hv.2.2 a b e x hx, map_smul]

abbrev MeasurableCotangentFamily (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :=
  ↥(familySubmodule (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H))

abbrev Family := MeasurableCotangentFamily F ζ hζ U R P H

def coefficient (v : Family (U := U) (H := H)) (a : Chart (U := U) (H := H)) (x : omega a) :
    Coefficients F := v.val a x

theorem normSquare_descends (v : Family (U := U) (H := H)) :
    ∃! f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0,
      Measurable f ∧ ∀ (a : Chart (U := U) (H := H)) (x : omega a),
        f (q a x.val) = ‖coefficient v a x‖₊ ^ 2 := by
  apply KPContActualCotangentMeasurableMeasure.scalar_descends
    (fun a x => ‖coefficient v a x‖₊ ^ 2)
  · intro a
    exact (v.property.1 a).nnnorm.pow_const 2
  · intro a b e x hx
    change ‖v.val b ⟨e.arrow.psi x, e.target_shrinking hx⟩‖₊ ^ 2 = _
    rw [v.property.2.2 a b e x hx, LinearIsometryEquiv.nnnorm_map]
    rfl

def normSquare (v : Family (U := U) (H := H)) : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0 :=
  Classical.choose (normSquare_descends v)

theorem pairing_descends (v w : Family (U := U) (H := H)) :
    ∃! f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ,
      Measurable f ∧ ∀ (a : Chart (U := U) (H := H)) (x : omega a),
        f (q a x.val) = inner ℂ (coefficient v a x) (coefficient w a x) := by
  apply KPContActualCotangentMeasurableMeasure.scalar_descends
    (fun a x => inner ℂ (coefficient v a x) (coefficient w a x))
  · intro a
    exact (v.property.1 a).inner (w.property.1 a)
  · intro a b e x hx
    change inner ℂ (v.val b ⟨e.arrow.psi x, e.target_shrinking hx⟩)
      (w.val b ⟨e.arrow.psi x, e.target_shrinking hx⟩) = _
    rw [v.property.2.2 a b e x hx, w.property.2.2 a b e x hx,
      LinearIsometryEquiv.inner_map_map]
    rfl

def pair (v w : Family (U := U) (H := H)) : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ :=
  Classical.choose (pairing_descends v w)

theorem measurable_normSquare (v : Family (U := U) (H := H)) : Measurable (normSquare v) := by
  exact (Classical.choose_spec (normSquare_descends v)).1.1

theorem normSquare_chart (v : Family (U := U) (H := H)) (a : Chart (U := U) (H := H)) (x : omega a) :
    normSquare v (q a x.val) = ‖coefficient v a x‖₊ ^ 2 := by
  exact (Classical.choose_spec (normSquare_descends v)).1.2 a x

theorem measurable_pair (v w : Family (U := U) (H := H)) : Measurable (pair v w) := by
  exact (Classical.choose_spec (pairing_descends v w)).1.1

theorem pair_chart (v w : Family (U := U) (H := H)) (a : Chart (U := U) (H := H)) (x : omega a) :
    pair v w (q a x.val) = inner ℂ (coefficient v a x) (coefficient w a x) := by
  exact (Classical.choose_spec (pairing_descends v w)).1.2 a x

abbrev baseMeasure := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U

def chartMeasure (a : Chart (U := U) (H := H)) : Measure (omega a) :=
  Measure.comap (Subtype.val : omega a → M F)
    ((KPContCotangentOverlapNullEquivalence.liftedMeasure a).restrict (omega a))

private theorem exists_lift (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ (a : Chart (U := U) (H := H)) (y : omega a), q a y.val = x := by
  let cover := Classical.choice (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨z, hz⟩ := hn
  let y : omega (cover.chart n) := ⟨labeledAInv (placeEquiv F ζ hζ) z.val, by
    change labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z.val) ∈ (cover.chart n).domain
    have he : labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z.val) = z.val := by
      funext k; simp [labeledA, labeledAInv]
    rw [he]; exact z.property⟩
  refine ⟨cover.chart n, y, ?_⟩
  change q (cover.chart n) y.val = x
  convert hz using 1
  unfold KPContCotangentOverlapRationalBranches.q ShrunkChart.toBase
  congr 2
  funext k
  simp [y, labeledA, labeledAInv]

 theorem normSquare_zero_point (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    normSquare (0 : Family (U := U) (H := H)) x = 0 := by
  obtain ⟨a, y, rfl⟩ := exists_lift (H := H) x
  rw [normSquare_chart]
  simp [coefficient]

private theorem normSquare_eq_zero_iff (v : Family (U := U) (H := H))
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    normSquare v x = 0 ↔ ∀ (a : Chart (U := U) (H := H)) (y : omega a),
      q a y.val = x → coefficient v a y = 0 := by
  constructor
  · intro hv a y hy
    rw [← hy, normSquare_chart] at hv
    simpa only [pow_eq_zero_iff (by decide : 2 ≠ 0), nnnorm_eq_zero] using hv
  · intro hv
    obtain ⟨a, y, hy⟩ := exists_lift (H := H) x
    rw [← hy, normSquare_chart, hv a y hy]
    simp

 theorem normSquare_add_zero (v w : Family (U := U) (H := H))
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hv : normSquare v x = 0)
    (hw : normSquare w x = 0) : normSquare (v + w) x = 0 := by
  apply (normSquare_eq_zero_iff _ _).mpr
  intro a y hy
  have h1 := (normSquare_eq_zero_iff v x).mp hv a y hy
  have h2 := (normSquare_eq_zero_iff w x).mp hw a y hy
  change coefficient v a y + coefficient w a y = 0
  rw [h1, h2, add_zero]

 theorem normSquare_smul_zero (c : ℂ) (v : Family (U := U) (H := H))
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hv : normSquare v x = 0) :
    normSquare (c • v) x = 0 := by
  apply (normSquare_eq_zero_iff _ _).mpr
  intro a y hy
  change c • coefficient v a y = 0
  rw [(normSquare_eq_zero_iff v x).mp hv a y hy, smul_zero]

 theorem normSquare_add_bound (v w : Family (U := U) (H := H))
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    (normSquare (v + w) x : ℝ) ≤ 2 * ((normSquare v x : ℝ) + (normSquare w x : ℝ)) := by
  obtain ⟨a, y, rfl⟩ := exists_lift (H := H) x
  rw [normSquare_chart, normSquare_chart, normSquare_chart]
  simp only [NNReal.coe_pow, coe_nnnorm]
  have he := parallelogram_law_with_norm ℂ (coefficient v a y) (coefficient w a y)
  change ‖coefficient v a y + coefficient w a y‖ ^ 2 ≤ _
  nlinarith [sq_nonneg ‖coefficient v a y - coefficient w a y‖]

 theorem normSquare_smul_point (c : ℂ) (v : Family (U := U) (H := H))
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    (normSquare (c • v) x : ℝ) = ‖c‖ ^ 2 * (normSquare v x : ℝ) := by
  obtain ⟨a, y, rfl⟩ := exists_lift (H := H) x
  rw [normSquare_chart, normSquare_chart]
  simp only [NNReal.coe_pow, coe_nnnorm]
  change ‖c • coefficient v a y‖ ^ 2 = _
  rw [norm_smul, mul_pow]

def squareFinite (v : Family (U := U) (H := H)) : Prop :=
  (∫⁻ x, ENNReal.ofReal ((normSquare v x : ℝ)) ∂(baseMeasure (R := R) (P := P) (U := U))) < ⊤

def squareFiniteSubmodule : Submodule ℂ (Family (U := U) (H := H)) where
  carrier := {v | squareFinite v}
  zero_mem' := by
    change squareFinite (0 : Family (U := U) (H := H))
    unfold squareFinite
    simp only [normSquare_zero_point, NNReal.coe_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact ENNReal.zero_lt_top
  add_mem' := by
    intro v w hv hw
    unfold squareFinite at hv hw ⊢
    have hbound : ∀ x, ENNReal.ofReal ((normSquare (v + w) x : ℝ)) ≤
        2 * (ENNReal.ofReal ((normSquare v x : ℝ)) + ENNReal.ofReal ((normSquare w x : ℝ))) := by
      intro x
      calc
        _ ≤ ENNReal.ofReal (2 * ((normSquare v x : ℝ) + (normSquare w x : ℝ))) :=
          ENNReal.ofReal_le_ofReal (normSquare_add_bound v w x)
        _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
          norm_num
    apply lt_of_le_of_lt (lintegral_mono hbound)
    rw [lintegral_const_mul, lintegral_add_left]
    · exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hv, hw⟩)
    · exact (measurable_normSquare v).coe_nnreal_real.ennreal_ofReal
    · exact ((measurable_normSquare v).coe_nnreal_real.ennreal_ofReal).add
        ((measurable_normSquare w).coe_nnreal_real.ennreal_ofReal)
  smul_mem' := by
    intro c v hv
    unfold squareFinite at hv ⊢
    change (∫⁻ x, ENNReal.ofReal ((normSquare (c • v) x : ℝ)) ∂baseMeasure) < ⊤
    simp_rw [normSquare_smul_point, ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
    rw [lintegral_const_mul]
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv
    · exact (measurable_normSquare v).coe_nnreal_real.ennreal_ofReal

abbrev SquareFiniteFamily := ↥(squareFiniteSubmodule (U := U) (H := H))

def AeEquivalent (v w : Family (U := U) (H := H)) : Prop :=
  ∀ᵐ x ∂(baseMeasure (R := R) (P := P) (U := U)), normSquare (v - w) x = 0

def nullSubmodule : Submodule ℂ (SquareFiniteFamily (U := U) (H := H)) where
  carrier := {v | AeEquivalent v.val 0}
  zero_mem' := by
    change ∀ᵐ x ∂baseMeasure, normSquare (0 - 0 : Family (U := U) (H := H)) x = 0
    simp only [sub_self]
    exact Filter.Eventually.of_forall normSquare_zero_point
  add_mem' := by
    intro v w hv hw
    change ∀ᵐ x ∂baseMeasure, normSquare (v.val + w.val - 0) x = 0
    change ∀ᵐ x ∂baseMeasure, normSquare (v.val - 0) x = 0 at hv
    change ∀ᵐ x ∂baseMeasure, normSquare (w.val - 0) x = 0 at hw
    simp only [sub_zero] at hv hw ⊢
    filter_upwards [hv, hw] with x hx hy
    exact normSquare_add_zero _ _ x hx hy
  smul_mem' := by
    intro c v hv
    change ∀ᵐ x ∂baseMeasure, normSquare (c • v.val - 0) x = 0
    change ∀ᵐ x ∂baseMeasure, normSquare (v.val - 0) x = 0 at hv
    simp only [sub_zero] at hv ⊢
    filter_upwards [hv] with x hx
    exact normSquare_smul_zero c _ x hx

abbrev CotangentAeQuotient :=
  Quotient (Submodule.quotientRel (R := ℂ)
    (M := SquareFiniteFamily (U := U) (H := H)) (nullSubmodule (U := U) (H := H)))

instance quotientAddCommGroup : AddCommGroup (CotangentAeQuotient (U := U) (H := H)) := by
  exact @Submodule.Quotient.addCommGroup ℂ (SquareFiniteFamily (U := U) (H := H))
    _ (Submodule.addCommGroup (squareFiniteSubmodule (U := U) (H := H)))
    (Submodule.module (squareFiniteSubmodule (U := U) (H := H))) nullSubmodule

instance quotientModule : Module ℂ (CotangentAeQuotient (U := U) (H := H)) := by
  exact @Submodule.Quotient.module ℂ (SquareFiniteFamily (U := U) (H := H))
    _ (Submodule.addCommGroup (squareFiniteSubmodule (U := U) (H := H)))
    (Submodule.module (squareFiniteSubmodule (U := U) (H := H))) nullSubmodule

def toAeQuotient : SquareFiniteFamily (U := U) (H := H) →ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) where
  toFun := Quotient.mk''
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

theorem toAeQuotient_surjective :
    Function.Surjective (toAeQuotient (U := U) (H := H)) := by
  intro q
  exact Quotient.inductionOn q (fun v => ⟨v, rfl⟩)

theorem toAeQuotient_add (v w : SquareFiniteFamily (U := U) (H := H)) :
    toAeQuotient (v + w) = toAeQuotient v + toAeQuotient w := by
  exact map_add toAeQuotient v w

theorem toAeQuotient_smul (c : ℂ) (v : SquareFiniteFamily (U := U) (H := H)) :
    toAeQuotient (c • v) = c • toAeQuotient v := by
  exact map_smul toAeQuotient c v

theorem toAeQuotient_eq_iff (v w : SquareFiniteFamily (U := U) (H := H)) :
    toAeQuotient v = toAeQuotient w ↔ AeEquivalent v.val w.val := by
  change Submodule.Quotient.mk v = Submodule.Quotient.mk w ↔ _
  rw [Submodule.Quotient.eq]
  change AeEquivalent (v - w).val 0 ↔ AeEquivalent v.val w.val
  simp only [AeEquivalent, Submodule.coe_sub, sub_zero]

theorem aeEquivalent_iff_all_charts (v w : Family (U := U) (H := H)) :
    AeEquivalent v w ↔ ∀ a : Chart (U := U) (H := H),
      ∀ᵐ x ∂chartMeasure a, coefficient v a x = coefficient w a x := by
  have hzero (a : Chart (U := U) (H := H)) (x : omega a) :
      normSquare (v - w) (q a x.val) = 0 ↔ coefficient v a x = coefficient w a x := by
    rw [normSquare_chart]
    simp only [pow_eq_zero_iff (by decide : 2 ≠ 0), nnnorm_eq_zero]
    change coefficient v a x - coefficient w a x = 0 ↔ _
    exact sub_eq_zero
  have hmeas : MeasurableSet {x | normSquare (v - w) x = 0} :=
    measurableSet_eq_fun (measurable_normSquare (v - w)) measurable_const
  constructor
  · intro h a
    have ha := (KPContActualCotangentMeasurableMeasure.ae_chart_iff a
      (fun x => normSquare (v - w) x = 0) hmeas).mpr (ae_restrict_of_ae h)
    exact ha.mono fun x hx => (hzero a x).mp hx
  · intro h
    let cover := Classical.choice
      (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
    apply (KPContActualCotangentMeasurableMeasure.ae_cover_iff cover
      (fun x => normSquare (v - w) x = 0) hmeas).mpr
    intro n
    exact (h (cover.chart n)).mono fun x hx => (hzero (cover.chart n) x).mpr hx

end DedekindZetaZeroFree.KPContActualCotangentMeasurableFamilies

namespace DedekindZetaZeroFree

open KPContActualCotangentMeasurableFamilies

end DedekindZetaZeroFree

end
