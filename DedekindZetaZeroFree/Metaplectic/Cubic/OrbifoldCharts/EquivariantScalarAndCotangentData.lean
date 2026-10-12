module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.HyperbolicCharts.LogarithmicCoframe
public import DedekindZetaZeroFree.Analysis.EquivariantSections.WeightedL2.SmoothDensity
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.CoreCutoffsAndL2Reconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorChartEquivariantInputs

open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentCountableShrinking
open KPContActualCotangentChartRestriction
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def baseReindex : M F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (3 * d F)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coefficientIndex (F := F))

def scalarReindex : ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 1) where
  toFun z := WithLp.toLp 2 (fun _ => z)
  invFun z := z 0
  left_inv := by intro z; rfl
  right_inv := by
    intro z
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  norm_map' := by
    intro z
    change ‖WithLp.toLp 2 (Function.const (Fin 1) z)‖ = ‖z‖
    rw [PiLp.norm_toLp_const']
    simp

def toActual (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    KPCuspGenuineMonodromy.SymmetricSpace F :=
  labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm x)

def fromActual (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    EuclideanSpace ℝ (Fin (3 * d F)) :=
  baseReindex (labeledAInv (placeEquiv F ζ hζ) y)

private theorem continuous_labeledA_aux
    (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) : Continuous (labeledA p) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

 theorem continuous_toActual_aux :
    Continuous (toActual (F := F) (ζ := ζ) (hζ := hζ)) := by
  show Continuous (fun x => labeledA (placeEquiv F ζ hζ)
    ((baseReindex (F := F)).symm x))
  exact (continuous_labeledA_aux (F := F) (placeEquiv F ζ hζ)).comp
    (baseReindex (F := F)).symm.continuous

 theorem fromActual_toActual_aux (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    fromActual (ζ := ζ) (hζ := hζ) (toActual (ζ := ζ) (hζ := hζ) x) = x := by
  unfold fromActual toActual
  have h : ∀ y : M F, labeledAInv (placeEquiv F ζ hζ) (labeledA (placeEquiv F ζ hζ) y) = y := by
    intro y; apply PiLp.ext; intro k; simp [labeledAInv, labeledA]
  rw [h, LinearIsometryEquiv.apply_symm_apply]

 theorem toActual_fromActual_aux (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
    toActual (ζ := ζ) (hζ := hζ) (fromActual (ζ := ζ) (hζ := hζ) y) = y := by
  simp only [toActual, fromActual, LinearIsometryEquiv.symm_apply_apply]
  funext k
  simp [labeledA, labeledAInv]

 theorem continuous_fromActual_aux :
    Continuous (fromActual (F := F) (ζ := ζ) (hζ := hζ)) := by
  unfold fromActual labeledAInv
  fun_prop

 def actualMeasurableEquiv : EuclideanSpace ℝ (Fin (3 * d F)) ≃ᵐ
    KPCuspGenuineMonodromy.SymmetricSpace F where
  toFun := toActual (ζ := ζ) (hζ := hζ)
  invFun := fromActual (ζ := ζ) (hζ := hζ)
  left_inv := fromActual_toActual_aux
  right_inv := toActual_fromActual_aux
  measurable_toFun := continuous_toActual_aux.measurable
  measurable_invFun := continuous_fromActual_aux.measurable

private theorem toActual_volume_aux :
    MeasurePreserving (toActual (F := F) (ζ := ζ) (hζ := hζ)) volume volume := by
  have hA : MeasurePreserving (CotangentLogCoframe.A (d F)) volume volume :=
    ⟨(CotangentLogCoframe.A (d F)).continuous.measurable,
      KPContActualGlobalGreen.map_A_volume (d F)⟩
  have hp := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (KPCuspLogShape.dimension F) => ℂ × ℝ) (placeEquiv F ζ hζ)
  have h := hp.comp (hA.comp (baseReindex (F := F)).symm.measurePreserving)
  convert h using 1
  funext x k
  simp [toActual, labeledA, Equiv.piCongrLeft_apply_apply, Function.comp_def]
  rfl

variable (a : ShrunkChart F ζ hζ U R P H)

def chart : Set (EuclideanSpace ℝ (Fin (3 * d F))) :=
  (toActual (ζ := ζ) (hζ := hζ)) ⁻¹' a.domain

def normalization : ℝ :=
  ((H.disintegration U).componentWeight a.component /
    (Nat.card a.Isotropy : ℝ≥0∞)).toReal

def weight (x : EuclideanSpace ℝ (Fin (3 * d F))) : ℝ :=
  normalization a * KPArch.volumeDensity (KPCuspLogShape.dimension F) (toActual (ζ := ζ) (hζ := hζ) x)

def action (γ : Gamma a) (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    EuclideanSpace ℝ (Fin (3 * d F)) :=
  baseReindex ((isotropyArrow a γ).psi ((baseReindex (F := F)).symm x))

 theorem action_one_aux (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    action a 1 x = x := by
  show baseReindex ((isotropyArrow a 1).psi ((baseReindex (F := F)).symm x)) = x
  have h : (isotropyArrow a 1).psi ((baseReindex (F := F)).symm x) =
      (baseReindex (F := F)).symm x :=
    (gammaMulAction a).one_smul _
  rw [h, LinearIsometryEquiv.apply_symm_apply]

 theorem action_mul_aux (γ δ : Gamma a) (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    action a (γ * δ) x = action a γ (action a δ x) := by
  show baseReindex ((isotropyArrow a (γ * δ)).psi ((baseReindex (F := F)).symm x)) =
    baseReindex ((isotropyArrow a γ).psi ((baseReindex (F := F)).symm
      (baseReindex ((isotropyArrow a δ).psi ((baseReindex (F := F)).symm x)))))
  rw [LinearIsometryEquiv.symm_apply_apply]
  congr 1
  exact (gammaMulAction a).mul_smul γ δ _

 theorem toActual_action_aux (γ : Gamma a) (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    toActual (ζ := ζ) (hζ := hζ) (action a γ x) =
      ((γ.val.1).val : KPCuspArithmetic.PGL2 F) • toActual (ζ := ζ) (hζ := hζ) x := by
  have hAA : ∀ w, labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) w) = w := by
    intro w; funext k; simp [labeledA, labeledAInv]
  rw [show toActual (ζ := ζ) (hζ := hζ) (action a γ x) =
      labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi ((baseReindex (F := F)).symm x)) from by
    simp [toActual, action, LinearIsometryEquiv.symm_apply_apply]]
  rw [show (isotropyArrow a γ).psi ((baseReindex (F := F)).symm x) =
      labeledAInv (placeEquiv F ζ hζ) (((γ.val.1).val : KPCuspArithmetic.PGL2 F) •
        labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm x)) from by
    have hg : (isotropyArrow a γ).gamma = γ.val.1.val := rfl
    simp only [Arrow.psi, coordinateMap, isotropyChart, ChartKind.representative,
      inv_one, one_mul, mul_one, hg]]
  rw [hAA]
  rfl

 theorem chart_mem_isotropyChart (x : EuclideanSpace ℝ (Fin (3 * d F)))
    (hx : x ∈ chart a) : (baseReindex (F := F)).symm x ∈ (isotropyChart a).omega := by
  show labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm x) ∈ a.larger.neighborhood
  have h : toActual (ζ := ζ) (hζ := hζ) x ∈ a.domain := hx
  exact a.closure_subset (subset_closure h)

 theorem smooth_weight_aux : ContDiffOn ℝ (⊤ : ℕ∞) (weight a) (chart a) := by
  have htoActual : ContDiff ℝ (⊤ : ℕ∞) (toActual (ζ := ζ) (hζ := hζ)) := by
    show ContDiff ℝ (⊤ : ℕ∞)
      (fun x => labeledA (placeEquiv F ζ hζ) ((baseReindex (F := F)).symm x))
    unfold labeledA
    fun_prop
  have hvol : ContDiff ℝ (⊤ : ℕ∞) (KPArch.volumeDensity (KPCuspLogShape.dimension F)) := by
    unfold KPArch.volumeDensity KPArch.height
    apply contDiff_prod
    intro i hi
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : KPArch.Space (KPCuspLogShape.dimension F) => (z i).2) := by
      fun_prop
    exact (((h1.exp).inv (fun p => ne_of_gt (Real.exp_pos _))).pow 2)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => KPArch.volumeDensity (KPCuspLogShape.dimension F)
        (toActual (ζ := ζ) (hζ := hζ) x)) (chart a) :=
    (hvol.comp htoActual).contDiffOn
  exact (contDiffOn_const.mul hcomp)

private theorem normalization_pos_aux : 0 < normalization a := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  haveI : Nonempty a.Isotropy := ⟨⟨1, one_mem _⟩⟩
  haveI : Finite a.Isotropy := hP.finite_isotropy
  rw [normalization, ENNReal.toReal_pos_iff]
  refine ⟨ENNReal.div_pos_iff.mpr ⟨hP.normalization_positive.ne', ?_⟩,
    ENNReal.div_lt_top hP.normalization_finite.ne ?_⟩
  · exact ENNReal.natCast_ne_top _
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact (Nat.card_pos (α := a.Isotropy)).ne'

 theorem positive_weight_aux : ∀ x ∈ chart a, 0 < weight a x := by
  intro x hx
  refine mul_pos (normalization_pos_aux (a := a)) ?_
  unfold KPArch.volumeDensity KPArch.height
  exact Finset.prod_pos (fun i _ => pow_pos (inv_pos.mpr (Real.exp_pos _)) 2)

 theorem locally_integrable_weight_aux :
    LocallyIntegrableOn (weight a) (chart a) volume :=
  (smooth_weight_aux (a := a)).continuousOn.locallyIntegrableOn
    (a.domain_open.measurableSet.preimage continuous_toActual_aux.measurable)

 theorem smooth_action_aux (γ : Gamma a) :
    ContDiffOn ℝ (⊤ : ℕ∞) (action a γ) (chart a) := by
  have hψ : ContDiffOn ℝ (⊤ : ℕ∞) (isotropyArrow a γ).psi (isotropyChart a).omega :=
    (smooth_metric (isotropyArrow a γ)).1
  have hsymm : ContDiffOn ℝ (⊤ : ℕ∞) (baseReindex (F := F)).symm (chart a) :=
    (baseReindex (F := F)).symm.contDiff.contDiffOn
  have hmaps : Set.MapsTo (baseReindex (F := F)).symm (chart a) (isotropyChart a).omega :=
    fun x hx => chart_mem_isotropyChart (a := a) x hx
  have hcomp1 : ContDiffOn ℝ (⊤ : ℕ∞)
      ((isotropyArrow a γ).psi ∘ (baseReindex (F := F)).symm) (chart a) :=
    hψ.comp hsymm hmaps
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (baseReindex (F := F)) Set.univ :=
    (baseReindex (F := F)).contDiff.contDiffOn
  have h := hb.comp hcomp1 (Set.mapsTo_univ _ _)
  exact h

 theorem chi_norm_aux (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : ε ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp ε.property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun x => (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)) hp

def scalarPhase (ε : rootsOfUnity 3 F) : ℂ ≃ₗᵢ[ℂ] ℂ where
  toFun z := (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * z
  invFun z := (KPCuspGenuineMonodromy.chi F ζ hζ ε⁻¹ : ℂ) * z
  left_inv := by
    intro z
    show (KPCuspGenuineMonodromy.chi F ζ hζ ε⁻¹ : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * z) = z
    rw [← mul_assoc]
    have h : (KPCuspGenuineMonodromy.chi F ζ hζ ε⁻¹ : ℂ) *
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) = 1 := by
      rw [map_inv, Units.inv_mul]
    rw [h, one_mul]
  right_inv := by
    intro z
    show (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ ε⁻¹ : ℂ) * z) = z
    rw [← mul_assoc]
    have h : (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (KPCuspGenuineMonodromy.chi F ζ hζ ε⁻¹ : ℂ) = 1 := by
      rw [map_inv, Units.mul_inv]
    rw [h, one_mul]
  map_add' := by intros; simp [mul_add]
  map_smul' := by intros; simp [mul_left_comm]
  norm_map' := by
    intro z
    show ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * z‖ = ‖z‖
    rw [norm_mul, chi_norm_aux (ζ := ζ) (hζ := hζ) ε, one_mul]

def scalarCocycle (γ : Gamma a) (_x : EuclideanSpace ℝ (Fin (3 * d F))) :
    EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 1) :=
  scalarReindex.symm.trans ((scalarPhase (ζ := ζ) (hζ := hζ) γ.val.2).trans scalarReindex)

 theorem T_one_aux (y : M F) (hy : y ∈ (isotropyChart a).omega) :
    T (isotropyArrow a (1 : Gamma a)) y hy = LinearIsometryEquiv.refl ℂ (E F) := by
  show T (isotropyArrow a 1) y hy = LinearIsometryEquiv.refl ℂ (E F)
  exact (stabilizerRepresentation (A := a) y hy).map_one

 theorem smooth_scalarCocycle_aux (γ : Gamma a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin (3 * d F)) × EuclideanSpace ℂ (Fin 1) =>
        scalarCocycle a γ p.1 p.2) (chart a ×ˢ Set.univ) := by
  have h : (fun p : EuclideanSpace ℝ (Fin (3 * d F)) × EuclideanSpace ℂ (Fin 1) =>
        scalarCocycle a γ p.1 p.2)
      = (fun v : EuclideanSpace ℂ (Fin 1) => scalarCocycle a γ 0 v) ∘ Prod.snd := by
    funext p; rfl
  rw [h]
  have hL : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : EuclideanSpace ℂ (Fin 1) => scalarCocycle a γ 0 v) :=
    (LinearIsometryEquiv.contDiff (scalarCocycle a γ 0)).restrict_scalars ℝ
  exact (hL.comp (contDiff_snd (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (3 * d F)))
    (F := EuclideanSpace ℂ (Fin 1)))).contDiffOn

def cotangentCocycle (γ : Gamma a) (x : EuclideanSpace ℝ (Fin (3 * d F))) :
    EuclideanSpace ℂ (Fin (3 * d F)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (3 * d F)) :=
  if hx : (baseReindex (F := F)).symm x ∈ (isotropyChart a).omega then
    (coefficientReindex (F := F)).symm.trans
      ((T (isotropyArrow a γ) ((baseReindex (F := F)).symm x) hx).trans
        (coefficientReindex (F := F)))
  else LinearIsometryEquiv.refl ℂ _

private theorem weighted_map_aux {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (ρ : B → ENNReal) (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = ν.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  rw [← hf.map_eq]
  rw [← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs,
    lintegral_map (hρ.indicator hs) hf.measurable]
  congr 1

private theorem actualDensity_measurable_aux : Measurable
    (fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
      ENNReal.ofReal (KPArch.volumeDensity (KPCuspLogShape.dimension F) y)) := by
  unfold KPArch.volumeDensity KPArch.height
  fun_prop

private theorem measure_transport_aux :
    MeasurePreserving (toActual (ζ := ζ) (hζ := hζ))
      (KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a))
      (ENNReal.ofReal (normalization a) •
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain) := by
  have hρ := actualDensity_measurable_aux (F := F)
  have hmp : MeasurePreserving (toActual (ζ := ζ) (hζ := hζ))
      (volume.withDensity (fun x => ENNReal.ofReal
        (KPArch.volumeDensity (KPCuspLogShape.dimension F) (toActual (ζ := ζ) (hζ := hζ) x))))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) := by
    refine ⟨continuous_toActual_aux.measurable, ?_⟩
    change Measure.map (toActual (ζ := ζ) (hζ := hζ))
      (volume.withDensity ((fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
        ENNReal.ofReal (KPArch.volumeDensity (KPCuspLogShape.dimension F) y)) ∘
          toActual (ζ := ζ) (hζ := hζ))) =
      volume.withDensity (fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
        ENNReal.ofReal (KPArch.volumeDensity (KPCuspLogShape.dimension F) y))
    exact weighted_map_aux (toActual_volume_aux (ζ := ζ) (hζ := hζ)) _ hρ
  have h := (hmp.restrict_preimage a.domain_open.measurableSet).smul_measure
    (ENNReal.ofReal (normalization a))
  convert h using 1
  rw [restrict_withDensity (a.domain_open.measurableSet.preimage continuous_toActual_aux.measurable)]
  unfold KPChartL2.weightedMeasure weight chart
  have he : (fun x : EuclideanSpace ℝ (Fin (3 * d F)) => ENNReal.ofReal
      (normalization a * KPArch.volumeDensity (KPCuspLogShape.dimension F)
        (toActual (ζ := ζ) (hζ := hζ) x))) =
      ENNReal.ofReal (normalization a) • (fun x => ENNReal.ofReal
        (KPArch.volumeDensity (KPCuspLogShape.dimension F) (toActual (ζ := ζ) (hζ := hζ) x))) := by
    funext x
    exact ENNReal.ofReal_mul (normalization_pos_aux (a := a)).le
  rw [he]
  exact withDensity_smul _ (hρ.comp (continuous_toActual_aux (ζ := ζ) (hζ := hζ)).measurable)

 theorem action_invariant_measure_aux (γ : Gamma a) :
    MeasurePreserving (action a γ)
      (KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a))
      (KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a)) := by
  have hpre : (fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
      (γ.val.1.val : KPCuspArithmetic.PGL2 F) • y) ⁻¹' a.domain = a.domain := by
    ext y
    constructor
    · intro hy
      have hi := a.invariant γ.val.1⁻¹
      have hmem := Set.mem_image_of_mem
        (fun z : KPCuspGenuineMonodromy.SymmetricSpace F =>
          ((γ.val.1⁻¹).val : KPCuspArithmetic.PGL2 F) • z)
        (show (γ.val.1.val : KPCuspArithmetic.PGL2 F) • y ∈ a.domain from hy)
      rw [hi] at hmem
      simpa using hmem
    · intro hy
      have hmem := Set.mem_image_of_mem
        (fun z : KPCuspGenuineMonodromy.SymmetricSpace F =>
          (γ.val.1.val : KPCuspArithmetic.PGL2 F) • z) hy
      rw [a.invariant γ.val.1] at hmem
      exact hmem
  have hg := (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val.1.val).restrict_preimage
    a.domain_open.measurableSet
  rw [hpre] at hg
  have hf := measure_transport_aux (a := a)
  have hi := hf.symm (actualMeasurableEquiv (ζ := ζ) (hζ := hζ))
  have h := hi.comp ((hg.smul_measure (ENNReal.ofReal (normalization a))).comp hf)
  convert h using 1
  funext x
  change action a γ x = fromActual (ζ := ζ) (hζ := hζ)
    ((γ.val.1.val : KPCuspArithmetic.PGL2 F) • toActual (ζ := ζ) (hζ := hζ) x)
  rw [← toActual_action_aux (a := a) γ x, fromActual_toActual_aux]

private theorem lifted_measure_transport_aux :
    Measure.map (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) a.liftedMeasure =
      KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a) := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  haveI : Nonempty a.Isotropy := ⟨⟨1, one_mem _⟩⟩
  haveI : Finite a.Isotropy := hP.finite_isotropy
  have hn : ENNReal.ofReal (normalization a) =
      (H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ENNReal) := by
    apply ENNReal.ofReal_toReal
    exact (ENNReal.div_lt_top hP.normalization_finite.ne
      (by simp only [ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := a.Isotropy)).ne')).ne
  have hm : Measure.map (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
      a.liftedMeasure = ENNReal.ofReal (normalization a) •
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain := by
    unfold ShrunkChart.liftedMeasure
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet).map_comap,
      Subtype.range_coe_subtype]
    change _ • ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain).restrict
      a.domain = _
    rw [Measure.restrict_restrict a.domain_open.measurableSet, Set.inter_self, hn]
  rw [show (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) =
      fromActual (ζ := ζ) (hζ := hζ) ∘ Subtype.val from rfl,
    ← Measure.map_map continuous_fromActual_aux.measurable measurable_subtype_coe, hm]
  exact ((measure_transport_aux (a := a)).symm
    (actualMeasurableEquiv (ζ := ζ) (hζ := hζ))).map_eq

theorem lifted_measure_transport :
    Measure.map (fun y : a.domain => fromActual (ζ := ζ) (hζ := hζ) y.val) a.liftedMeasure =
      KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a) :=
  lifted_measure_transport_aux (a := a)

def scalarData : KPChartL2.Data (3 * d F) 1 (Gamma a) where
  chart := chart a
  open_chart := a.domain_open.preimage continuous_toActual_aux
  weight := weight a
  smooth_weight := smooth_weight_aux (a := a)
  positive_weight := positive_weight_aux (a := a)
  locally_integrable_weight := locally_integrable_weight_aux (a := a)
  act := action a
  act_mem := by
    intro γ x hx
    show toActual (ζ := ζ) (hζ := hζ) (action a γ x) ∈ a.domain
    rw [toActual_action_aux (a := a) γ x]
    have hinv : (fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
        ((γ.val.1).val : KPCuspArithmetic.PGL2 F) • y) '' a.domain = a.domain :=
      a.invariant γ.val.1
    rw [← hinv]
    exact Set.mem_image_of_mem _ hx
  act_one := fun x _ => action_one_aux (a := a) x
  act_mul := fun γ δ x _ => action_mul_aux (a := a) γ δ x
  smooth_action := fun γ => smooth_action_aux (a := a) γ
  invariant_measure := action_invariant_measure_aux (a := a)
  cocycle := scalarCocycle a
  smooth_cocycle := fun γ => smooth_scalarCocycle_aux (a := a) γ
  cocycle_one := by
    intro x hx
    ext z
    simp [scalarCocycle, scalarPhase]
  cocycle_mul := by
    intro γ δ x hx v
    show scalarReindex ((KPCuspGenuineMonodromy.chi F ζ hζ ((γ * δ).val.2) : ℂ) *
        (scalarReindex.symm v)) =
      scalarReindex ((KPCuspGenuineMonodromy.chi F ζ hζ (γ.val.2) : ℂ) *
        (scalarReindex.symm
          (scalarReindex ((KPCuspGenuineMonodromy.chi F ζ hζ (δ.val.2) : ℂ) *
            (scalarReindex.symm v)))))
    rw [LinearIsometryEquiv.symm_apply_apply]
    congr 1
    have h2 : (γ * δ).val.2 = γ.val.2 * δ.val.2 := rfl
    rw [h2, map_mul, Units.val_mul]
    ring

def cotangentData : KPChartL2.Data (3 * d F) (3 * d F) (Gamma a) where
  chart := chart a
  open_chart := a.domain_open.preimage continuous_toActual_aux
  weight := weight a
  smooth_weight := smooth_weight_aux (a := a)
  positive_weight := positive_weight_aux (a := a)
  locally_integrable_weight := locally_integrable_weight_aux (a := a)
  act := action a
  act_mem := by
    intro γ x hx
    show toActual (ζ := ζ) (hζ := hζ) (action a γ x) ∈ a.domain
    rw [toActual_action_aux (a := a) γ x]
    have hinv : (fun y : KPCuspGenuineMonodromy.SymmetricSpace F =>
        ((γ.val.1).val : KPCuspArithmetic.PGL2 F) • y) '' a.domain = a.domain :=
      a.invariant γ.val.1
    rw [← hinv]
    exact Set.mem_image_of_mem _ hx
  act_one := fun x _ => action_one_aux (a := a) x
  act_mul := fun γ δ x _ => action_mul_aux (a := a) γ δ x
  smooth_action := fun γ => smooth_action_aux (a := a) γ
  invariant_measure := action_invariant_measure_aux (a := a)
  cocycle := cotangentCocycle a
  cocycle_one := by
    intro x hx
    have hxω := chart_mem_isotropyChart (a := a) x hx
    show cotangentCocycle a 1 x =
      LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (Fin (3 * d F)))
    unfold cotangentCocycle
    rw [dif_pos hxω, T_one_aux (a := a) ((baseReindex (F := F)).symm x) hxω]
    simp
  cocycle_mul := by
    intro γ δ x hx v
    have hy := chart_mem_isotropyChart (a := a) x hx
    have ht := (isotropyArrow a δ).target hy
    have hax : (baseReindex (F := F)).symm (action a δ x) =
        (isotropyArrow a δ).psi ((baseReindex (F := F)).symm x) := by
      simp [action]
    have hay : (baseReindex (F := F)).symm (action a δ x) ∈ (isotropyChart a).omega := by
      rw [hax]; exact ht
    unfold cotangentCocycle
    simp only [dif_pos hy, dif_pos hay, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply]
    change coefficientReindex (twistedOperator (isotropyArrow a (γ * δ))
        ((baseReindex (F := F)).symm x) (coefficientReindex.symm v)) =
      coefficientReindex (twistedOperator (isotropyArrow a γ)
        ((baseReindex (F := F)).symm (action a δ x))
        (twistedOperator (isotropyArrow a δ) ((baseReindex (F := F)).symm x)
          (coefficientReindex.symm v)))
    rw [hax]
    have hs : T (isotropyArrow a (γ * δ)) ((baseReindex (F := F)).symm x) hy =
        T (comp (isotropyArrow a γ) (isotropyArrow a δ))
          ((baseReindex (F := F)).symm x) ⟨hy, ht⟩ := by
      apply LinearIsometryEquiv.ext
      intro w
      change twistedOperator (isotropyArrow a (γ * δ)) _ w =
        twistedOperator (comp (isotropyArrow a γ) (isotropyArrow a δ)) _ w
      simp only [twistedOperator, Arrow.phase, Arrow.psi,
        KPContCotangentActualGenuineTwistIsotropy.Q]
      rfl
    apply congrArg coefficientReindex
    exact congrArg (fun L : E F ≃ₗᵢ[ℂ] E F => L (coefficientReindex.symm v))
      (hs.trans (T_comp (isotropyArrow a γ) (isotropyArrow a δ)
        ((baseReindex (F := F)).symm x) hy ht))
  smooth_cocycle := by
    intro γ
    let S := chart a ×ˢ (Set.univ : Set (EuclideanSpace ℂ (Fin (3 * d F))))
    have hbase : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin (3 * d F)) × EuclideanSpace ℂ (Fin (3 * d F)) =>
          (baseReindex (F := F)).symm p.1) S :=
      ((baseReindex (F := F)).symm.contDiff.comp contDiff_fst).contDiffOn
    have hmaps : Set.MapsTo (fun p : EuclideanSpace ℝ (Fin (3 * d F)) ×
        EuclideanSpace ℂ (Fin (3 * d F)) => (baseReindex (F := F)).symm p.1)
        S (isotropyArrow a γ).domain := by
      intro p hp
      exact chart_mem_isotropyChart (a := a) p.1 hp.1
    have hop := (smooth_operators (isotropyArrow a γ)).2.comp hbase hmaps
    have hopR : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin (3 * d F)) × EuclideanSpace ℂ (Fin (3 * d F)) =>
          (twistedOperator (isotropyArrow a γ) ((baseReindex (F := F)).symm p.1)).restrictScalars ℝ) S :=
      (ContinuousLinearMap.restrictScalarsL ℂ (E F) (E F) ℝ ℝ).contDiff.comp_contDiffOn hop
    have hcoef : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin (3 * d F)) × EuclideanSpace ℂ (Fin (3 * d F)) =>
          (coefficientReindex (F := F)).symm p.2) S :=
      (((coefficientReindex (F := F)).symm.contDiff.restrict_scalars ℝ).comp
        contDiff_snd).contDiffOn
    have h := ((coefficientReindex (F := F)).contDiff.restrict_scalars ℝ).comp_contDiffOn
      (hopR.clm_apply hcoef)
    apply h.congr
    intro p hp
    simp only [cotangentCocycle, dif_pos (chart_mem_isotropyChart (a := a) p.1 hp.1),
      LinearIsometryEquiv.trans_apply]
    rfl

abbrev measure := KPChartL2.weightedMeasure (3 * d F) (chart a) (weight a)

 def domainEmbedding (y : a.domain) : EuclideanSpace ℝ (Fin (3 * d F)) :=
  fromActual (ζ := ζ) (hζ := hζ) y.val

private theorem domainEmbedding_measurable_aux : MeasurableEmbedding (domainEmbedding a) :=
  (actualMeasurableEquiv (ζ := ζ) (hζ := hζ)).symm.measurableEmbedding.comp
    (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet)

private theorem domainEmbedding_action_aux (γ : Gamma a) (y : a.domain) :
    domainEmbedding a (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
      action a γ (domainEmbedding a y) := by
  change fromActual (ζ := ζ) (hζ := hζ) (γ.val.1.val • y.val) = _
  apply (actualMeasurableEquiv (ζ := ζ) (hζ := hζ)).injective
  change toActual (ζ := ζ) (hζ := hζ) (fromActual (ζ := ζ) (hζ := hζ) _) =
    toActual (ζ := ζ) (hζ := hζ) (action a γ (domainEmbedding a y))
  rw [toActual_fromActual_aux, toActual_action_aux, domainEmbedding, toActual_fromActual_aux]
  rfl

private theorem domainEmbedding_mem_aux (y : a.domain) : domainEmbedding a y ∈ chart a := by
  change toActual (ζ := ζ) (hζ := hζ) (fromActual (ζ := ζ) (hζ := hζ) y.val) ∈ a.domain
  rw [toActual_fromActual_aux]
  exact y.property

private theorem lift_equivariant_aux {r : ℕ}
    (D : KPChartL2.Data (3 * d F) r (Gamma a))
    (hact : D.act = action a) (hμ : KPChartL2.weightedMeasure (3 * d F) D.chart D.weight = measure a)
    (g : a.domain → EuclideanSpace ℂ (Fin r)) (hg : MemLp g 2 a.liftedMeasure)
    (hcov : ∀ γ : Gamma a, ∀ᵐ y ∂a.liftedMeasure,
      g (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
        D.cocycle γ (domainEmbedding a y) (g y)) :
    ∃ f : Lp (EuclideanSpace ℂ (Fin r)) 2 (measure a),
      f ∈ KPChartL2.equivariantL2 (3 * d F) r (Gamma a) (measure a) D.act D.cocycle ∧
      (fun y => f (domainEmbedding a y)) =ᵐ[a.liftedMeasure] g := by
  let G := Function.extend (domainEmbedding a) g 0
  have he := domainEmbedding_measurable_aux (a := a)
  have hmap : Measure.map (domainEmbedding a) a.liftedMeasure = measure a :=
    lifted_measure_transport_aux (a := a)
  have hG : MemLp G 2 (measure a) := by
    rw [← hmap, he.memLp_map_measure_iff]
    simpa only [G, Function.extend_comp he.injective] using hg
  have hpoint (y : a.domain) : G (domainEmbedding a y) = g y :=
    congrFun (Function.extend_comp he.injective g 0) y
  have hpull (p : EuclideanSpace ℝ (Fin (3 * d F)) → Prop)
      (hp : ∀ᵐ x ∂measure a, p x) : ∀ᵐ y ∂a.liftedMeasure, p (domainEmbedding a y) :=
    he.ae_map_iff.mp (Eq.mpr (congrArg (fun μ => ∀ᵐ x ∂μ, p x) hmap) hp)
  have hpush (p : EuclideanSpace ℝ (Fin (3 * d F)) → Prop)
      (hp : ∀ᵐ y ∂a.liftedMeasure, p (domainEmbedding a y)) : ∀ᵐ x ∂measure a, p x :=
    Eq.mp (congrArg (fun μ => ∀ᵐ x ∂μ, p x) hmap) (he.ae_map_iff.mpr hp)
  refine ⟨hG.toLp G, ?_, ?_⟩
  · intro γ
    have hf := hG.coeFn_toLp
    have hpres := D.invariant_measure γ
    rw [hμ] at hpres
    have hfγ := hpres.quasiMeasurePreserving.ae hf
    have hfy := hpull _ hf
    have hfγy := hpull _ hfγ
    apply hpush
    filter_upwards [hfy, hfγy, hcov γ] with y hy hyγ hc
    rw [hyγ, hy, hact, ← domainEmbedding_action_aux]
    simpa only [hpoint] using hc
  · have hfy := hpull _ hG.coeFn_toLp
    filter_upwards [hfy] with y hy
    exact hy.trans (hpoint y)

private theorem cotangentCocycle_domain_aux (γ : Gamma a) (y : a.domain) :
    cotangentCocycle a γ (domainEmbedding a y) =
      (KPContActualCotangentChartRestriction.euclideanData a).tensor γ y := by
  unfold cotangentCocycle
  rw [dif_pos (chart_mem_isotropyChart (a := a) _ (domainEmbedding_mem_aux (a := a) y))]
  apply LinearIsometryEquiv.ext
  intro v
  simp only [LinearIsometryEquiv.trans_apply, KPContActualCotangentChartRestriction.euclideanData,
    KPContActualCotangentPieceHilbertSum.actualTensor]
  change coefficientReindex (twistedOperator (isotropyArrow a γ)
    ((baseReindex (F := F)).symm (domainEmbedding a y)) (coefficientReindex.symm v)) =
    coefficientReindex (twistedOperator (isotropyArrow a γ)
      (KPContActualCotangentPieceHilbertSum.coordinates a y).val (coefficientReindex.symm v))
  simp [domainEmbedding, fromActual, KPContActualCotangentPieceHilbertSum.coordinates]

private theorem localized_memLp_aux {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 a.liftedMeasure)
    (η : a.domain → ℝ) (hη : Measurable η) (hb : ∀ y, 0 ≤ η y ∧ η y ≤ 1) :
    MemLp (fun y => (η y : ℂ) • f y) 2 a.liftedMeasure := by
  apply (Lp.memLp f).mono
  · exact (hη.complex_ofReal.aestronglyMeasurable).smul (Lp.aestronglyMeasurable f)
  · filter_upwards [] with y
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb y).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb y).2

private theorem multiplier_action_aux {n : ℕ}
    (C : Fin n → ShrunkChart F ζ hζ U R P H) (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (partition : KPContActualSectorFiniteSupportPartition.FinitePartition F ζ hζ U R P H C K O)
    (i : Fin n) (γ : Gamma (C i)) (y : (C i).domain) :
    partition.multiplier i ((C i).toBase
      (KPContActualCotangentPieceHilbertSum.actualActionEquiv (C i) γ y)) =
      partition.multiplier i ((C i).toBase y) := by
  rw [← partition.lift_restriction, ← partition.lift_restriction]
  exact partition.lift_invariant i γ.val.1 y.val

private theorem scalar_norm_aux (s : Sections F ζ hζ U R P H) (y : a.domain) :
    sectionNorm F ζ hζ U R P H s (a.toBase y) = ‖(a.coefficient s y : ℂ)‖ := by
  change sectionNorm F ζ hζ U R P H s
    (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      (KPCuspSiegel.projection F _ y.val)) = _
  rw [← (H.atlas U).components_formula]
  exact sectionNorm_component F ζ hζ U R P H s a.component y.val

private theorem scalar_coefficient_memLp_aux (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (fun y : a.domain => (a.coefficient s.val y : ℂ)) 2 a.liftedMeasure := by
  have hmeas : Measurable (fun y : a.domain => (a.coefficient s.val y : ℂ)) :=
    (s.property.1 a.component).comp measurable_subtype_coe
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have he (y : a.domain) : ‖(‖(a.coefficient s.val y : ℂ)‖ ^ 2 : ℝ)‖ₑ =
      squaredNorm F ζ hζ U R P H s.val (a.toBase y) := by
    rw [Real.enorm_eq_ofReal (sq_nonneg _), squaredNorm, scalar_norm_aux]
  simp only [he]
  have ha := every_shrunkChart_properties F ζ hζ U R P H a
  calc
    (∫⁻ y, squaredNorm F ζ hζ U R P H s.val (a.toBase y) ∂a.liftedMeasure) =
        ∫⁻ b, squaredNorm F ζ hζ U R P H s.val b ∂Measure.map a.toBase a.liftedMeasure :=
      (lintegral_map' (squaredNorm_measurable F ζ hζ U R P H s.val s.property.1).aemeasurable
        ha.measurable.aemeasurable).symm
    _ = ∫⁻ b in a.baseDomain, squaredNorm F ζ hζ U R P H s.val b
        ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by rw [ha.exact_pushforward]
    _ ≤ normIntegral F ζ hζ U R P H s.val := setLIntegral_le_lintegral _ _
    _ < ⊤ := s.property.2

private theorem scalar_coeff_congr_aux (s t : BorelL2Sections F ζ hζ U R P H)
    (hst : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t) :
    (fun y : a.domain => (a.coefficient s.val y : ℂ)) =ᵐ[a.liftedMeasure]
      (fun y => (a.coefficient t.val y : ℂ)) := by
  have hn := (mk_eq_mk_iff F ζ hζ U R P H s t).mp hst
  have ha := every_shrunkChart_properties F ζ hζ U R P H a
  have hn' := ae_restrict_of_ae (s := a.baseDomain) hn
  rw [← ha.exact_pushforward] at hn'
  have hmeas := squaredNorm_measurable F ζ hζ U R P H (s.val - t.val) (s - t).property.1
  have hy := (ae_map_iff ha.measurable.aemeasurable
    (measurableSet_eq_fun hmeas measurable_const)).mp hn'
  filter_upwards [hy] with y hy
  change squaredNorm F ζ hζ U R P H (s.val - t.val) (a.toBase y) = 0 at hy
  rw [squaredNorm, scalar_norm_aux] at hy
  change ENNReal.ofReal (‖(a.coefficient s.val y : ℂ) - (a.coefficient t.val y : ℂ)‖ ^ 2) = 0 at hy
  rw [ENNReal.ofReal_eq_zero] at hy
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hy (sq_nonneg _))))

private theorem scalar_coefficient_covariant_aux (s : Sections F ζ hζ U R P H)
    (γ : Gamma a) (y : a.domain) :
    (a.coefficient s (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) : ℂ) =
      (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (a.coefficient s y : ℂ) := by
  let x := labeledAInv (placeEquiv F ζ hζ) y.val
  have hx : x ∈ (isotropyChart a).omega := by
    have h := chart_mem_isotropyChart (a := a) _ (domainEmbedding_mem_aux (a := a) y)
    simpa only [domainEmbedding, fromActual, LinearIsometryEquiv.symm_apply_apply] using h
  have hc := (unitary_phase (isotropyArrow a γ)).2.2.2 s x hx
  have hcoord := KPContActualCotangentPieceHilbertSum.coordinates_action a γ y
  change labeledAInv (placeEquiv F ζ hζ)
    (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y).val =
    (isotropyArrow a γ).psi x at hcoord
  have he : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  have hx' : labeledA (placeEquiv F ζ hζ) x = y.val := he _
  have ht : labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi x) =
      (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y).val := by
    rw [← hcoord, he]
  simp only [LiftedChart.coefficient, Arrow.phase, isotropyChart, ChartKind.representative,
    one_smul, one_mul, inv_one, mul_one, map_one, Units.val_one, hx'] at hc
  change (s a.component).val (labeledA (placeEquiv F ζ hζ) ((isotropyArrow a γ).psi x)) =
    (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (s a.component).val y.val at hc
  rw [ht] at hc
  exact hc

structure Inputs {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (partition : KPContActualSectorFiniteSupportPartition.FinitePartition
      F ζ hζ U R P H C K O) : Prop where
  dimension_positive : 1 ≤ d F
  finite_isotropy : ∀ i, Finite (Gamma (C i))
  positive_normalization : ∀ i, 0 < normalization (C i)
  exact_measure : ∀ i,
    Measure.map (fun y : (C i).domain => fromActual (ζ := ζ) (hζ := hζ) y.val) (C i).liftedMeasure =
      measure (C i)
  actual_action : ∀ i (γ : Gamma (C i)) x,
    toActual (ζ := ζ) (hζ := hζ) (action (C i) γ x) =
      (γ.val.1.val : KPCuspArithmetic.PGL2 F) • toActual (ζ := ζ) (hζ := hζ) x
  genuine_scalar : ∀ i (γ : Gamma (C i)) x z,
    scalarCocycle (C i) γ x (scalarReindex z) =
      scalarReindex ((isotropyArrow (C i) γ).phase
        ((baseReindex (F := F)).symm x) * z)
  actual_tensor : ∀ i (γ : Gamma (C i)) x (hx : x ∈ chart (C i)),
    ∃ hlarge : (baseReindex (F := F)).symm x ∈ (isotropyChart (C i)).omega,
      ∀ v : E F,
        cotangentCocycle (C i) γ x (coefficientReindex v) =
          coefficientReindex
            (T (isotropyArrow (C i) γ) ((baseReindex (F := F)).symm x) hlarge v)
  scalar_localization : ∀ i (u : KPContSectorClosedLpSubspace.H F ζ hζ R U),
    ∃ f : Lp (EuclideanSpace ℂ (Fin 1)) 2 (measure (C i)),
      f ∈ KPChartL2.equivariantL2 (3 * d F) 1 (Gamma (C i))
        (measure (C i)) (scalarData (C i)).act (scalarData (C i)).cocycle ∧
      ∀ s : BorelL2Sections F ζ hζ U R P H,
        mk F ζ hζ U R P H s = sectorLineIsometry F ζ hζ U R P H u →
        (fun y : (C i).domain => f (fromActual (ζ := ζ) (hζ := hζ) y.val)) =ᵐ[(C i).liftedMeasure]
          (fun y => scalarReindex
            ((partition.multiplier i ((C i).toBase y) : ℂ) *
              ((C i).coefficient s.val y : ℂ)))
  cotangent_localization : ∀ i (v : KPContActualSectorCotangentL2.V F ζ hζ U R P H),
    ∃ f : Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 (measure (C i)),
      f ∈ KPChartL2.equivariantL2 (3 * d F) (3 * d F) (Gamma (C i))
        (measure (C i)) (cotangentData (C i)).act (cotangentData (C i)).cocycle ∧
      ∀ r : KPContActualCotangentMeasurableFamilies.SquareFiniteFamily (U := U) (H := H),
        KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r = v →
        (fun y : (C i).domain => f (fromActual (ζ := ζ) (hζ := hζ) y.val)) =ᵐ[(C i).liftedMeasure]
          (fun y => (partition.multiplier i ((C i).toBase y) : ℂ) •
            coefficientReindex (localCoefficient (C i) r.val y))

end DedekindZetaZeroFree.KPContActualSectorChartEquivariantInputs

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_chart_equivariant_inputs
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    {n : ℕ} (C : Fin n → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (partition : KPContActualSectorFiniteSupportPartition.FinitePartition
      F ζ hζ U R P H C K O) :
    KPContActualSectorChartEquivariantInputs.Inputs C K O partition := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := KPArch.complex_places_of_primitive_twelfth_root F ζ hζ
    change 1 ≤ Module.finrank ℚ F / 2
    rw [← h.2.1]
    exact h.2.2
  · intro i
    exact KPContCotangentActualGenuineTwistIsotropy.finite_Gamma (C i)
  · intro i
    exact KPContActualSectorChartEquivariantInputs.normalization_pos_aux (a := C i)
  · intro i
    exact KPContActualSectorChartEquivariantInputs.lifted_measure_transport_aux (a := C i)
  · intro i γ x
    exact KPContActualSectorChartEquivariantInputs.toActual_action_aux (a := C i) γ x
  · intro i γ x z
    simp only [KPContActualSectorChartEquivariantInputs.scalarCocycle,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
    simp [KPContActualSectorChartEquivariantInputs.scalarPhase,
      KPContCotangentActualOverlap.Arrow.phase,
      KPContCotangentActualGenuineTwistIsotropy.isotropyChart,
      KPContCotangentActualGenuineTwistIsotropy.isotropyArrow]
  · intro i γ x hx
    have hlarge := KPContActualSectorChartEquivariantInputs.chart_mem_isotropyChart
      (a := C i) x hx
    refine ⟨hlarge, ?_⟩
    intro v
    simp only [KPContActualSectorChartEquivariantInputs.cotangentCocycle, dif_pos hlarge,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  · intro i u
    obtain ⟨s, hs, -⟩ := realization.sector_line_norm u
    let a := C i
    let coeff : a.domain → EuclideanSpace ℂ (Fin 1) :=
      fun y => KPContActualSectorChartEquivariantInputs.scalarReindex (a.coefficient s.val y : ℂ)
    have hc : MemLp coeff 2 a.liftedMeasure :=
      (KPContActualSectorChartEquivariantInputs.scalarReindex.toContinuousLinearEquiv.toContinuousLinearMap).comp_memLp'
        (KPContActualSectorChartEquivariantInputs.scalar_coefficient_memLp_aux (a := a) s)
    let g : a.domain → EuclideanSpace ℂ (Fin 1) :=
      fun y => (partition.multiplier i (a.toBase y) : ℂ) • coeff y
    have ha := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
    have hg : MemLp g 2 a.liftedMeasure := by
      apply hc.mono
      · exact ((partition.continuous i).measurable.comp ha.measurable).complex_ofReal.aestronglyMeasurable.smul
          hc.aestronglyMeasurable
      · filter_upwards [] with y
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (partition.nonnegative i _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (partition.at_most_one i _)
    have hcov : ∀ γ : KPContCotangentActualGenuineTwistIsotropy.Gamma a,
        ∀ᵐ y ∂a.liftedMeasure,
          g (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
            (KPContActualSectorChartEquivariantInputs.scalarData a).cocycle γ
              (KPContActualSectorChartEquivariantInputs.domainEmbedding a y) (g y) := by
      intro γ
      filter_upwards [] with y
      dsimp [g, coeff]
      rw [KPContActualSectorChartEquivariantInputs.multiplier_action_aux C K O partition i γ y,
        KPContActualSectorChartEquivariantInputs.scalar_coefficient_covariant_aux]
      change _ = KPContActualSectorChartEquivariantInputs.scalarCocycle a γ
        (KPContActualSectorChartEquivariantInputs.domainEmbedding a y) _
      simp only [KPContActualSectorChartEquivariantInputs.scalarCocycle, LinearIsometryEquiv.trans_apply]
      change (partition.multiplier i (a.toBase y) : ℂ) •
        KPContActualSectorChartEquivariantInputs.scalarReindex
          ((KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (a.coefficient s.val y : ℂ)) =
        KPContActualSectorChartEquivariantInputs.scalarReindex
          (KPContActualSectorChartEquivariantInputs.scalarPhase (ζ := ζ) (hζ := hζ) γ.val.2
            (KPContActualSectorChartEquivariantInputs.scalarReindex.symm
              ((partition.multiplier i (a.toBase y) : ℂ) •
                KPContActualSectorChartEquivariantInputs.scalarReindex (a.coefficient s.val y : ℂ))))
      rw [← KPContActualSectorChartEquivariantInputs.scalarReindex.map_smul
        (partition.multiplier i (a.toBase y) : ℂ) (a.coefficient s.val y : ℂ),
        LinearIsometryEquiv.symm_apply_apply]
      rw [← KPContActualSectorChartEquivariantInputs.scalarReindex.map_smul
        (partition.multiplier i (a.toBase y) : ℂ)
        ((KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (a.coefficient s.val y : ℂ))]
      change KPContActualSectorChartEquivariantInputs.scalarReindex
        ((partition.multiplier i (a.toBase y) : ℂ) *
          ((KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (a.coefficient s.val y : ℂ))) =
        KPContActualSectorChartEquivariantInputs.scalarReindex
          ((KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) *
            ((partition.multiplier i (a.toBase y) : ℂ) * (a.coefficient s.val y : ℂ)))
      congr 1
      ring
    obtain ⟨f, hf, hfg⟩ := KPContActualSectorChartEquivariantInputs.lift_equivariant_aux
      (a := a) (KPContActualSectorChartEquivariantInputs.scalarData a) rfl rfl g hg hcov
    refine ⟨f, hf, ?_⟩
    intro t ht
    have hst : KPContSectorLineL2Isometry.mk F ζ hζ U R P H s =
        KPContSectorLineL2Isometry.mk F ζ hζ U R P H t := hs.symm.trans ht.symm
    have hcoeff := KPContActualSectorChartEquivariantInputs.scalar_coeff_congr_aux (a := a) s t hst
    filter_upwards [hfg, hcoeff] with y hy hz
    change f (KPContActualSectorChartEquivariantInputs.domainEmbedding a y) = _
    rw [hy]
    dsimp [g, coeff]
    rw [hz]
    exact (KPContActualSectorChartEquivariantInputs.scalarReindex.map_smul
      (partition.multiplier i (a.toBase y) : ℂ) (a.coefficient t.val y : ℂ)).symm
  · intro i v
    let a := C i
    let qv := KPContActualSectorCotangentL2.restriction F ζ hζ U R P H a v
    let g : a.domain → EuclideanSpace ℂ (Fin (3 * KPContCotangentActualOverlap.d F)) :=
      fun y => (partition.multiplier i (a.toBase y) : ℂ) • qv.val y
    have ha := KPContActualCotangentCountableShrinking.every_shrunkChart_properties F ζ hζ U R P H a
    have hg : MemLp g 2 a.liftedMeasure :=
      KPContActualSectorChartEquivariantInputs.localized_memLp_aux (a := a) qv.val _
        ((partition.continuous i).measurable.comp ha.measurable)
        (fun y => ⟨partition.nonnegative i _, partition.at_most_one i _⟩)
    have hcov : ∀ γ : KPContCotangentActualGenuineTwistIsotropy.Gamma a,
        ∀ᵐ y ∂a.liftedMeasure,
          g (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
            (KPContActualSectorChartEquivariantInputs.cotangentData a).cocycle γ
              (KPContActualSectorChartEquivariantInputs.domainEmbedding a y) (g y) := by
      intro γ
      have hq := qv.property.1 γ
      filter_upwards [hq] with y hy
      change qv.val (KPContActualCotangentPieceHilbertSum.actualActionEquiv a γ y) =
        (KPContActualCotangentChartRestriction.euclideanData a).tensor γ y (qv.val y) at hy
      dsimp [g]
      rw [KPContActualSectorChartEquivariantInputs.multiplier_action_aux C K O partition i γ y,
        hy]
      change _ = KPContActualSectorChartEquivariantInputs.cotangentCocycle a γ
        (KPContActualSectorChartEquivariantInputs.domainEmbedding a y) _
      rw [KPContActualSectorChartEquivariantInputs.cotangentCocycle_domain_aux]
      exact ((KPContActualCotangentChartRestriction.euclideanData a).tensor γ y).map_smul
          (partition.multiplier i (a.toBase y) : ℂ) (qv.val y) |>.symm
    obtain ⟨f, hf, hfg⟩ := KPContActualSectorChartEquivariantInputs.lift_equivariant_aux
      (a := a) (KPContActualSectorChartEquivariantInputs.cotangentData a) rfl rfl g hg hcov
    refine ⟨f, hf, ?_⟩
    intro r hr
    have hp := kp_cont_actual_sector_cotangent_l2 F ζ hζ μG hμG U R hR P H realization
    have hqr := hp.restriction_represented a v r hr
    filter_upwards [hfg, hqr] with y hy hz
    exact hy.trans (congrArg (fun w => (partition.multiplier i (a.toBase y) : ℂ) • w) hz)

end DedekindZetaZeroFree

end
