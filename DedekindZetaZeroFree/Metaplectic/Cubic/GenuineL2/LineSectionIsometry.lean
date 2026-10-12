module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.EquivariantBorelRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineNormDisintegration

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContSectorLineL2Isometry

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorFixedPushforwardSupport KPContSectorSmoothFramesSupport
open KPContSectorPhaseComponentCharts
open KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def scalarRepresentative (s : Sections F ζ hζ U R P H) :
    GenuineCoveredScalars F ζ hζ U :=
  (J F ζ hζ U).symm ((H.atlas U).scalar_realization.symm s)

theorem scalarRepresentative_mk (s : Sections F ζ hζ U R P H)
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    (scalarRepresentative F ζ hζ U R P H s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x,c)) =
        ((H.atlas U).scalar_realization.symm s).val (x,c) := by
  rfl

theorem scalarRepresentative_eq_symm (s : Sections F ζ hζ U R P H) :
    scalarRepresentative F ζ hζ U R P H s = (S F ζ hζ U R P H).symm s := by
  rfl

private lemma recovery_phase (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U) (x : SymmetricSpace F) :
    (scalarRepresentative F ζ hζ U R P H s).val
      (componentHomeomorph F ζ hζ U R P H ⟨i, Quotient.mk _ (m,x)⟩) =
      (phaseCoefficient F ζ hζ U R P H s i m x : ℂ) := by
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  simpa only [heq] using phase_component_restriction F ζ hζ U R P H
    (scalarRepresentative F ζ hζ U R P H s) i m x

theorem borel_iff (s : Sections F ζ hζ U R P H) :
    (∀ i, Measurable (s i).val) ↔
      Measurable (scalarRepresentative F ζ hζ U R P H s).val := by
  constructor
  · intro hs
    let D := Fin (H.atlas U).componentCount × (PhaseSheets F ζ hζ U × SymmetricSpace F)
    let π : D → CoveredSpherical F ζ hζ U := fun p =>
      componentHomeomorph F ζ hζ U R P H ⟨p.1, Quotient.mk _ p.2⟩
    have hπ : Continuous π := by
      apply continuous_prod_of_discrete_left.mpr
      intro i
      have hq : Continuous (fun p : PhaseSheets F ζ hζ U × SymmetricSpace F =>
          (Quotient.mk _ p : PhaseComponent F ζ hζ U R P H i)) := continuous_quotient_mk'
      exact (componentHomeomorph F ζ hζ U R P H).continuous.comp
        (continuous_sigmaMk.comp hq)
    have hsurj : Function.Surjective π := by
      intro v
      obtain ⟨⟨i,w⟩, hw⟩ := (componentHomeomorph F ζ hζ U R P H).surjective v
      obtain ⟨p, rfl⟩ := Quotient.exists_rep w
      exact ⟨(i,p), hw⟩
    letI : MeasurableSpace (PhaseSheets F ζ hζ U) := borel _
    letI : BorelSpace (PhaseSheets F ζ hζ U) := ⟨rfl⟩
    have hmeas : Measurable ((scalarRepresentative F ζ hζ U R P H s).val ∘ π) := by
      apply measurable_from_prod_countable_right
      intro i
      apply measurable_from_prod_countable_right
      intro m
      refine Quotient.inductionOn m ?_
      intro ε
      have heq : (fun x : SymmetricSpace F =>
        (scalarRepresentative F ζ hζ U R P H s).val (π (i, (Quotient.mk _ ε, x)))) =
          fun x => (chi F ζ hζ ε : ℂ) * (s i).val x := by
        funext x
        rw [recovery_phase]
        exact phaseCoefficient_class F ζ hζ U R P H s i ε x
      change Measurable (fun x : SymmetricSpace F =>
        (scalarRepresentative F ζ hζ U R P H s).val (π (i, (Quotient.mk _ ε, x))))
      rw [heq]
      exact measurable_const.mul (hs i)
    rw [measurable_iff_comap_le]
    have hmap := hπ.map_eq_borel hsurj
    rw [← BorelSpace.measurable_eq (α := CoveredSpherical F ζ hζ U)] at hmap
    rw [← hmap, ← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
    exact hmeas.comap_le
  · intro hf i
    have heq : (fun x : SymmetricSpace F => (scalarRepresentative F ζ hζ U R P H s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i))) = (s i).val := by
      funext x
      have h := congrArg (fun t : Sections F ζ hζ U R P H => (t i).val x)
        ((S F ζ hζ U R P H).apply_symm_apply s)
      rw [S_apply] at h
      exact h
    rw [← heq]
    exact hf.comp ((continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)).measurable)

theorem continuous_iff (s : Sections F ζ hζ U R P H) :
    (∀ i, Continuous (s i).val) ↔
      Continuous (scalarRepresentative F ζ hζ U R P H s).val := by
  constructor
  · intro hs
    have hg : Continuous ((scalarRepresentative F ζ hζ U R P H s).val ∘
        componentHomeomorph F ζ hζ U R P H) := by
      apply continuous_sigma
      intro i
      apply isQuotientMap_quotient_mk'.continuous_iff.mpr
      apply continuous_prod_of_discrete_left.mpr
      intro m
      refine Quotient.inductionOn m ?_
      intro ε
      have heq : (fun x : SymmetricSpace F =>
          (scalarRepresentative F ζ hζ U R P H s).val
            (componentHomeomorph F ζ hζ U R P H ⟨i, Quotient.mk _ (Quotient.mk _ ε,x)⟩)) =
          fun x => (chi F ζ hζ ε : ℂ) * (s i).val x := by
        funext x
        rw [recovery_phase]
        exact phaseCoefficient_class F ζ hζ U R P H s i ε x
      change Continuous (fun x : SymmetricSpace F =>
          (scalarRepresentative F ζ hζ U R P H s).val
            (componentHomeomorph F ζ hζ U R P H ⟨i, Quotient.mk _ (Quotient.mk _ ε,x)⟩))
      rw [heq]
      exact continuous_const.mul (hs i)
    have h := hg.comp (componentHomeomorph F ζ hζ U R P H).symm.continuous
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using h
  · intro hf i
    have heq : (fun x : SymmetricSpace F => (scalarRepresentative F ζ hζ U R P H s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i))) = (s i).val := by
      funext x
      have h := congrArg (fun t : Sections F ζ hζ U R P H => (t i).val x)
        ((S F ζ hζ U R P H).apply_symm_apply s)
      rw [S_apply] at h
      exact h
    rw [← heq]
    exact hf.comp (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const))

def squaredNorm (s : Sections F ζ hζ U R P H) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  fun b => ENNReal.ofReal (sectionNorm F ζ hζ U R P H s b ^ 2)

def normIntegral (s : Sections F ζ hζ U R P H) : ℝ≥0∞ :=
  ∫⁻ b, squaredNorm F ζ hζ U R P H s b ∂sphericalMeasure F ζ hζ R P U

 theorem sectionNorm_zero :
    sectionNorm F ζ hζ U R P H (0 : Sections F ζ hζ U R P H) = 0 := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp [componentNorm]

 theorem squaredNorm_zero :
    squaredNorm F ζ hζ U R P H (0 : Sections F ζ hζ U R P H) = 0 := by
  funext b
  simp only [squaredNorm, sectionNorm_zero]
  simp

private theorem componentNorm_add_le (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (y : KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :
    componentNorm F ζ hζ U R P H (s + t) i y ≤
      componentNorm F ζ hζ U R P H s i y + componentNorm F ζ hζ U R P H t i y := by
  refine Quotient.inductionOn y ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  calc ‖((s + t) i).val x‖ = ‖(s i).val x + (t i).val x‖ := by simp
    _ ≤ ‖(s i).val x‖ + ‖(t i).val x‖ := norm_add_le _ _

 theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    0 ≤ sectionNorm F ζ hζ U R P H s b := by
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  exact norm_nonneg _

 theorem sectionNorm_add_le (s t : Sections F ζ hζ U R P H) :
    sectionNorm F ζ hζ U R P H (s + t) ≤
      sectionNorm F ζ hζ U R P H s + sectionNorm F ζ hζ U R P H t := by
  intro b
  simp only [sectionNorm]
  exact componentNorm_add_le F ζ hζ U R P H s t _ _

 theorem sectionNorm_smul (c : ℂ) (s : Sections F ζ hζ U R P H) :
    sectionNorm F ζ hζ U R P H (c • s) =
      fun b => ‖c‖ * sectionNorm F ζ hζ U R P H s b := by
  funext b
  simp only [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 ?_
  intro x
  simp only [componentNorm, Quotient.lift_mk]
  rw [show ((c • s) ((H.atlas U).components.symm b).fst).val x =
      c * (s ((H.atlas U).components.symm b).fst).val x from by simp, norm_mul]

 theorem squaredNorm_add_le (s t : Sections F ζ hζ U R P H)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    squaredNorm F ζ hζ U R P H (s + t) b ≤
      (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H s b +
        (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H t b := by
  have ha := sectionNorm_nonneg F ζ hζ U R P H s b
  have hb := sectionNorm_nonneg F ζ hζ U R P H t b
  have hc := sectionNorm_nonneg F ζ hζ U R P H (s + t) b
  have hle : sectionNorm F ζ hζ U R P H (s + t) b ≤
      sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b :=
    sectionNorm_add_le F ζ hζ U R P H s t b
  have hmain : (sectionNorm F ζ hζ U R P H (s + t) b) ^ 2 ≤
      2 * sectionNorm F ζ hζ U R P H s b ^ 2 + 2 * sectionNorm F ζ hζ U R P H t b ^ 2 := by
    calc (sectionNorm F ζ hζ U R P H (s + t) b) ^ 2
        ≤ (sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b) ^ 2 :=
          pow_le_pow_left₀ hc hle 2
      _ ≤ 2 * (sectionNorm F ζ hζ U R P H s b ^ 2 + sectionNorm F ζ hζ U R P H t b ^ 2) :=
          add_sq_le
      _ = _ := by ring
  simp only [squaredNorm]
  calc ENNReal.ofReal (sectionNorm F ζ hζ U R P H (s + t) b ^ 2)
      ≤ ENNReal.ofReal (2 * sectionNorm F ζ hζ U R P H s b ^ 2 +
          2 * sectionNorm F ζ hζ U R P H t b ^ 2) := ENNReal.ofReal_le_ofReal hmain
    _ = (2 : ℝ≥0∞) * ENNReal.ofReal (sectionNorm F ζ hζ U R P H s b ^ 2) +
          (2 : ℝ≥0∞) * ENNReal.ofReal (sectionNorm F ζ hζ U R P H t b ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := (2:ℝ)) (by norm_num),
          ENNReal.ofReal_mul (p := (2:ℝ)) (by norm_num)]
        norm_num

 theorem squaredNorm_smul (c : ℂ) (s : Sections F ζ hζ U R P H)
    (b : KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :
    squaredNorm F ζ hζ U R P H (c • s) b =
      ENNReal.ofReal (‖c‖ ^ 2) * squaredNorm F ζ hζ U R P H s b := by
  have ha := sectionNorm_nonneg F ζ hζ U R P H s b
  simp only [squaredNorm]
  rw [show sectionNorm F ζ hζ U R P H (c • s) b =
      ‖c‖ * sectionNorm F ζ hζ U R P H s b from
        congrFun (sectionNorm_smul F ζ hζ U R P H c s) b]
  rw [mul_pow, ENNReal.ofReal_mul (by positivity)]

 theorem squaredNorm_measurable_aux (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val) :
    Measurable (squaredNorm F ζ hζ U R P H s) := by
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s)
      ((borel_iff F ζ hζ U R P H s).mp hs)).borel
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  change Measurable (fun b => ENNReal.ofReal
    (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H s)) b ^ 2)) at hn
  rw [heq] at hn
  exact hn

def BorelL2Sections : Submodule ℂ (Sections F ζ hζ U R P H) where
  carrier := {s | (∀ i, Measurable (s i).val) ∧ normIntegral F ζ hζ U R P H s < ⊤}
  zero_mem' := ⟨fun _ => measurable_zero, by
    rw [normIntegral, squaredNorm_zero]; simp⟩
  add_mem' := by
    intro s t hs ht
    refine ⟨fun i => (hs.1 i).add (ht.1 i), ?_⟩
    have hle : normIntegral F ζ hζ U R P H (s + t) ≤
        (2 : ℝ≥0∞) * normIntegral F ζ hζ U R P H s +
          (2 : ℝ≥0∞) * normIntegral F ζ hζ U R P H t := by
      simp only [normIntegral]
      calc ∫⁻ b, squaredNorm F ζ hζ U R P H (s + t) b ∂sphericalMeasure F ζ hζ R P U
          ≤ ∫⁻ b, ((2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H s b +
              (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H t b)
              ∂sphericalMeasure F ζ hζ R P U :=
            lintegral_mono (fun b => squaredNorm_add_le F ζ hζ U R P H s t b)
        _ = (2 : ℝ≥0∞) * ∫⁻ b, squaredNorm F ζ hζ U R P H s b
              ∂sphericalMeasure F ζ hζ R P U +
            (2 : ℝ≥0∞) * ∫⁻ b, squaredNorm F ζ hζ U R P H t b
              ∂sphericalMeasure F ζ hζ R P U := by
            rw [lintegral_add_left ((squaredNorm_measurable_aux F ζ hζ U R P H s hs.1).const_mul 2),
              lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num),
              lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
    refine lt_of_le_of_lt hle ?_
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.mul_lt_top (by norm_num) hs.2, ENNReal.mul_lt_top (by norm_num) ht.2⟩
  smul_mem' := by
    intro c s hs
    refine ⟨fun i => (hs.1 i).const_smul c, ?_⟩
    have heq : normIntegral F ζ hζ U R P H (c • s) =
        ENNReal.ofReal (‖c‖ ^ 2) * normIntegral F ζ hζ U R P H s := by
      simp only [normIntegral]
      rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ 2)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro b
      exact squaredNorm_smul F ζ hζ U R P H c s b
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.2

def BorelL2Scalars : Submodule ℂ (GenuineCoveredScalars F ζ hζ U) where
  carrier := {f | Measurable f.val ∧ MemLp f.val 2 (coveredMeasure F ζ hζ R U)}
  zero_mem' := ⟨measurable_zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    exact ⟨hf.1.const_smul c, hf.2.const_smul c⟩

theorem finite_integral_iff (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val) :
    normIntegral F ζ hζ U R P H s < ⊤ ↔
      MemLp (scalarRepresentative F ζ hζ U R P H s).val 2
        (coveredMeasure F ζ hζ R U) := by
  have hf : Measurable (scalarRepresentative F ζ hζ U R P H s).val :=
    (borel_iff F ζ hζ U R P H s).mp hs
  have hbridge : normIntegral F ζ hζ U R P H s =
      ∫⁻ v, ENNReal.ofReal
        (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ 2)
        ∂coveredMeasure F ζ hζ R U := by
    have hq : Measurable (q F ζ hζ U) :=
      (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
    rw [normIntegral, ← map_q_coveredMeasure F ζ hζ R P U,
      lintegral_map (squaredNorm_measurable_aux F ζ hζ U R P H s hs) hq]
    apply lintegral_congr
    intro v
    have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
      (S F ζ hζ U R P H).apply_symm_apply s
    have hsn : sectionNorm F ζ hζ U R P H
        (S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s)) (q F ζ hζ U v) =
        ‖(scalarRepresentative F ζ hζ U R P H s).val v‖ :=
      sectionNorm_pullback F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) v
    simp only [squaredNorm]
    conv_lhs => rw [← heq]
    rw [hsn]
  have hIntEq : (∫⁻ v, ENNReal.ofReal
        (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ 2)
        ∂coveredMeasure F ζ hζ R U) =
      ∫⁻ v, ‖(scalarRepresentative F ζ hζ U R P H s).val v‖ₑ ^
        (2 : ℝ≥0∞).toReal ∂coveredMeasure F ζ hζ R U := by
    apply lintegral_congr
    intro v
    rw [ENNReal.toReal_ofNat,
      show (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ : ℝ) ^ 2 =
        ‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ (2 : ℝ) from
          (Real.rpow_two _).symm,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    simp
  rw [hbridge, memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf.aestronglyMeasurable, hIntEq]

def borelS : BorelL2Scalars F ζ hζ U R ≃ₗ[ℂ] BorelL2Sections F ζ hζ U R P H where
  toFun f := by
    have hmeas : ∀ i, Measurable ((S F ζ hζ U R P H f.val) i).val := by
      intro i
      have hc : Measurable (fun x : SymmetricSpace F =>
          Quotient.mk (coveredRelation F ζ hζ U) (x, (H.atlas U).representative i)) :=
        (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)).measurable
      have heq : (S F ζ hζ U R P H f.val i).val =
          fun x => f.val.val (Quotient.mk (coveredRelation F ζ hζ U)
            (x, (H.atlas U).representative i)) := by
        funext x; rw [S_apply]
      rw [heq]; exact f.property.1.comp hc
    refine ⟨S F ζ hζ U R P H f.val, hmeas, ?_⟩
    refine (finite_integral_iff F ζ hζ U R P H (S F ζ hζ U R P H f.val) hmeas).mpr ?_
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H (S F ζ hζ U R P H f.val),
      (S F ζ hζ U R P H).symm_apply_apply f.val]
    exact f.property.2
  invFun s := ⟨scalarRepresentative F ζ hζ U R P H s.val,
    (borel_iff F ζ hζ U R P H s.val).mp s.property.1,
    (finite_integral_iff F ζ hζ U R P H s.val s.property.1).mp s.property.2⟩
  left_inv := by
    intro f
    apply Subtype.ext
    show scalarRepresentative F ζ hζ U R P H (S F ζ hζ U R P H f.val) =
      (f.val : GenuineCoveredScalars F ζ hζ U)
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H (S F ζ hζ U R P H f.val),
      (S F ζ hζ U R P H).symm_apply_apply f.val]
  right_inv := by
    intro s
    apply Subtype.ext
    show S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s.val) =
      (s.val : Sections F ζ hζ U R P H)
    rw [scalarRepresentative_eq_symm F ζ hζ U R P H s.val,
      (S F ζ hζ U R P H).apply_symm_apply s.val]
  map_add' := by
    intro f g
    apply Subtype.ext
    simp [map_add]
  map_smul' := by
    intro c f
    apply Subtype.ext
    simp [map_smul]

def nullSections : Submodule ℂ (BorelL2Sections F ζ hζ U R P H) where
  carrier := {s | squaredNorm F ζ hζ U R P H s.val =ᵐ[
    sphericalMeasure F ζ hζ R P U] 0}
  zero_mem' := by
    change squaredNorm F ζ hζ U R P H ((0 : BorelL2Sections F ζ hζ U R P H).val)
      =ᵐ[sphericalMeasure F ζ hζ R P U] 0
    rw [show (0 : BorelL2Sections F ζ hζ U R P H).val =
      (0 : Sections F ζ hζ U R P H) from rfl, squaredNorm_zero]
  add_mem' := by
    intro s t hs ht
    change squaredNorm F ζ hζ U R P H (s.val + t.val) =ᵐ[sphericalMeasure F ζ hζ R P U] 0
    have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[sphericalMeasure F ζ hζ R P U] 0 := hs
    have ht' : squaredNorm F ζ hζ U R P H t.val =ᵐ[sphericalMeasure F ζ hζ R P U] 0 := ht
    have hle : squaredNorm F ζ hζ U R P H (s.val + t.val) ≤ᵐ[sphericalMeasure F ζ hζ R P U]
        fun b => (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H s.val b +
          (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H t.val b :=
      Filter.Eventually.of_forall (fun b => squaredNorm_add_le F ζ hζ U R P H s.val t.val b)
    have hzero : (fun b => (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H s.val b +
          (2 : ℝ≥0∞) * squaredNorm F ζ hζ U R P H t.val b)
        =ᵐ[sphericalMeasure F ζ hζ R P U] 0 := by
      filter_upwards [hs', ht'] with b hb hbt
      simp [hb, hbt]
    exact (hle.trans_eq hzero).antisymm
      (Filter.Eventually.of_forall
        (fun b => (zero_le : (0 : ℝ≥0∞) ≤ squaredNorm F ζ hζ U R P H (s.val + t.val) b)))
  smul_mem' := by
    intro c s hs
    change squaredNorm F ζ hζ U R P H (c • s.val) =ᵐ[sphericalMeasure F ζ hζ R P U] 0
    have hs' : squaredNorm F ζ hζ U R P H s.val =ᵐ[sphericalMeasure F ζ hζ R P U] 0 := hs
    filter_upwards [hs'] with b hb
    rw [squaredNorm_smul F ζ hζ U R P H c s.val b, hb]
    simp

local instance : HasQuotient (BorelL2Sections F ζ hζ U R P H)
    (Submodule ℂ (BorelL2Sections F ζ hζ U R P H)) :=
  @Submodule.hasQuotient ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance

abbrev L2Line := ↥(BorelL2Sections F ζ hζ U R P H) ⧸ nullSections F ζ hζ U R P H

def mk : BorelL2Sections F ζ hζ U R P H →ₗ[ℂ] L2Line F ζ hζ U R P H :=
  @Submodule.mkQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)

theorem mk_eq_mk_iff (s t : BorelL2Sections F ζ hζ U R P H) :
    mk F ζ hζ U R P H s = mk F ζ hζ U R P H t ↔
      squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[
        sphericalMeasure F ζ hζ R P U] 0 := by
  change Submodule.Quotient.mk s = Submodule.Quotient.mk t ↔
    s - t ∈ nullSections F ζ hζ U R P H
  exact @Submodule.Quotient.eq ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H) s t

theorem null_iff_scalar_ae_eq (s t : BorelL2Sections F ζ hζ U R P H) :
    squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[
        sphericalMeasure F ζ hζ R P U] 0 ↔
      (scalarRepresentative F ζ hζ U R P H s.val).val =ᵐ[
        coveredMeasure F ζ hζ R U]
          (scalarRepresentative F ζ hζ U R P H t.val).val := by
  have hmeas := squaredNorm_measurable_aux F ζ hζ U R P H
    (s.val - t.val) (s - t).property.1
  have hq : Measurable (q F ζ hζ U) :=
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable
  have hdesc : (squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[
      sphericalMeasure F ζ hζ R P U] 0) ↔
      ∀ᵐ v ∂coveredMeasure F ζ hζ R U,
        squaredNorm F ζ hζ U R P H (s.val - t.val) (q F ζ hζ U v) = 0 := by
    rw [← map_q_coveredMeasure F ζ hζ R P U]
    exact ae_map_iff hq.aemeasurable (measurableSet_eq_fun hmeas measurable_const)
  rw [hdesc]
  have hpoint (v : CoveredSpherical F ζ hζ U) :
      squaredNorm F ζ hζ U R P H (s.val - t.val) (q F ζ hζ U v) = 0 ↔
      (scalarRepresentative F ζ hζ U R P H s.val).val v =
        (scalarRepresentative F ζ hζ U R P H t.val).val v := by
    have heq : S F ζ hζ U R P H
        (scalarRepresentative F ζ hζ U R P H (s.val - t.val)) = s.val - t.val :=
      (S F ζ hζ U R P H).apply_symm_apply _
    have hnorm := sectionNorm_pullback F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H (s.val - t.val)) v
    rw [heq] at hnorm
    have hsub : scalarRepresentative F ζ hζ U R P H (s.val - t.val) =
        scalarRepresentative F ζ hζ U R P H s.val -
          scalarRepresentative F ζ hζ U R P H t.val := by
      simp only [scalarRepresentative_eq_symm, map_sub]
    rw [squaredNorm, hnorm, hsub]
    change ENNReal.ofReal
      (‖(scalarRepresentative F ζ hζ U R P H s.val).val v -
        (scalarRepresentative F ζ hζ U R P H t.val).val v‖ ^ 2) = 0 ↔ _
    rw [ENNReal.ofReal_eq_zero]
    constructor
    · intro hh
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
        (le_antisymm hh (sq_nonneg _))))
    · intro hh
      simp [hh]
  exact Filter.eventually_congr (Filter.Eventually.of_forall hpoint)

theorem representative_memLp (s : BorelL2Sections F ζ hζ U R P H) :
    MemLp (scalarRepresentative F ζ hζ U R P H s.val).val 2
      (coveredMeasure F ζ hζ R U) :=
  (finite_integral_iff F ζ hζ U R P H s.val s.property.1).mp s.property.2

def toSector : BorelL2Sections F ζ hζ U R P H →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U where
  toFun s := ⟨(representative_memLp F ζ hζ U R P H s).toLp
    (scalarRepresentative F ζ hζ U R P H s.val).val, by
      rw [KPContSectorClosedLpSubspace.mem_H_iff]
      intro ε
      have hcoef : ((representative_memLp F ζ hζ U R P H s).toLp
          (scalarRepresentative F ζ hζ U R P H s.val).val :
            CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U]
          (scalarRepresentative F ζ hζ U R P H s.val).val :=
        MemLp.coeFn_toLp _
      have h1 : ((representative_memLp F ζ hζ U R P H s).toLp
          (scalarRepresentative F ζ hζ U R P H s.val).val :
            CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε =ᵐ[coveredMeasure F ζ hζ R U]
          (scalarRepresentative F ζ hζ U R P H s.val).val ∘ z F ζ hζ U ε :=
        (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).quasiMeasurePreserving.ae_eq_comp
          hcoef
      have h2 : (scalarRepresentative F ζ hζ U R P H s.val).val ∘ z F ζ hζ U ε =ᵐ[
          coveredMeasure F ζ hζ R U]
          (chi F ζ hζ ε : ℂ) • (scalarRepresentative F ζ hζ U R P H s.val).val :=
        Filter.Eventually.of_forall (fun v => by
          rw [Pi.smul_apply, smul_eq_mul]
          exact (scalarRepresentative F ζ hζ U R P H s.val).property ε v)
      have h3 : (chi F ζ hζ ε : ℂ) • (scalarRepresentative F ζ hζ U R P H s.val).val =ᵐ[
          coveredMeasure F ζ hζ R U]
          (chi F ζ hζ ε : ℂ) • ((representative_memLp F ζ hζ U R P H s).toLp
            (scalarRepresentative F ζ hζ U R P H s.val).val :
              CoveredSpherical F ζ hζ U → ℂ) :=
        (hcoef.const_smul (chi F ζ hζ ε : ℂ)).symm
      exact h1.trans (h2.trans h3)⟩
  map_add' := by
    intro s t
    apply Subtype.ext
    simp only [Submodule.coe_add]
    have hsadd : scalarRepresentative F ζ hζ U R P H (s + t) =
        scalarRepresentative F ζ hζ U R P H s + scalarRepresentative F ζ hζ U R P H t := by
      simp only [scalarRepresentative, map_add]
    have hfg : (scalarRepresentative F ζ hζ U R P H (s + t)).val =
        (scalarRepresentative F ζ hζ U R P H s).val +
          (scalarRepresentative F ζ hζ U R P H t).val := by
      rw [hsadd, Submodule.coe_add]
    have hA : (representative_memLp F ζ hζ U R P H (s + t)).toLp
        (scalarRepresentative F ζ hζ U R P H (s + t)).val =
        ((representative_memLp F ζ hζ U R P H s).add
          (representative_memLp F ζ hζ U R P H t)).toLp
          ((scalarRepresentative F ζ hζ U R P H s).val +
            (scalarRepresentative F ζ hζ U R P H t).val) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun v => congrFun hfg v))
    rw [hA, MemLp.toLp_add]
  map_smul' := by
    intro c s
    apply Subtype.ext
    simp only [Submodule.coe_smul]
    have hsmul : scalarRepresentative F ζ hζ U R P H (c • s) =
        c • scalarRepresentative F ζ hζ U R P H s := by
      simp only [scalarRepresentative, map_smul]
    have hfg : (scalarRepresentative F ζ hζ U R P H (c • s)).val =
        c • (scalarRepresentative F ζ hζ U R P H s).val := by
      rw [hsmul, Submodule.coe_smul]
    have hA : (representative_memLp F ζ hζ U R P H (c • s)).toLp
        (scalarRepresentative F ζ hζ U R P H (c • s)).val =
        ((representative_memLp F ζ hζ U R P H s).const_smul c).toLp
          (c • (scalarRepresentative F ζ hζ U R P H s).val) :=
      MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun v => congrFun hfg v))
    rw [hA]
    exact MemLp.toLp_const_smul c (representative_memLp F ζ hζ U R P H s)

def quotientToSector : L2Line F ζ hζ U R P H →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  @Submodule.liftQ ℂ (BorelL2Sections F ζ hζ U R P H)
    inferInstance inferInstance inferInstance (nullSections F ζ hζ U R P H)
    ℂ (KPContSectorClosedLpSubspace.H F ζ hζ R U)
    inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (toSector F ζ hζ U R P H) (by
      intro s hs
      change toSector F ζ hζ U R P H s = 0
      rw [← map_zero (toSector F ζ hζ U R P H)]
      apply Subtype.ext
      have hnull : squaredNorm F ζ hζ U R P H (s.val - (0 : Sections F ζ hζ U R P H)) =ᵐ[
          sphericalMeasure F ζ hζ R P U] 0 := by
        change squaredNorm F ζ hζ U R P H s.val =ᵐ[sphericalMeasure F ζ hζ R P U] 0 at hs
        simpa using hs
      have hae := (null_iff_scalar_ae_eq F ζ hζ U R P H s 0).mp hnull
      exact (representative_memLp F ζ hζ U R P H s).toLp_congr
        (representative_memLp F ζ hζ U R P H 0) hae)

set_option maxHeartbeats 1000000 in

theorem quotientToSector_bijective : Function.Bijective (quotientToSector F ζ hζ U R P H) := by
  constructor
  · intro x y hxy
    obtain ⟨s, hs⟩ := Quotient.exists_rep x
    obtain ⟨t, ht⟩ := Quotient.exists_rep y
    change mk F ζ hζ U R P H s = x at hs
    change mk F ζ hζ U R P H t = y at ht
    rw [← hs, ← ht] at hxy ⊢
    apply (mk_eq_mk_iff F ζ hζ U R P H s t).mpr
    apply (null_iff_scalar_ae_eq F ζ hζ U R P H s t).mpr
    apply ((representative_memLp F ζ hζ U R P H s).toLp_eq_toLp_iff
      (representative_memLp F ζ hζ U R P H t)).mp
    exact congrArg Subtype.val hxy
  · intro u
    obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfg, hfu, hfeq, _⟩ :=
      KPContSectorExactBorelRepresentatives.exists_exact_borel_representative F ζ hζ R U u
    let f₀ : GenuineCoveredScalars F ζ hζ U := ⟨f, hfeq⟩
    let f₁ : BorelL2Scalars F ζ hζ U R := ⟨f₀, hf, hfLp⟩
    let s := borelS F ζ hζ U R P H f₁
    refine ⟨mk F ζ hζ U R P H s, ?_⟩
    apply Subtype.ext
    change (representative_memLp F ζ hζ U R P H s).toLp
      (scalarRepresentative F ζ hζ U R P H s.val).val = _
    have heq : scalarRepresentative F ζ hζ U R P H s.val = f₀ := by
      change (S F ζ hζ U R P H).symm (S F ζ hζ U R P H f₀) = f₀
      exact (S F ζ hζ U R P H).symm_apply_apply f₀
    have hae : (scalarRepresentative F ζ hζ U R P H s.val).val =ᵐ[
        coveredMeasure F ζ hζ R U] f := by rw [heq]
    exact ((representative_memLp F ζ hζ U R P H s).toLp_congr hfLp hae).trans hfu

def lineToSector : L2Line F ζ hζ U R P H ≃ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  LinearEquiv.ofBijective (quotientToSector F ζ hζ U R P H)
    (quotientToSector_bijective F ζ hζ U R P H)

instance instNormedAddCommGroupL2Line : NormedAddCommGroup (L2Line F ζ hζ U R P H) :=
  NormedAddCommGroup.induced _ _ (lineToSector F ζ hζ U R P H).toAddMonoidHom
    (lineToSector F ζ hζ U R P H).injective

instance instNormedSpaceL2Line : NormedSpace ℂ (L2Line F ζ hζ U R P H) :=
  NormedSpace.induced ℂ _ _ (lineToSector F ζ hζ U R P H).toLinearMap

def sectorLineIsometry : KPContSectorClosedLpSubspace.H F ζ hζ R U ≃ₗᵢ[ℂ]
    L2Line F ζ hζ U R P H where
  __ := (lineToSector F ζ hζ U R P H).symm
  norm_map' := by
    intro u
    change ‖lineToSector F ζ hζ U R P H ((lineToSector F ζ hζ U R P H).symm u)‖ = ‖u‖
    rw [LinearEquiv.apply_symm_apply]

instance instCompleteSpaceL2Line : CompleteSpace (L2Line F ζ hζ U R P H) :=
  (sectorLineIsometry F ζ hζ U R P H).symm.toIsometryEquiv.completeSpace

instance instInnerProductSpaceL2Line : InnerProductSpace ℂ (L2Line F ζ hζ U R P H) :=
  InnerProductSpace.induced (lineToSector F ζ hζ U R P H)

theorem norm_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ‖mk F ζ hζ U R P H s‖ ^ 2 = (normIntegral F ζ hζ U R P H s.val).toReal := by
  have hf := (borel_iff F ζ hζ U R P H s.val).mp s.property.1
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s.val) hf).lp_norm
      (representative_memLp F ζ hζ U R P H s)
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s.val) = s.val :=
    (S F ζ hζ U R P H).apply_symm_apply s.val
  change ‖(representative_memLp F ζ hζ U R P H s).toLp
    (scalarRepresentative F ζ hζ U R P H s.val).val‖ ^ 2 = _
  simpa only [KPContSectorFixedLineNormIntegrals.lineNorm, heq, normIntegral, squaredNorm] using hn

theorem ofReal_norm_sq (s : BorelL2Sections F ζ hζ U R P H) :
    ENNReal.ofReal (‖mk F ζ hζ U R P H s‖ ^ 2) = normIntegral F ζ hζ U R P H s.val := by
  rw [norm_sq, ENNReal.ofReal_toReal (ne_of_lt s.property.2)]

theorem sectorLineIsometry_symm_mk (s : BorelL2Sections F ζ hζ U R P H) :
    ((sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H s) :
      KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
    (representative_memLp F ζ hζ U R P H s).toLp
      (scalarRepresentative F ζ hζ U R P H s.val).val := by
  rfl

theorem sectorLineIsometry_toSector (f : BorelL2Scalars F ζ hζ U R) :
    sectorLineIsometry F ζ hζ U R P H
      (toSector F ζ hζ U R P H (borelS F ζ hζ U R P H f)) =
        mk F ζ hζ U R P H (borelS F ζ hζ U R P H f) := by
  change (lineToSector F ζ hζ U R P H).symm
    (lineToSector F ζ hζ U R P H (mk F ζ hζ U R P H (borelS F ζ hζ U R P H f))) = _
  exact (lineToSector F ζ hζ U R P H).symm_apply_apply _

def scalarEmbedding : BorelL2Scalars F ζ hζ U R →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (toSector F ζ hζ U R P H).comp (borelS F ζ hζ U R P H).toLinearMap

theorem scalarEmbedding_coe (f : BorelL2Scalars F ζ hζ U R) :
    (scalarEmbedding F ζ hζ U R P H f : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
      f.property.2.toLp f.val.val := by
  have heq : scalarRepresentative F ζ hζ U R P H (borelS F ζ hζ U R P H f).val = f.val :=
    (S F ζ hζ U R P H).symm_apply_apply f.val
  have hae : (scalarRepresentative F ζ hζ U R P H (borelS F ζ hζ U R P H f).val).val =ᵐ[
      coveredMeasure F ζ hζ R U] f.val.val := by rw [heq]
  exact (representative_memLp F ζ hζ U R P H (borelS F ζ hζ U R P H f)).toLp_congr
    f.property.2 hae

theorem sectorLineIsometry_representative
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (f : BorelL2Scalars F ζ hζ U R)
    (hf : f.property.2.toLp f.val.val =
      (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) :
    sectorLineIsometry F ζ hζ U R P H u =
      mk F ζ hζ U R P H (borelS F ζ hζ U R P H f) := by
  have heq : scalarEmbedding F ζ hζ U R P H f = u :=
    Subtype.ext ((scalarEmbedding_coe F ζ hζ U R P H f).trans hf)
  rw [← heq]
  exact sectorLineIsometry_toSector F ζ hζ U R P H f

def ContinuousL2Scalars : Submodule ℂ (BorelL2Scalars F ζ hζ U R) where
  carrier := {f | Continuous f.val.val}
  zero_mem' := continuous_const
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    exact hf.const_smul c

def ContinuousL2Sections : Submodule ℂ (BorelL2Sections F ζ hζ U R P H) where
  carrier := {s | ∀ i, Continuous (s.val i).val}
  zero_mem' := fun _ => continuous_const
  add_mem' := by
    intro s t hs ht i
    exact (hs i).add (ht i)
  smul_mem' := by
    intro c s hs i
    exact (hs i).const_smul c

def continuousScalarEmbedding : ContinuousL2Scalars F ζ hζ U R →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (scalarEmbedding F ζ hζ U R P H).comp (ContinuousL2Scalars F ζ hζ U R).subtype

def continuousSectionEmbedding : ContinuousL2Sections F ζ hζ U R P H →ₗ[ℂ]
    L2Line F ζ hζ U R P H :=
  (mk F ζ hζ U R P H).comp (ContinuousL2Sections F ζ hζ U R P H).subtype

theorem continuousScalarEmbedding_injective :
    Function.Injective (continuousScalarEmbedding F ζ hζ U R P H) := by
  letI := (levelSupport F ζ hζ R P
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  intro f g hfg
  have hlp := congrArg (fun u : KPContSectorClosedLpSubspace.H F ζ hζ R U => u.val) hfg
  change (scalarEmbedding F ζ hζ U R P H f.val).val =
    (scalarEmbedding F ζ hζ U R P H g.val).val at hlp
  rw [scalarEmbedding_coe, scalarEmbedding_coe] at hlp
  have hae := (f.val.property.2.toLp_eq_toLp_iff g.val.property.2).mp hlp
  have heq := (f.property.ae_eq_iff_eq (coveredMeasure F ζ hζ R U) g.property).mp hae
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext heq

theorem continuousSectionEmbedding_injective :
    Function.Injective (continuousSectionEmbedding F ζ hζ U R P H) := by
  letI := (levelSupport F ζ hζ R P
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1 U).covered_open_positive
  intro s t hst
  have hae := (null_iff_scalar_ae_eq F ζ hζ U R P H s.val t.val).mp
    ((mk_eq_mk_iff F ζ hζ U R P H s.val t.val).mp hst)
  have hs := (continuous_iff F ζ hζ U R P H s.val.val).mp s.property
  have ht := (continuous_iff F ζ hζ U R P H t.val.val).mp t.property
  have heq := (hs.ae_eq_iff_eq (coveredMeasure F ζ hζ R U) ht).mp hae
  have hsct : scalarRepresentative F ζ hζ U R P H s.val.val =
      scalarRepresentative F ζ hζ U R P H t.val.val := Subtype.ext heq
  have hval : s.val.val = t.val.val := (S F ζ hζ U R P H).symm.injective hsct
  exact Subtype.ext (Subtype.ext hval)

def SmoothCompactL2Scalars : Submodule ℂ (BorelL2Scalars F ζ hζ U R) where
  carrier := {f | IsSmoothCovered F ζ hζ U f.val ∧ HasCompactSupport f.val.val}
  zero_mem' := ⟨by
      show IsSmoothCovered F ζ hζ U (0 : GenuineCoveredScalars F ζ hζ U)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U 0).val (x, c))
          = fun _ => (0 : ℂ) := by
        funext x; simp
      rw [h]; exact contDiff_const,
    by
      show HasCompactSupport (0 : CoveredSpherical F ζ hζ U → ℂ)
      rw [hasCompactSupport_iff_eventuallyEq]⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · show IsSmoothCovered F ζ hζ U (f.val + g.val)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U (f.val + g.val)).val (x, c))
          = fun x => (J F ζ hζ U f.val).val (x, c) + (J F ζ hζ U g.val).val (x, c) := by
        funext x; simp [map_add]
      rw [h]; exact (hf.1 c).add (hg.1 c)
    · simpa using hf.2.add hg.2
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_⟩
    · show IsSmoothCovered F ζ hζ U (a • f.val)
      intro c
      have h : (fun x : SymmetricSpace F => (J F ζ hζ U (a • f.val)).val (x, c))
          = fun x => a • (J F ζ hζ U f.val).val (x, c) := by
        funext x; simp [map_smul]
      rw [h]; exact (hf.1 c).const_smul a
    · have heq : (a • f).val.val = fun x => a * f.val.val x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rw [heq]; exact hf.2.comp_left (g := fun z => a * z) (by simp)

def smoothCompactScalarEmbedding : SmoothCompactL2Scalars F ζ hζ U R →ₗ[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U :=
  (scalarEmbedding F ζ hζ U R P H).comp (SmoothCompactL2Scalars F ζ hζ U R).subtype

theorem smoothCompactScalarEmbedding_injective :
    Function.Injective (smoothCompactScalarEmbedding F ζ hζ U R P H) := by
  intro f g hfg
  have hcont : ∀ h : SmoothCompactL2Scalars F ζ hζ U R, Continuous h.val.val.val := by
    intro h
    have hs := (smooth_iff F ζ hζ U R P H h.val.val).mp h.property.1
    have hc := (continuous_iff F ζ hζ U R P H (S F ζ hζ U R P H h.val.val)).mp
      (fun i => (hs i).continuous)
    simpa only [scalarRepresentative_eq_symm, LinearEquiv.symm_apply_apply] using hc
  let f₀ : ContinuousL2Scalars F ζ hζ U R := ⟨f.val, hcont f⟩
  let g₀ : ContinuousL2Scalars F ζ hζ U R := ⟨g.val, hcont g⟩
  have heq : continuousScalarEmbedding F ζ hζ U R P H f₀ =
      continuousScalarEmbedding F ζ hζ U R P H g₀ := hfg
  have hval := congrArg (fun h : ContinuousL2Scalars F ζ hζ U R => h.val)
    (continuousScalarEmbedding_injective F ζ hζ U R P H heq)
  exact Subtype.ext hval

def SmoothCompactL2Sections : Submodule ℂ (BorelL2Sections F ζ hζ U R P H) where
  carrier := {s | IsSmoothSections F ζ hζ U R P H s.val ∧
    HasCompactSupport (sectionNorm F ζ hζ U R P H s.val)}
  zero_mem' := ⟨by
      show IsSmoothSections F ζ hζ U R P H (0 : Sections F ζ hζ U R P H)
      intro i
      have h : ((0 : Sections F ζ hζ U R P H) i).val = fun _ => (0 : ℂ) := by
        funext x; simp
      rw [h]; exact contDiff_const,
    by
      show HasCompactSupport (sectionNorm F ζ hζ U R P H (0 : Sections F ζ hζ U R P H))
      rw [sectionNorm_zero, hasCompactSupport_iff_eventuallyEq]⟩
  add_mem' := by
    intro s t hs ht
    refine ⟨?_, ?_⟩
    · show IsSmoothSections F ζ hζ U R P H (s.val + t.val)
      intro i
      have h : ((s.val + t.val) i).val = fun x => (s.val i).val x + (t.val i).val x := by
        funext x; simp
      rw [h]; exact (hs.1 i).add (ht.1 i)
    · refine (hs.2.add ht.2).mono (fun b hb => ?_)
      intro h0
      exact hb (le_antisymm (h0 ▸ sectionNorm_add_le F ζ hζ U R P H s.val t.val b)
        (sectionNorm_nonneg F ζ hζ U R P H (s.val + t.val) b))
  smul_mem' := by
    intro c s hs
    refine ⟨?_, ?_⟩
    · show IsSmoothSections F ζ hζ U R P H (c • s.val)
      intro i
      have h : ((c • s.val) i).val = fun x => c • (s.val i).val x := by
        funext x; simp
      rw [h]; exact (hs.1 i).const_smul c
    · change HasCompactSupport (sectionNorm F ζ hζ U R P H (c • s.val))
      have heq : sectionNorm F ζ hζ U R P H (c • s.val) =
          (fun _ => ‖c‖) * sectionNorm F ζ hζ U R P H s.val := by
        rw [sectionNorm_smul]
        funext b; rfl
      rw [heq]
      exact HasCompactSupport.mul_left (f := fun _ => ‖c‖)
        (f' := sectionNorm F ζ hζ U R P H s.val) hs.2

def smoothCompactSectionEmbedding : SmoothCompactL2Sections F ζ hζ U R P H →ₗ[ℂ]
    L2Line F ζ hζ U R P H :=
  (mk F ζ hζ U R P H).comp (SmoothCompactL2Sections F ζ hζ U R P H).subtype

theorem smoothCompactSectionEmbedding_injective :
    Function.Injective (smoothCompactSectionEmbedding F ζ hζ U R P H) := by
  intro s t hst
  let s₀ : ContinuousL2Sections F ζ hζ U R P H :=
    ⟨s.val, fun i => (s.property.1 i).continuous⟩
  let t₀ : ContinuousL2Sections F ζ hζ U R P H :=
    ⟨t.val, fun i => (t.property.1 i).continuous⟩
  have heq : continuousSectionEmbedding F ζ hζ U R P H s₀ =
      continuousSectionEmbedding F ζ hζ U R P H t₀ := hst
  have hval := congrArg Subtype.val
    (continuousSectionEmbedding_injective F ζ hζ U R P H heq)
  exact Subtype.ext hval

theorem squaredNorm_measurable (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val) :
    Measurable (squaredNorm F ζ hζ U R P H s) := by
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s)
      ((borel_iff F ζ hζ U R P H s).mp hs)).borel
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  change Measurable (fun b => ENNReal.ofReal
    (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H s)) b ^ 2)) at hn
  rw [heq] at hn
  exact hn

theorem squaredNorm_pullback (s : Sections F ζ hζ U R P H)
    (v : CoveredSpherical F ζ hζ U) :
    squaredNorm F ζ hζ U R P H s (q F ζ hζ U v) =
      ENNReal.ofReal (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ 2) := by
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  unfold squaredNorm
  rw [← heq, sectionNorm_pullback, heq]

theorem base_restriction (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
    Measurable (fun b : E => squaredNorm F ζ hζ U R P H s b.val) ∧
    Measurable (fun v : (q F ζ hζ U) ⁻¹' E =>
      (scalarRepresentative F ζ hζ U R P H s).val v.val) ∧
    (∫⁻ b in E, squaredNorm F ζ hζ U R P H s b ∂sphericalMeasure F ζ hζ R P U) =
      ∫⁻ v in (q F ζ hζ U) ⁻¹' E,
        ENNReal.ofReal (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ 2)
          ∂coveredMeasure F ζ hζ R U := by
  have hf := (borel_iff F ζ hζ U R P H s).mp hs
  refine ⟨(squaredNorm_measurable F ζ hζ U R P H s hs).comp measurable_subtype_coe,
    hf.comp measurable_subtype_coe, ?_⟩
  have hn := (DedekindZetaZeroFree.kp_cont_sector_fixed_line_norm_integrals
    F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) hf).restricted_pushforward E hE
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  simpa only [KPContSectorFixedLineNormIntegrals.lineNorm, heq, squaredNorm] using hn.symm

theorem lift_restriction (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val)
    (i : Fin (H.atlas U).componentCount) (V : Set (SymmetricSpace F))
    (hV : MeasurableSet V) :
    Measurable (fun x : V => (s i).val x.val) ∧
    (fun x : V => (J F ζ hζ U (scalarRepresentative F ζ hζ U R P H s)).val
      (x.val, (H.atlas U).representative i)) = (fun x : V => (s i).val x.val) ∧
    (∀ x : V, squaredNorm F ζ hζ U R P H s
      ((H.atlas U).components ⟨i, Quotient.mk _ x.val⟩) =
        ENNReal.ofReal (‖(s i).val x.val‖ ^ 2)) := by
  refine ⟨(hs i).comp measurable_subtype_coe, ?_, ?_⟩
  · funext x
    have heq := congrArg (fun t : Sections F ζ hζ U R P H => (t i).val x.val)
      ((S F ζ hζ U R P H).apply_symm_apply s)
    rw [S_apply, ← J_apply] at heq
    exact heq
  · intro x
    unfold squaredNorm
    rw [sectionNorm_component]

instance instMeasurableSpaceCoveredChartDomain
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    MeasurableSpace (KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O) :=
  borel _

instance instBorelSpaceCoveredChartDomain
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    BorelSpace (KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O) :=
  ⟨rfl⟩

theorem orbifold_restriction (s : Sections F ζ hζ U R P H)
    (hs : ∀ i, Measurable (s i).val)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x) :
    Measurable (fun v : KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O =>
      (scalarRepresentative F ζ hζ U R P H s).val
        (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O v).val) ∧
    (∀ (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) (y : O.neighborhood),
      (scalarRepresentative F ζ hζ U R P H s).val
        (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
          (Quotient.mk _ (m,y))).val =
        (phaseCoefficient F ζ hζ U R P H s i m y.val : ℂ)) ∧
    (∀ (ε : rootsOfUnity 3 F) (y : O.neighborhood),
      squaredNorm F ζ hζ U R P H s
        (q F ζ hζ U (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
          (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,y))).val) =
        ENNReal.ofReal (‖(s i).val y.val‖ ^ 2)) := by
  have hf := (borel_iff F ζ hζ U R P H s).mp hs
  have heq : S F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) = s :=
    (S F ζ hζ U R P H).apply_symm_apply s
  refine ⟨hf.comp (measurable_subtype_coe.comp
    (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O).measurable), ?_, ?_⟩
  · intro m y
    simpa only [heq] using orbifold_restriction_commutes F ζ hζ U R P H
      (scalarRepresentative F ζ hζ U R P H s) i x O m y
  · intro ε y
    rw [squaredNorm_pullback,
      KPContSectorPhaseComponentCharts.coveredChart_mk, scalarRepresentative_mk]
    have hc : ((H.atlas U).scalar_realization.symm s).val
        (y.val, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i) =
        (chi F ζ hζ ε : ℂ) * (s i).val y.val := by
      simpa only [scalarRepresentative_mk, heq] using phase_lift_formula
        F ζ hζ U R P H (scalarRepresentative F ζ hζ U R P H s) i ε y.val
    rw [hc, norm_mul, chi_coe, chi_norm, one_mul]

theorem restricted_integral_congr (s t : BorelL2Sections F ζ hζ U R P H)
    (hst : mk F ζ hζ U R P H s = mk F ζ hζ U R P H t)
    (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
    (∫⁻ b in E, squaredNorm F ζ hζ U R P H s.val b ∂sphericalMeasure F ζ hζ R P U) =
      ∫⁻ b in E, squaredNorm F ζ hζ U R P H t.val b ∂sphericalMeasure F ζ hζ R P U := by
  rw [(base_restriction F ζ hζ U R P H s.val s.property.1 E hE).2.2,
    (base_restriction F ζ hζ U R P H t.val t.property.1 E hE).2.2]
  have hae := (null_iff_scalar_ae_eq F ζ hζ U R P H s t).mp
    ((mk_eq_mk_iff F ζ hζ U R P H s t).mp hst)
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hae] with v hv
  rw [hv]

theorem subsingleton_of_sector_eq_bot
    (hzero : KPContSectorClosedLpSubspace.H F ζ hζ R U = ⊥) :
    Subsingleton (L2Line F ζ hζ U R P H) := by
  have hs : Subsingleton (KPContSectorClosedLpSubspace.H F ζ hζ R U) := by
    rw [hzero]
    infer_instance
  exact ⟨fun x y => (lineToSector F ζ hζ U R P H).injective (hs.elim _ _)⟩

structure RealizationIdentities : Prop where
  borel : ∀ s : Sections F ζ hζ U R P H,
    (∀ i, Measurable (s i).val) ↔ Measurable (scalarRepresentative F ζ hζ U R P H s).val
  reconstruction : ∀ (s : Sections F ζ hζ U R P H)
      (x : SymmetricSpace F) (c : FiniteCover F ζ hζ),
    (scalarRepresentative F ζ hζ U R P H s).val
      (Quotient.mk (coveredRelation F ζ hζ U) (x,c)) =
        ((H.atlas U).scalar_realization.symm s).val (x,c)
  null_relation : ∀ s t : BorelL2Sections F ζ hζ U R P H,
    mk F ζ hζ U R P H s = mk F ζ hζ U R P H t ↔
      squaredNorm F ζ hζ U R P H (s.val - t.val) =ᵐ[sphericalMeasure F ζ hζ R P U] 0
  norm_formula : ∀ s : BorelL2Sections F ζ hζ U R P H,
    ‖mk F ζ hζ U R P H s‖ ^ 2 = (normIntegral F ζ hζ U R P H s.val).toReal
  extended_norm_formula : ∀ s : BorelL2Sections F ζ hζ U R P H,
    ENNReal.ofReal (‖mk F ζ hζ U R P H s‖ ^ 2) = normIntegral F ζ hζ U R P H s.val
  forward : ∀ (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
      (f : BorelL2Scalars F ζ hζ U R),
    f.property.2.toLp f.val.val = (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) →
      sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H (borelS F ζ hζ U R P H f)
  inverse : ∀ s : BorelL2Sections F ζ hζ U R P H,
    ((sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H s) :
      KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
        (representative_memLp F ζ hζ U R P H s).toLp
          (scalarRepresentative F ζ hζ U R P H s.val).val
  continuous_scalars : Function.Injective (continuousScalarEmbedding F ζ hζ U R P H)
  continuous_sections : Function.Injective (continuousSectionEmbedding F ζ hζ U R P H)
  smooth_compact_scalars : Function.Injective (smoothCompactScalarEmbedding F ζ hζ U R P H)
  smooth_compact_sections : Function.Injective (smoothCompactSectionEmbedding F ζ hζ U R P H)
  restricted_norm : ∀ (s : Sections F ζ hζ U R P H), (∀ i, Measurable (s i).val) →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
      (∫⁻ b in E, squaredNorm F ζ hζ U R P H s b ∂sphericalMeasure F ζ hζ R P U) =
        ∫⁻ v in (q F ζ hζ U) ⁻¹' E,
          ENNReal.ofReal (‖(scalarRepresentative F ζ hζ U R P H s).val v‖ ^ 2)
            ∂coveredMeasure F ζ hζ R U
  restricted_borel : ∀ (s : Sections F ζ hζ U R P H), (∀ i, Measurable (s i).val) →
    ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
      Measurable (fun b : E => squaredNorm F ζ hζ U R P H s b.val) ∧
      Measurable (fun v : (q F ζ hζ U) ⁻¹' E =>
        (scalarRepresentative F ζ hζ U R P H s).val v.val)
  chart_borel : ∀ (s : Sections F ζ hζ U R P H), (∀ i, Measurable (s i).val) →
    ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x),
      Measurable (fun v : KPContSectorPhaseComponentCharts.CoveredChartDomain F ζ hζ U R P H i x O =>
        (scalarRepresentative F ζ hζ U R P H s).val
          (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O v).val)
  chart_norm : ∀ (s : Sections F ζ hζ U R P H)
      (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (ε : rootsOfUnity 3 F) (y : O.neighborhood),
    squaredNorm F ζ hζ U R P H s
      (q F ζ hζ U (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
        (Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,y))).val) =
        ENNReal.ofReal (‖(s i).val y.val‖ ^ 2)

end DedekindZetaZeroFree.KPContSectorLineL2Isometry

namespace DedekindZetaZeroFree

theorem kp_cont_sector_line_l2_isometry
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContSectorLineL2Isometry.RealizationIdentities F ζ hζ U R P H := by
  exact {
    borel := KPContSectorLineL2Isometry.borel_iff F ζ hζ U R P H
    reconstruction := KPContSectorLineL2Isometry.scalarRepresentative_mk F ζ hζ U R P H
    null_relation := KPContSectorLineL2Isometry.mk_eq_mk_iff F ζ hζ U R P H
    norm_formula := KPContSectorLineL2Isometry.norm_sq F ζ hζ U R P H
    extended_norm_formula := KPContSectorLineL2Isometry.ofReal_norm_sq F ζ hζ U R P H
    forward := KPContSectorLineL2Isometry.sectorLineIsometry_representative F ζ hζ U R P H
    inverse := KPContSectorLineL2Isometry.sectorLineIsometry_symm_mk F ζ hζ U R P H
    continuous_scalars := KPContSectorLineL2Isometry.continuousScalarEmbedding_injective F ζ hζ U R P H
    continuous_sections := KPContSectorLineL2Isometry.continuousSectionEmbedding_injective F ζ hζ U R P H
    smooth_compact_scalars := KPContSectorLineL2Isometry.smoothCompactScalarEmbedding_injective F ζ hζ U R P H
    smooth_compact_sections := KPContSectorLineL2Isometry.smoothCompactSectionEmbedding_injective F ζ hζ U R P H
    restricted_norm := fun s hs E hE =>
      (KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).2.2
    restricted_borel := fun s hs E hE =>
      ⟨(KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).1,
        (KPContSectorLineL2Isometry.base_restriction F ζ hζ U R P H s hs E hE).2.1⟩
    chart_borel := fun s hs i x O =>
      (KPContSectorLineL2Isometry.orbifold_restriction F ζ hζ U R P H s hs i x O).1
    chart_norm := by
      intro s i x O ε y
      rw [KPContSectorLineL2Isometry.squaredNorm_pullback,
        KPContSectorPhaseComponentCharts.coveredChart_mk]
      have hp := KPContSectorSmoothFramesSupport.phase_lift_formula F ζ hζ U R P H
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s) i ε y.val
      have heq : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H
          (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ U R P H s) = s :=
        (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H).apply_symm_apply s
      rw [hp, heq, norm_mul, KPContSectorCoveredQuotientVocabulary.chi_coe,
        KPContSectorCoveredQuotientVocabulary.chi_norm, one_mul]
  }

end DedekindZetaZeroFree

end
