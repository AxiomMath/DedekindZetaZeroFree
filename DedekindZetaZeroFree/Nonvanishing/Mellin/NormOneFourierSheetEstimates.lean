module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.NormSheetLogarithmicDerivativeBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.VerticalStripRapidDecay

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace ProbeSheet
variable {F : Type} [Field F] [NumberField F]

def localUnits (A : SArithmeticData F) : A.G ≃* (SLocalProduct F A.Sf)ˣ :=
  ((MulEquiv.piUnits).symm.prodCongr (MulEquiv.piUnits).symm).trans
    (MulEquiv.prodUnits).symm

def ell (A : SArithmeticData F) (T : ℝ) : (SLocalProduct F A.Sf)ˣ :=
  if hT : 0 < T then localUnits A (A.radialSection T hT) else 1

def complexNormFlow (A : SArithmeticData F) (w : InfinitePlace F)
    (u : ℝ) (x : SLocalProduct F A.Sf) : SLocalProduct F A.Sf :=
  (Function.update x.1 w
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
      (Real.exp (u / 2) : ℂ) * x.1 w), x.2)

def logDerivative (A : SArithmeticData F) (w : InfinitePlace F) (k : ℕ)
    (f : SLocalProduct F A.Sf → ℂ) (x : SLocalProduct F A.Sf) : ℂ :=
  iteratedDeriv k (fun u : ℝ => f (complexNormFlow A w u x)) 0

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

def radialMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fun T => ENNReal.ofReal (1 / T))

def sheetPoint (A : SArithmeticData F) (T : ℝ) (t : A.G1) :
    (SLocalProduct F A.Sf)ˣ := localUnits A t.val * ell A T

def HaarDisintegration (A : SArithmeticData F)
    (ν : Measure (SLocalProduct F A.Sf)ˣ) (dt : Measure A.G1) : Prop :=
  ν = Measure.map (fun p : ℝ × A.G1 => sheetPoint A p.1 p.2)
    (radialMeasure.prod dt)

def envelope (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F A.Sf)) (dt : Measure A.G1)
    (W0 : SLocalProduct F A.Sf → ℂ) (T : ℝ) : ℂ :=
  ∫ t, ProbeWeight.fourier F A.Sf e μ W0 (sheetPoint A T t).val ∂dt

def MellinEstimates (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F A.Sf)) (ν : Measure (SLocalProduct F A.Sf)ˣ)
    (dt : Measure A.G1) (w : InfinitePlace F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight) : Prop :=
  let W0hat := ProbeWeight.fourier F A.Sf e μ W0
  let V0 := envelope A e μ dt W0
  let M := ProbeWeight.fourierMellin F A.Sf e μ ν W0
  (∀ T : ℝ, 0 < T → Integrable (fun t => W0hat (sheetPoint A T t).val) dt) ∧
  (∀ (σ : ℝ) (k : ℕ), 0 < σ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 0 < T →
      Integrable (fun t => logDerivative A w k W0hat (sheetPoint A T t).val) dt ∧
      (∫ t, ‖logDerivative A w k W0hat (sheetPoint A T t).val‖ ∂dt) ≤
        C * T ^ (-σ)) ∧
  (∀ z : ℂ, 0 < z.re →
    Integrable (fun y : (SLocalProduct F A.Sf)ˣ =>
      W0hat y.val * (ProbeWeight.modulus F A.Sf y : ℂ) ^ z) ν ∧
    IntegrableOn (fun T : ℝ => V0 T * (T : ℂ) ^ z / (T : ℂ)) (Set.Ioi 0) ∧
    (∫ T in Set.Ioi (0 : ℝ), V0 T * (T : ℂ) ^ z / (T : ℂ)) = M z) ∧
  DifferentiableOn ℂ M {z | 0 < z.re} ∧
  (∀ (σ0 σ1 B : ℝ), 0 < σ0 → σ0 ≤ σ1 → 0 ≤ B →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σ0 σ1, ∀ τ : ℝ,
      ‖M ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B)) ∧
  Differentiable ℂ (probeRealWeightMellin W1) ∧
  (∀ (σ0 σ1 B : ℝ), σ0 ≤ σ1 → 0 ≤ B →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σ0 σ1, ∀ τ : ℝ,
      ‖probeRealWeightMellin W1 ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        C * (1 + |τ|) ^ (-B)) ∧
  (∀ (c T : ℝ), 0 < c → 0 < T →
    Integrable (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) ∧
    V0 T = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ : ℝ, M ((c : ℂ) + (τ : ℂ) * Complex.I) *
        (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I))

open MeasureTheory.Measure
variable (A : SArithmeticData F)
local instance : MeasurableSpace A.G := borel _
local instance : BorelSpace A.G := ⟨rfl⟩

lemma norm_pos (x : A.G) : 0 < A.norm x := by
  unfold SArithmeticData.norm
  exact mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (x.1 w).ne_zero) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (x.2 v).ne_zero)
lemma norm_mul (x y : A.G) : A.norm (x * y) = A.norm x * A.norm y := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, _root_.norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring
lemma norm_div (x y : A.G) : A.norm (x / y) = A.norm x / A.norm y := by
  simp [SArithmeticData.norm, norm_div, div_pow, Finset.prod_div_distrib, div_mul_div_comm]
lemma continuous_norm : Continuous A.norm := by
  unfold SArithmeticData.norm
  fun_prop
lemma locallyCompact_G : LocallyCompactSpace A.G := by
  letI (v : A.Sf) : LocallyCompactSpace (v.val.adicCompletion F) :=
    (PoissonS.finite_components_locallyCompact F A.Sf).1 v
  infer_instance
lemma secondCountable_G : SecondCountableTopology A.G := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  infer_instance
lemma locallyCompact_G1 : LocallyCompactSpace A.G1 := by
  letI := locallyCompact_G A
  exact IsClosed.locallyCompactSpace (isClosed_singleton.preimage (continuous_norm A))
lemma secondCountable_G1 : SecondCountableTopology A.G1 := by
  letI := secondCountable_G A
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
lemma continuous_localUnits : Continuous (localUnits A) := by
  change Continuous (Homeomorph.prodUnits.symm ∘
    (ContinuousMulEquiv.piUnits.symm.toHomeomorph.prodCongr
      ContinuousMulEquiv.piUnits.symm.toHomeomorph))
  fun_prop
lemma continuous_localUnits_symm : Continuous (localUnits A).symm := by
  change Continuous ((ContinuousMulEquiv.piUnits.toHomeomorph.prodCongr
    ContinuousMulEquiv.piUnits.toHomeomorph) ∘ Homeomorph.prodUnits)
  fun_prop

def normOnePart (x : A.G) : A.G1 :=
  ⟨x / A.radialSection (A.norm x) (norm_pos A x), by
    change A.norm _ = 1
    rw [ProbeSheet.norm_div, A.norm_radialSection, div_self (norm_pos A x).ne']⟩
lemma continuous_normOnePart : Continuous (normOnePart A) := by
  apply Continuous.subtype_mk
  change Continuous (fun x : A.G => x / A.radialSection (A.norm x) _)
  simp only [div_eq_mul_inv]
  have hr : Continuous (fun x : A.G => A.radialSection (A.norm x) (norm_pos A x)) :=
    A.continuous_radialSection.comp
      ((continuous_norm A).subtype_mk fun x => norm_pos A x)
  fun_prop

def logSplit : A.G ≃ₜ Multiplicative ℝ × A.G1 where
  toFun x := (Multiplicative.ofAdd (Real.log (A.norm x)), normOnePart A x)
  invFun p := p.2.val * A.radialSection (Real.exp p.1.toAdd) (Real.exp_pos _)
  left_inv x := by
    change x / A.radialSection (A.norm x) _ * A.radialSection (Real.exp (Real.log (A.norm x))) _ = x
    simp [Real.exp_log (norm_pos A x)]
  right_inv p := by
    have hn : A.norm (p.2.val * A.radialSection (Real.exp p.1.toAdd) (Real.exp_pos _)) =
        Real.exp p.1.toAdd := by
      rw [norm_mul, show A.norm p.2.val = 1 from p.2.property, A.norm_radialSection, one_mul]
    apply Prod.ext
    · change Multiplicative.ofAdd (Real.log _) = _
      rw [hn, Real.log_exp]
      rfl
    · apply Subtype.ext
      change (_ * _) / _ = _
      simp only [hn, mul_div_cancel_right]
  continuous_toFun :=
    (continuous_ofAdd.comp ((continuous_norm A).log
      (fun x => (norm_pos A x).ne'))).prodMk (continuous_normOnePart A)
  continuous_invFun := continuous_subtype_val.comp continuous_snd |>.mul
    (A.continuous_radialSection.comp
      ((Real.continuous_exp.comp (continuous_toAdd.comp continuous_fst)).subtype_mk fun _ => Real.exp_pos _))

lemma logSplit_mul (x y : A.G) : logSplit A (x * y) = logSplit A x * logSplit A y := by
  apply Prod.ext
  · change Multiplicative.ofAdd (Real.log (A.norm (x * y))) =
      Multiplicative.ofAdd (Real.log (A.norm x) + Real.log (A.norm y))
    rw [ProbeSheet.norm_mul, Real.log_mul (norm_pos A x).ne' (norm_pos A y).ne']
  · apply Subtype.ext
    change x * y / A.radialSection (A.norm (x * y)) _ =
      (x / A.radialSection (A.norm x) _) * (y / A.radialSection (A.norm y) _)
    have hs : A.radialSection (A.norm (x * y)) (norm_pos A (x * y)) =
        A.radialSection (A.norm x) (norm_pos A x) * A.radialSection (A.norm y) (norm_pos A y) := by
      simp only [ProbeSheet.norm_mul]
      exact A.radialSection_mul _ _ (norm_pos A x) (norm_pos A y)
    rw [hs]
    exact (div_mul_div_comm x _ y _).symm

def logSplitMul : A.G ≃ₜ* Multiplicative ℝ × A.G1 where
  __ := logSplit A
  map_mul' := logSplit_mul A

lemma map_log_radial : Measure.map Real.log radialMeasure = volume := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := Set.Ioi 0) (f := Real.log)
    (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ x⁻¹)
    measurableSet_Ioi.nullMeasurableSet
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt hx)).hasFDerivAt.hasFDerivWithinAt)
    Real.strictMonoOn_log.injOn
  have him : Real.log '' Set.Ioi 0 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    exact ⟨Real.exp u, Real.exp_pos u, Real.log_exp u⟩
  have hd (x : ℝ) : (ContinuousLinearMap.toSpanSingleton ℝ x⁻¹).det = x⁻¹ := by
    exact ContinuousLinearMap.det_toSpanSingleton _
  simp only [hd, him, Measure.restrict_univ] at h
  convert h using 2
  unfold radialMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp [one_div, abs_of_pos (show 0 < x from hx)]
lemma map_exp_volume : Measure.map Real.exp volume = radialMeasure := by
  rw [← map_log_radial, Measure.map_map Real.continuous_exp.measurable Real.measurable_log]
  calc
    Measure.map (Real.exp ∘ Real.log) radialMeasure = Measure.map id radialMeasure := by
      apply Measure.map_congr
      apply (withDensity_absolutelyContinuous _ _).ae_le
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.exp_log hx
    _ = radialMeasure := Measure.map_id

local instance : MeasurableSpace (Multiplicative ℝ) := borel _
local instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩
def mulVolume : Measure (Multiplicative ℝ) := Measure.map Multiplicative.ofAdd volume
instance : mulVolume.IsHaarMeasure := by
  let e : ℝ ≃ₜ Multiplicative ℝ := ⟨Multiplicative.ofAdd, continuous_ofAdd, continuous_toAdd⟩
  have hfin : IsFiniteMeasureOnCompacts mulVolume :=
    IsFiniteMeasureOnCompacts.map volume e
  have hopen : IsOpenPosMeasure mulVolume := by
    exact continuous_ofAdd.isOpenPosMeasure_map Multiplicative.ofAdd.surjective
  refine { hfin, hopen with
    map_mul_left_eq_self := ?_ }
  intro x
  unfold mulVolume
  rw [Measure.map_map (by fun_prop) continuous_ofAdd.measurable]
  change Measure.map (Multiplicative.ofAdd ∘ (x.toAdd + ·)) volume = _
  rw [← Measure.map_map continuous_ofAdd.measurable (by fun_prop), map_add_left_eq_self]

def localUnitsContinuous : A.G ≃ₜ* (SLocalProduct F A.Sf)ˣ where
  __ := localUnits A
  continuous_toFun := continuous_localUnits A
  continuous_invFun := continuous_localUnits_symm A

def unitLogSplit : (SLocalProduct F A.Sf)ˣ ≃ₜ* Multiplicative ℝ × A.G1 :=
  (localUnitsContinuous A).symm.trans (logSplitMul A)

lemma unitLogSplit_symm_apply (p : Multiplicative ℝ × A.G1) :
    (unitLogSplit A).symm p = sheetPoint A (Real.exp p.1.toAdd) p.2 := by
  change localUnits A (p.2.val * A.radialSection (Real.exp p.1.toAdd) _) = _
  rw [map_mul]
  simp [sheetPoint, ell, Real.exp_pos]

lemma units_val_isEmbedding :
    Topology.IsEmbedding (Units.val : (SLocalProduct F A.Sf)ˣ → SLocalProduct F A.Sf) := by
  have hc : Topology.IsEmbedding (fun x : A.G =>
      ((fun w => (x.1 w).val), (fun v => (x.2 v).val))) :=
    (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀)).prodMap
      (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀))
  exact hc.comp (localUnitsContinuous A).symm.toHomeomorph.isEmbedding

local instance unitsBorelSpace : BorelSpace (SLocalProduct F A.Sf)ˣ := by
  constructor
  change (borel (SLocalProduct F A.Sf)).comap Units.val = borel _
  rw [← borel_comap, ← (units_val_isEmbedding A).isInducing.eq_induced]

lemma measurable_sheetPoint : Measurable (fun p : ℝ × A.G1 => sheetPoint A p.1 p.2) := by
  have he : Measurable (ell A) := by
    unfold ell
    exact Measurable.dite
      (((continuous_localUnits A).comp A.continuous_radialSection).measurable)
      measurable_const measurableSet_Ioi
  have hm : MeasurableMul₂ (SLocalProduct F A.Sf)ˣ := by
    letI := secondCountable_G A
    letI : SecondCountableTopology (SLocalProduct F A.Sf)ˣ :=
      (localUnitsContinuous A).symm.toHomeomorph.secondCountableTopology
    infer_instance
  letI := hm
  unfold sheetPoint
  exact ((continuous_localUnits A).measurable.comp
    (continuous_subtype_val.comp continuous_snd).measurable).mul (he.comp measurable_fst)

lemma sheet_map_log_product (dt : Measure A.G1) [SFinite dt] :
    Measure.map (fun p : ℝ × A.G1 => sheetPoint A p.1 p.2)
      (radialMeasure.prod dt) =
    Measure.map (unitLogSplit A).symm (mulVolume.prod dt) := by
  have hm : Measure.map (fun p : ℝ × A.G1 =>
      (Multiplicative.ofAdd p.1, p.2)) (volume.prod dt) = mulVolume.prod dt := by
    change Measure.map (Prod.map Multiplicative.ofAdd id) (volume.prod dt) = _
    simpa only [Measure.map_id, mulVolume] using
      (Measure.map_prod_map (volume : Measure ℝ) dt
        continuous_ofAdd.measurable measurable_id).symm
  have hr : Measure.map (fun p : ℝ × A.G1 => (Real.exp p.1, p.2))
      (volume.prod dt) = radialMeasure.prod dt := by
    change Measure.map (Prod.map Real.exp id) (volume.prod dt) = _
    simpa only [map_exp_volume, Measure.map_id] using
      (Measure.map_prod_map (volume : Measure ℝ) dt
        Real.continuous_exp.measurable measurable_id).symm
  have hup : Measurable (fun p : ℝ × A.G1 => (Multiplicative.ofAdd p.1, p.2)) :=
    (continuous_ofAdd.comp continuous_fst |>.prodMk continuous_snd).measurable
  have hus : Measurable (unitLogSplit A).symm :=
    (unitLogSplit A).symm.continuous.measurable
  rw [← hr, ← hm,
    Measure.map_map (measurable_sheetPoint A) (by fun_prop),
    Measure.map_map hus hup]
  congr 1
  funext p
  exact (unitLogSplit_symm_apply A (Multiplicative.ofAdd p.1, p.2)).symm

lemma sheet_map_isHaar (dt : Measure A.G1) [dt.IsHaarMeasure] :
    (Measure.map (fun p : ℝ × A.G1 => sheetPoint A p.1 p.2)
      (radialMeasure.prod dt)).IsHaarMeasure := by
  letI := locallyCompact_G1 A
  letI := secondCountable_G1 A
  rw [sheet_map_log_product A dt]
  letI : (mulVolume.prod dt).IsHaarMeasure := inferInstance
  exact (unitLogSplit A).symm.isHaarMeasure_map (mulVolume.prod dt)

lemma normalized_haar_exists
    (ν : Measure (SLocalProduct F A.Sf)ˣ) [ν.IsHaarMeasure] :
    ∃ dt : Measure A.G1, dt.IsHaarMeasure ∧ HaarDisintegration A ν dt := by
  letI := locallyCompact_G A
  letI := secondCountable_G A
  letI := locallyCompact_G1 A
  letI := secondCountable_G1 A
  letI : LocallyCompactSpace (SLocalProduct F A.Sf)ˣ :=
    (localUnitsContinuous A).symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  letI : SecondCountableTopology (SLocalProduct F A.Sf)ˣ :=
    (localUnitsContinuous A).symm.toHomeomorph.secondCountableTopology
  let dt₀ : Measure A.G1 := Measure.haar
  let ν₀ : Measure (SLocalProduct F A.Sf)ˣ :=
    Measure.map (fun p : ℝ × A.G1 => sheetPoint A p.1 p.2) (radialMeasure.prod dt₀)
  letI : dt₀.IsHaarMeasure := by dsimp [dt₀]; infer_instance
  letI : ν₀.IsHaarMeasure := sheet_map_isHaar A dt₀
  let c : NNReal := ν.haarScalarFactor ν₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure ν ν₀).ne'
  refine ⟨c • dt₀, Measure.IsHaarMeasure.nnreal_smul dt₀ hc, ?_⟩
  unfold HaarDisintegration
  rw [Measure.prod_smul_right, Measure.map_smul c (measurable_sheetPoint A).aemeasurable]
  exact Measure.isMulLeftInvariant_eq_smul ν ν₀

lemma modulus_localUnits (A : SArithmeticData F) (x : A.G) :
    ProbeWeight.modulus F A.Sf (localUnits A x) = A.norm x := by
  rfl
lemma modulus_sheetPoint (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) (t : A.G1) :
    ProbeWeight.modulus F A.Sf (sheetPoint A T t) = T := by
  unfold sheetPoint ell
  rw [dif_pos hT, ← map_mul, modulus_localUnits, ProbeSheet.norm_mul,
    show A.norm t.val = 1 from t.property, A.norm_radialSection, one_mul]

lemma radial_integrable_iff (f : ℝ → ℂ) :
    Integrable f radialMeasure ↔ IntegrableOn (fun T => f T / (T : ℂ)) (Set.Ioi 0) := by
  unfold radialMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  have hp : 0 < T := hT
  simp only [one_div, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), Complex.ofReal_inv, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, smul_eq_mul]
  ring
lemma radial_integral (f : ℝ → ℂ) :
    (∫ T, f T ∂radialMeasure) = ∫ T in Set.Ioi (0 : ℝ), f T / (T : ℂ) := by
  unfold radialMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  have hp : 0 < T := hT
  simp only [one_div, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), Complex.ofReal_inv, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, smul_eq_mul]
  ring

lemma sheet_mellin_of_integrable (A : SArithmeticData F)
    (ν : Measure (SLocalProduct F A.Sf)ˣ) (dt : Measure A.G1) [dt.IsHaarMeasure]
    (hdis : HaarDisintegration A ν dt) (f : (SLocalProduct F A.Sf)ˣ → ℂ) (z : ℂ)
    (hi : Integrable (fun y => f y * (ProbeWeight.modulus F A.Sf y : ℂ) ^ z) ν) :
    IntegrableOn (fun T : ℝ => (∫ t, f (sheetPoint A T t) ∂dt) * (T : ℂ) ^ z / (T : ℂ))
      (Set.Ioi 0) ∧
    (∫ T in Set.Ioi (0 : ℝ), (∫ t, f (sheetPoint A T t) ∂dt) * (T : ℂ) ^ z / (T : ℂ)) =
      ∫ y, f y * (ProbeWeight.modulus F A.Sf y : ℂ) ^ z ∂ν := by
  letI := locallyCompact_G1 A
  letI := secondCountable_G1 A
  have hs : SFinite radialMeasure := by unfold radialMeasure; infer_instance
  letI := hs
  let g : ℝ × A.G1 → ℂ := fun p => f (sheetPoint A p.1 p.2) *
    (ProbeWeight.modulus F A.Sf (sheetPoint A p.1 p.2) : ℂ) ^ z
  have hig : Integrable g (radialMeasure.prod dt) := by
    rw [hdis] at hi
    exact hi.comp_aemeasurable (measurable_sheetPoint A).aemeasurable
  have hae : (fun T : ℝ => ∫ t, g (T, t) ∂dt) =ᶠ[ae radialMeasure]
      (fun T : ℝ => (∫ t, f (sheetPoint A T t) ∂dt) * (T : ℂ) ^ z) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    dsimp [g]
    simp only [modulus_sheetPoint A T hT, integral_mul_const]
  refine ⟨(radial_integrable_iff _).mp (hig.integral_prod_left.congr hae), ?_⟩
  rw [← radial_integral, ← integral_congr_ae hae, ← integral_prod g hig]
  rw [hdis] at hi ⊢
  exact (integral_map (measurable_sheetPoint A).aemeasurable hi.aestronglyMeasurable).symm

lemma complexNormFlow_zero (A : SArithmeticData F) (w : InfinitePlace F)
    (x : SLocalProduct F A.Sf) : complexNormFlow A w 0 x = x := by
  apply Prod.ext
  · dsimp [complexNormFlow]
    simp only [zero_div, Real.exp_zero, Complex.ofReal_one, map_one, one_mul]
    exact Function.update_eq_self w x.1
  · rfl
lemma logDerivative_zero (A : SArithmeticData F) (w : InfinitePlace F)
    (f : SLocalProduct F A.Sf → ℂ) (x : SLocalProduct F A.Sf) :
    logDerivative A w 0 f x = f x := by
  simp [logDerivative, iteratedDeriv_zero, complexNormFlow_zero]

end ProbeSheet

open Filter Asymptotics
open scoped Topology

namespace ProbeSheet.MellinProof
private theorem realWeight_eventually_zero_top (W : ProbeRealAnnularWeight) :
    (fun t : ℝ => (W t : ℂ)) =ᶠ[atTop] 0 := by
  have h := (hasCompactSupport_iff_eventuallyEq.mp W.compactSupport).filter_mono
    ((atTop_le_cocompact : (atTop : Filter ℝ) ≤ cocompact ℝ).trans
      cocompact_le_coclosedCompact)
  filter_upwards [h] with t ht
  simp [ht]
private theorem realWeight_eventually_zero_zero (W : ProbeRealAnnularWeight) :
    (fun t : ℝ => (W t : ℂ)) =ᶠ[𝓝[>] 0] 0 := by
  have hz : (0 : ℝ) ∉ tsupport W.toFun := by
    intro h
    exact lt_irrefl (0 : ℝ) (W.support_positive h)
  have h : W.toFun =ᶠ[𝓝[>] (0 : ℝ)] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hz).filter_mono nhdsWithin_le_nhds
  filter_upwards [h] with t ht
  simp [ht]
private theorem realWeight_mellin_eq (W : ProbeRealAnnularWeight) :
    probeRealWeightMellin W = mellin (fun t : ℝ => (W t : ℂ)) := by
  funext z
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  simp only [smul_eq_mul]
  rw [Complex.cpow_sub _ _ hn]
  simp only [Complex.cpow_one]
  ring
theorem realWeight_mellin_differentiable (W : ProbeRealAnnularWeight) :
    Differentiable ℂ (probeRealWeightMellin W) := by
  rw [realWeight_mellin_eq]
  intro z
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := z.re + 1) (b := z.re - 1)
  · exact (Complex.continuous_ofReal.comp W.smooth.continuous).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · exact (isBigO_zero _ _).congr' (realWeight_eventually_zero_top W).symm Filter.EventuallyEq.rfl
  · linarith
  · exact (isBigO_zero _ _).congr' (realWeight_eventually_zero_zero W).symm Filter.EventuallyEq.rfl
  · linarith
theorem realWeight_mellin_convergent (W : ProbeRealAnnularWeight) (z : ℂ) :
    MellinConvergent (fun t : ℝ => (W t : ℂ)) z := by
  apply mellinConvergent_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1)
  · exact (Complex.continuous_ofReal.comp W.smooth.continuous).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · exact (isBigO_zero _ _).congr' (realWeight_eventually_zero_top W).symm Filter.EventuallyEq.rfl
  · linarith
  · exact (isBigO_zero _ _).congr' (realWeight_eventually_zero_zero W).symm Filter.EventuallyEq.rfl
  · linarith

private theorem cpow_mul_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Set.Ioi 0) (z : ℂ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ z * f t) := by
  have hcs : HasCompactSupport (fun t : ℝ => (t : ℂ) ^ z * f t) := hc.mul_left
  apply Continuous.integrable_of_hasCompactSupport ?_ hcs
  apply continuous_of_tsupport
  intro t ht
  have ht' : t ∈ tsupport f := tsupport_mul_subset_right ht
  have hpos : 0 < t := hp ht'
  exact ((continuousAt_cpow_const (by simpa using hpos)).comp
    Complex.continuous_ofReal.continuousAt).mul hf.continuousAt
private theorem cpow_derivative (z : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ z) (z * (t : ℂ) ^ (z - 1)) t := by
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id (t : ℂ)).cpow_const (c := z) (by simpa using ht)).comp_ofReal

theorem annular_mellin_logDerivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Set.Ioi 0) (z : ℂ) :
    mellin (fun t : ℝ => (t : ℂ) * deriv f t) z = -z * mellin f z := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hdp : tsupport (deriv f) ⊆ Set.Ioi 0 := tsupport_deriv_subset.trans hp
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => (t : ℂ) ^ z) (v := f)
    (u' := fun t : ℝ => z * (t : ℂ) ^ (z - 1)) (v' := deriv f)
    (fun t ht => cpow_derivative z t (hp ht))
    (fun t _ => (hf.differentiable (by simp) t).hasDerivAt)
    (cpow_mul_integrable hdc hc.deriv hdp z)
    (by simpa only [Pi.mul_def, mul_assoc] using
      (cpow_mul_integrable hf.continuous hc hp (z - 1)).const_mul z)
    (cpow_mul_integrable hf.continuous hc hp z)
  simp only [Pi.mul_def, mul_assoc, integral_const_mul] at hi
  have hleft : mellin (fun t : ℝ => (t : ℂ) * deriv f t) z =
      ∫ t : ℝ, (t : ℂ) ^ z * deriv f t := by
    unfold mellin
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : 0 < t
      · rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
        simp only [smul_eq_mul]
        field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
      · have hd : deriv f t = 0 := deriv_of_notMem_tsupport (fun h => ht (hp h))
        simp [hd]
    · intro t ht
      have hd : deriv f t = 0 := deriv_of_notMem_tsupport (fun h => ht (hp h))
      simp [hd]
  have hright : mellin f z = ∫ t : ℝ, (t : ℂ) ^ (z - 1) * f t := by
    unfold mellin
    simp only [smul_eq_mul]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hd : f t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hp h))
    simp [hd]
  rw [hleft, hright]
  simpa [neg_mul] using hi

private theorem globalMellin_eq {f : ℝ → ℂ} (hp : tsupport f ⊆ Set.Ioi 0) (z : ℂ) :
    mellin f z = ∫ t : ℝ, (t : ℂ) ^ (z - 1) * f t := by
  unfold mellin
  simp only [smul_eq_mul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [image_eq_zero_of_notMem_tsupport (fun h => ht (hp h))]
theorem annular_mellin_bounded_on_strip {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Set.Ioi 0)
    (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖mellin f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C := by
  let g : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((a : ℂ) - 1) * f t‖ +
    ‖(t : ℂ) ^ ((b : ℂ) - 1) * f t‖
  have hg : Integrable g := (cpow_mul_integrable hf hc hp _).norm.add (cpow_mul_integrable hf hc hp _).norm
  refine ⟨∫ t, g t, integral_nonneg (fun t => add_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro σ hσ τ
  rw [globalMellin_eq hp]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (cpow_mul_integrable hf hc hp _).norm hg
  filter_upwards [] with t
  by_cases ht : 0 < t
  · simp only [g, _root_.norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    have hh : t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
      by_cases ht1 : t ≤ 1
      · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 (sub_le_sub_right hσ.1 1)).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
      · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht1) (sub_le_sub_right hσ.2 1)).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
    calc
      t ^ (σ - 1) * ‖f t‖ ≤ (t ^ (a - 1) + t ^ (b - 1)) * ‖f t‖ :=
        mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = _ := by ring
  · have hz : f t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hp h))
    simp [g, hz]

 noncomputable def eulerIterate (f : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f
  | n + 1 => fun t => (t : ℂ) * deriv (eulerIterate f n) t
private theorem eulerIterate_properties {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Set.Ioi 0) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (eulerIterate f n) ∧ HasCompactSupport (eulerIterate f n) ∧
    tsupport (eulerIterate f n) ⊆ Set.Ioi 0 := by
  induction n with
  | zero => exact ⟨hf, hc, hp⟩
  | succ n ih =>
    refine ⟨?_, ih.2.1.deriv.mul_left, tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans ih.2.2)⟩
    dsimp only [eulerIterate]
    exact (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ))).mul
      ((contDiff_infty_iff_deriv.mp ih.1).2)
private theorem eulerIterate_mellin {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Set.Ioi 0) (n : ℕ) (z : ℂ) :
    mellin (eulerIterate f n) z = (-z) ^ n * mellin f z := by
  induction n with
  | zero => simp [eulerIterate]
  | succ n ih =>
    obtain ⟨hs, hc', hp'⟩ := eulerIterate_properties hf hc hp n
    rw [eulerIterate, annular_mellin_logDerivative hs hc' hp', ih, pow_succ]
    ring
theorem annular_mellin_rapid_on_strip {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Set.Ioi 0) (a b B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖mellin f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B) := by
  obtain ⟨n, hn⟩ := exists_nat_ge B
  obtain ⟨C0, hC0, hbound0⟩ := annular_mellin_bounded_on_strip hf.continuous hc hp a b
  obtain ⟨hs, hc', hp'⟩ := eulerIterate_properties hf hc hp n
  obtain ⟨Cn, hCn, hboundn⟩ := annular_mellin_bounded_on_strip hs.continuous hc' hp' a b
  refine ⟨(C0 + Cn) * 2 ^ n, mul_nonneg (add_nonneg hC0 hCn) (by positivity), ?_⟩
  intro σ hσ τ
  let z : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  have hzn : ‖z‖ ^ n * ‖mellin f z‖ ≤ Cn := by
    have h := hboundn σ hσ τ
    rw [eulerIterate_mellin hf hc hp n, _root_.norm_mul, norm_pow, norm_neg] at h
    exact h
  have hτz : |τ| ≤ ‖z‖ := by
    simpa [z] using Complex.abs_im_le_norm z
  have hbase : 1 ≤ 1 + |τ| := le_add_of_nonneg_right (abs_nonneg τ)
  have hpow : (1 + |τ|) ^ B ≤ (1 + |τ|) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase hn
  have hprod : ‖mellin f z‖ * (1 + |τ|) ^ n ≤ (C0 + Cn) * 2 ^ n := by
    by_cases hτ : |τ| ≤ 1
    · have hh : (1 + |τ|) ^ n ≤ (2 : ℝ) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      exact (mul_le_mul (hbound0 σ hσ τ) hh (by positivity) hC0).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCn) (by positivity))
    · have hh : (1 + |τ|) ^ n ≤ (2 : ℝ) ^ n * ‖z‖ ^ n := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        linarith
      calc
        ‖mellin f z‖ * (1 + |τ|) ^ n ≤ ‖mellin f z‖ * (2 ^ n * ‖z‖ ^ n) :=
          mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = (‖z‖ ^ n * ‖mellin f z‖) * 2 ^ n := by ring
        _ ≤ Cn * 2 ^ n := mul_le_mul_of_nonneg_right hzn (by positivity)
        _ ≤ (C0 + Cn) * 2 ^ n :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC0) (by positivity)
  have hprodB : ‖mellin f z‖ * (1 + |τ|) ^ B ≤ (C0 + Cn) * 2 ^ n :=
    (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans hprod
  rw [Real.rpow_neg (by positivity)]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) B)).mpr hprodB

theorem realWeight_mellin_rapid_on_strip (W : ProbeRealAnnularWeight)
    (a b B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
      ‖probeRealWeightMellin W ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        C * (1 + |τ|) ^ (-B) := by
  rw [realWeight_mellin_eq]
  apply annular_mellin_rapid_on_strip (Complex.ofRealCLM.contDiff.comp W.smooth)
    (W.compactSupport.comp_left (by simp))
  · exact (tsupport_comp_subset Complex.ofReal_zero W.toFun).trans W.support_positive
  · exact hB

theorem vertical_integrable_of_quadratic_decay (M : ℂ → ℂ) (c C : ℝ)
    (hmeas : AEStronglyMeasurable (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I)))
    (hbound : ∀ τ : ℝ, ‖M ((c : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-2 : ℝ)) :
    Complex.VerticalIntegrable M c := by
  have hkernel : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-2 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) (r := 2) (by simp))
  exact (hkernel.const_mul C).mono' hmeas (Filter.Eventually.of_forall hbound)

theorem inverse_kernel_integrable (M : ℂ → ℂ) (c T : ℝ) (hT : 0 < T)
    (hM : Complex.VerticalIntegrable M c) :
    Integrable (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) := by
  have hk : Continuous (fun τ : ℝ => (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hT.ne')
  apply (hM.norm.const_mul (T ^ (-c))).mono'
    (hM.aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards [] with τ
  simp only [Pi.mul_apply]
  rw [_root_.norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  exact le_of_eq (mul_comm _ _)

theorem mellin_inversion_explicit (f : ℝ → ℂ) (M : ℂ → ℂ) (c T : ℝ) (hT : 0 < T)
    (hconv : MellinConvergent f c) (hM : Complex.VerticalIntegrable M c)
    (heq : ∀ τ : ℝ, mellin f ((c : ℂ) + (τ : ℂ) * Complex.I) =
      M ((c : ℂ) + (τ : ℂ) * Complex.I)) (hcont : ContinuousAt f T) :
    Integrable (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) ∧
    f T = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ : ℝ, M ((c : ℂ) + (τ : ℂ) * Complex.I) *
        (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I) := by
  refine ⟨inverse_kernel_integrable M c T hT hM, ?_⟩
  have hFm : Complex.VerticalIntegrable (mellin f) c := by
    unfold Complex.VerticalIntegrable
    have hh := hM
    unfold Complex.VerticalIntegrable at hh
    simpa only [heq] using hh
  have hi := mellinInv_mellin_eq c f hT hconv hFm hcont
  rw [← hi]
  unfold mellinInv
  simp only [heq, smul_eq_mul, Complex.real_smul, one_div, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat, neg_add]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with τ
  simp only [sub_eq_add_neg, mul_comm]

lemma mellinConvergent_iff_explicit (f : ℝ → ℂ) (z : ℂ) :
    MellinConvergent f z ↔
      IntegrableOn (fun T : ℝ => f T * (T : ℂ) ^ z / (T : ℂ)) (Set.Ioi 0) := by
  unfold MellinConvergent
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  have hn : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  simp only [smul_eq_mul, Complex.cpow_sub _ _ hn, Complex.cpow_one]
  ring
lemma mellin_eq_explicit (f : ℝ → ℂ) (z : ℂ) :
    mellin f z = ∫ T in Set.Ioi (0 : ℝ), f T * (T : ℂ) ^ z / (T : ℂ) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro T hT
  have hn : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  simp only [smul_eq_mul, Complex.cpow_sub _ _ hn, Complex.cpow_one]
  ring

theorem positive_profile_mellin_inversion (V : ℝ → ℂ) (M : ℂ → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun T : ℝ => V T * (T : ℂ) ^ z / (T : ℂ)) (Set.Ioi 0))
    (heq : ∀ z : ℂ, 0 < z.re →
      (∫ T in Set.Ioi (0 : ℝ), V T * (T : ℂ) ^ z / (T : ℂ)) = M z)
    (hhol : DifferentiableOn ℂ M {z | 0 < z.re})
    (hdecay : ∀ (a b B : ℝ), 0 < a → a ≤ b → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
        ‖M ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B))
    (hcont : ContinuousOn V (Set.Ioi 0)) (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    Integrable (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I) *
      (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I)) ∧
    V T = ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ τ : ℝ, M ((c : ℂ) + (τ : ℂ) * Complex.I) *
        (T : ℂ) ^ (-(c : ℂ) - (τ : ℂ) * Complex.I) := by
  have hline : Continuous (fun τ : ℝ => M ((c : ℂ) + (τ : ℂ) * Complex.I)) := by
    apply hhol.continuousOn.comp_continuous (by fun_prop)
    intro τ
    simpa using hc
  obtain ⟨C, _, hb⟩ := hdecay c c 2 hc le_rfl (by norm_num)
  have hint := vertical_integrable_of_quadratic_decay M c C hline.aestronglyMeasurable
    (hb c ⟨le_rfl, le_rfl⟩)
  apply mellin_inversion_explicit V M c T hT
    ((mellinConvergent_iff_explicit _ _).mpr (hconv c hc)) hint
  · intro τ
    rw [mellin_eq_explicit]
    apply heq
    simpa using hc
  · exact (hcont T hT).continuousAt (isOpen_Ioi.mem_nhds hT)

theorem positive_profile_mellin_holomorphic (V : ℝ → ℂ) (M : ℂ → ℂ)
    (hcont : ContinuousOn V (Set.Ioi 0))
    (heq : ∀ z : ℂ, 0 < z.re →
      (∫ T in Set.Ioi (0 : ℝ), V T * (T : ℂ) ^ z / (T : ℂ)) = M z)
    (hbound : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ T : ℝ, 0 < T →
      ‖V T‖ ≤ C * T ^ (-σ)) :
    DifferentiableOn ℂ M {z | 0 < z.re} := by
  have hu : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  intro z hz
  have hzpos : 0 < z.re := hz
  obtain ⟨Ca, hCa⟩ := hbound (z.re + 1) (by linarith)
  obtain ⟨Cb, hCb⟩ := hbound (z.re / 2) (by linarith)
  have htop : V =O[atTop] (fun T : ℝ => T ^ (-(z.re + 1))) := by
    apply IsBigO.of_bound Ca
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT.le _)] using hCa T hT
  have hzero : V =O[𝓝[>] 0] (fun T : ℝ => T ^ (-(z.re / 2))) := by
    apply IsBigO.of_bound Cb
    filter_upwards [self_mem_nhdsWithin] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hT) _)] using hCb T hT
  have hd : DifferentiableAt ℂ (mellin V) z :=
    mellin_differentiableAt_of_isBigO_rpow (hcont.locallyIntegrableOn measurableSet_Ioi)
      htop (by linarith) hzero (by linarith)
  apply DifferentiableAt.differentiableWithinAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hu.mem_nhds hz] with s hs
  exact ((mellin_eq_explicit V s).trans (heq s hs)).symm

end ProbeSheet.MellinProof

theorem probe_sheet_norm_one_haar_exists (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν) :
    ∃ dt : @Measure A.G1 (borel _),
      @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt ∧
      ProbeSheet.HaarDisintegration A ν dt := by
  letI : MeasurableSpace (SLocalProduct F A.Sf) := borel _
  letI : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  letI := hν
  exact ProbeSheet.normalized_haar_exists A ν

theorem probe_sheet_mellin_estimates_of_disintegration (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (hnormalized : ProbeSheet.HaarDisintegration A ν dt)
    (w : InfinitePlace F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x}) :
    ProbeSheet.MellinEstimates A e μ ν dt w W0 W1 := by
  letI : MeasurableSpace (SLocalProduct F A.Sf) := borel _
  letI : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  letI := hdt
  let M := ProbeWeight.fourierMellin F A.Sf e μ ν W0
  let V := ProbeSheet.envelope A e μ dt W0
  have hglobal : ∀ z : ℂ, 0 < z.re → Integrable
      (fun y : (SLocalProduct F A.Sf)ˣ => ProbeWeight.fourier F A.Sf e μ W0 y.val *
        (ProbeWeight.modulus F A.Sf y : ℂ) ^ z) ν := by
    exact ProbeSheetFourierMellinBounds.fourier_mellin_integrable A e he hne μ ν hμ hν W0
      hW0 hcompact hannular
  have hprofile : ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun T : ℝ => V T * (T : ℂ) ^ z / (T : ℂ)) (Set.Ioi 0) ∧
      (∫ T in Set.Ioi (0 : ℝ), V T * (T : ℂ) ^ z / (T : ℂ)) = M z := by
    intro z hz
    exact ProbeSheet.sheet_mellin_of_integrable A ν dt hnormalized
      (fun y => ProbeWeight.fourier F A.Sf e μ W0 y.val) z (hglobal z hz)
  have hdecay : ∀ (a b B : ℝ), 0 < a → a ≤ b → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc a b, ∀ τ : ℝ,
        ‖M ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B) := by
    exact ProbeSheetFourierMellinBounds.fourier_mellin_rapid_on_strip A e he hne μ ν hμ hν W0
      hW0 hcompact hannular
  have hcont : ContinuousOn V (Set.Ioi 0) := by
    exact ProbeSheetFourierMellinBounds.positive_sheet_continuous A e he hne μ dt hμ hdt W0
      hW0 hcompact hannular
  have hsheet : ∀ (σ : ℝ) (k : ℕ), 0 < σ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : ℝ, 0 < T →
        Integrable (fun t => ProbeSheet.logDerivative A w k
          (ProbeWeight.fourier F A.Sf e μ W0) (ProbeSheet.sheetPoint A T t).val) dt ∧
        (∫ t, ‖ProbeSheet.logDerivative A w k (ProbeWeight.fourier F A.Sf e μ W0)
          (ProbeSheet.sheetPoint A T t).val‖ ∂dt) ≤ C * T ^ (-σ) := by
    exact ProbeSheetFourierMellinBounds.sheet_log_derivative_bounds A e he hne μ dt hμ hdt w W0
      hW0 hcompact hannular
  have henvelopeBound : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ T : ℝ, 0 < T →
      ‖V T‖ ≤ C * T ^ (-σ) := by
    intro σ hσ
    obtain ⟨C, hC, hbound⟩ := hsheet σ 0 hσ
    refine ⟨C, ?_⟩
    intro T hT
    apply (norm_integral_le_integral_norm _).trans
    simpa only [ProbeSheet.logDerivative_zero] using (hbound T hT).2
  have hhol : DifferentiableOn ℂ M {z | 0 < z.re} :=
    ProbeSheet.MellinProof.positive_profile_mellin_holomorphic V M hcont
      (fun z hz => (hprofile z hz).2) henvelopeBound
  unfold ProbeSheet.MellinEstimates
  refine ⟨?_, hsheet, ?_, hhol, hdecay,
    ProbeSheet.MellinProof.realWeight_mellin_differentiable W1, ?_, ?_⟩
  · intro T hT
    obtain ⟨C, hC, hbound⟩ := hsheet 1 0 (by norm_num)
    simpa only [ProbeSheet.logDerivative_zero] using (hbound T hT).1
  · intro z hz
    exact ⟨hglobal z hz, hprofile z hz⟩
  · intro σ0 σ1 B _ hB
    exact ProbeSheet.MellinProof.realWeight_mellin_rapid_on_strip W1 σ0 σ1 B hB
  · exact ProbeSheet.MellinProof.positive_profile_mellin_inversion V M
      (fun z hz => (hprofile z hz).1) (fun z hz => (hprofile z hz).2) hhol hdecay hcont

theorem probe_sheet_mellin_estimates (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (w : InfinitePlace F) (W0 : SLocalProduct F A.Sf → ℂ)
    (W1 : ProbeRealAnnularWeight) (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x}) :
    ∃ dt : @Measure A.G1 (borel _),
      @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt ∧
      ProbeSheet.HaarDisintegration A ν dt ∧
      ProbeSheet.MellinEstimates A e μ ν dt w W0 W1 := by
  obtain ⟨dt, hdt, hdisintegration⟩ := probe_sheet_norm_one_haar_exists F A ν hν
  exact ⟨dt, hdt, hdisintegration,
    probe_sheet_mellin_estimates_of_disintegration F A e he htrace hne μ ν dt
      hμ hν hdt hdisintegration w W0 W1 hW0 hcompact hannular⟩

end
end DedekindZetaZeroFree
