module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.IntrinsicHilbertIntegrals

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentChartRestriction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral
open KPContActualCotangentPieceHilbertSum
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (cover : CountableCover F ζ hζ U R P H)
variable (a : ShrunkChart F ζ hζ U R P H)

def fullPiece : KPMeasurableLocalL2.Piece (localData a) where
  set := Set.univ
  measurableSet := MeasurableSet.univ
  invariant _ _ := Iff.rfl

def Q : Submodule ℂ (Lp (E F) 2 a.liftedMeasure) :=
  KPMeasurableLocalL2.Q (localData a) (fullPiece a)

instance qInnerProductSpace : InnerProductSpace ℂ (Q a) :=
  KPMeasurableLocalL2.Q_innerProductSpace (localData a) (fullPiece a)

instance qCompleteSpace : CompleteSpace (Q a) :=
  KPMeasurableLocalL2.Q_completeSpace (localData a) (fullPiece a)

def localCoefficient (r : Family (U := U) (H := H)) (y : a.domain) : E F :=
  coefficient r a (coordinates a y)

private lemma q_coordinates (y : a.domain) :
    KPContCotangentOverlapRationalBranches.q a (coordinates a y).val = a.toBase y := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
    intro z; funext k; simp [labeledA, labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q, coordinates]
  rw [hi]

private theorem localCoefficient_covariant (r : Family (U := U) (H := H))
    (γ : Gamma a) (y : a.domain) :
    localCoefficient a r (actualActionEquiv a γ y) =
      actualTensor a γ y (localCoefficient a r y) := by
  have hcov := (r.property).2.1 a γ (coordinates a y).val (coordinates a y).property
  simp only [localCoefficient, actualTensor]
  rw [show coordinates a (actualActionEquiv a γ y) =
      ⟨(isotropyArrow a γ).psi (coordinates a y).val,
        isotropy_mem a γ (coordinates a y).val (coordinates a y).property⟩
      from Subtype.ext (coordinates_action a γ y)]
  exact hcov

theorem localCoefficient_memLp (r : SquareFiniteFamily (U := U) (H := H)) :
    MemLp (localCoefficient a r.val) 2 a.liftedMeasure := by
  have hmeas : Measurable (localCoefficient a r.val) :=
    ((r.val.property).1 a).comp (coordinates_continuous a).measurable
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnn : ∀ y, ‖(‖localCoefficient a r.val y‖ ^ 2 : ℝ)‖ₑ =
      (normSquare r.val (a.toBase y) : ℝ≥0∞) := by
    intro y
    have h1 : ‖(‖localCoefficient a r.val y‖ ^ 2 : ℝ)‖ₑ =
        (‖localCoefficient a r.val y‖₊ : ℝ≥0∞) ^ 2 := by
      have h : ‖(‖localCoefficient a r.val y‖ ^ 2 : ℝ)‖ₑ =
          ENNReal.ofReal (‖localCoefficient a r.val y‖ ^ 2) :=
        Real.enorm_eq_ofReal (r := ‖localCoefficient a r.val y‖ ^ 2) (sq_nonneg _)
      rw [h, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm (x := localCoefficient a r.val y),
        enorm_eq_nnnorm]
    rw [h1, ← q_coordinates a y, normSquare_chart]
    rfl
  simp only [hnn]
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  calc ∫⁻ y, (normSquare r.val (a.toBase y) : ℝ≥0∞) ∂a.liftedMeasure
      = ∫⁻ b, (normSquare r.val b : ℝ≥0∞) ∂(Measure.map a.toBase a.liftedMeasure) :=
        (lintegral_map' (f := fun b => (normSquare r.val b : ℝ≥0∞)) (g := a.toBase)
          (μ := a.liftedMeasure) (measurable_normSquare r.val).coe_nnreal_ennreal.aemeasurable
          hP.measurable.aemeasurable).symm
    _ = ∫⁻ b, (normSquare r.val b : ℝ≥0∞) ∂
          ((baseMeasure (R := R) (P := P) (U := U)).restrict a.baseDomain) := by
        rw [hP.exact_pushforward]
    _ ≤ ∫⁻ b, (normSquare r.val b : ℝ≥0∞) ∂
          (baseMeasure (R := R) (P := P) (U := U)) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ b, ENNReal.ofReal (normSquare r.val b : ℝ) ∂
          (baseMeasure (R := R) (P := P) (U := U)) := by
        simp only [ENNReal.ofReal_coe_nnreal]
    _ < ⊤ := r.property

def familyLp (r : SquareFiniteFamily (U := U) (H := H)) : Lp (E F) 2 a.liftedMeasure :=
  (localCoefficient_memLp a r).toLp (localCoefficient a r.val)

theorem familyLp_mem_Q (r : SquareFiniteFamily (U := U) (H := H)) :
    familyLp a r ∈ Q a := by
  show KPMeasurableLocalL2.SupportedCovariant (localData a) (fullPiece a) (familyLp a r)
  refine ⟨?_, ?_⟩
  · intro γ
    have hcoe := MemLp.coeFn_toLp (localCoefficient_memLp a r)
    have hact := (action_preserving a γ).quasiMeasurePreserving.ae hcoe
    filter_upwards [hcoe, hact] with y hy hyact
    show (familyLp a r) (actualActionEquiv a γ y) =
      actualTensor a γ y ((familyLp a r) y)
    simp only [familyLp]
    rw [hyact, hy, localCoefficient_covariant a r.val γ y]
  · filter_upwards with y hy
    exact absurd (Set.mem_univ y) hy

def familyQ (r : SquareFiniteFamily (U := U) (H := H)) : Q a :=
  ⟨familyLp a r, familyLp_mem_Q a r⟩

private theorem familyQ_inner_eq_integral (r s : SquareFiniteFamily (U := U) (H := H)) :
    inner ℂ (familyQ a r) (familyQ a s) =
      ∫ x in a.baseDomain, pair r.val s.val x
        ∂(baseMeasure (R := R) (P := P) (U := U)) := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have h1 : inner ℂ (familyQ a r) (familyQ a s) =
      ∫ y, inner ℂ ((familyQ a r : Lp (E F) 2 a.liftedMeasure) y)
        ((familyQ a s : Lp (E F) 2 a.liftedMeasure) y) ∂a.liftedMeasure :=
    KPMeasurableLocalL2.Q_inner_eq_integral (localData a) (fullPiece a) (familyQ a r) (familyQ a s)
  rw [h1]
  rw [integral_congr_ae (show (fun y => inner ℂ ((familyQ a r : Lp (E F) 2 a.liftedMeasure) y)
        ((familyQ a s : Lp (E F) 2 a.liftedMeasure) y))
        =ᵐ[a.liftedMeasure] (fun y => pair r.val s.val (a.toBase y)) from by
    filter_upwards [MemLp.coeFn_toLp (localCoefficient_memLp a r),
      MemLp.coeFn_toLp (localCoefficient_memLp a s)] with y hy1 hy2
    change inner ℂ (familyLp a r y) (familyLp a s y) = pair r.val s.val (a.toBase y)
    simp only [familyLp]
    rw [hy1, hy2, ← q_coordinates a y, pair_chart]
    rfl)]
  rw [(integral_map (μ := a.liftedMeasure) (φ := a.toBase) hP.measurable.aemeasurable
    (measurable_pair r.val s.val).aestronglyMeasurable).symm]
  rw [hP.exact_pushforward]

private theorem familyQ_norm_sq_eq_integral (r : SquareFiniteFamily (U := U) (H := H)) :
    ‖familyQ a r‖ ^ 2 = ∫ x in a.baseDomain, (normSquare r.val x : ℝ)
      ∂(baseMeasure (R := R) (P := P) (U := U)) := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hint : Integrable (fun x => pair r.val r.val x)
      ((baseMeasure (R := R) (P := P) (U := U)).restrict a.baseDomain) :=
    (integrable_pair r r).mono_measure Measure.restrict_le_self
  calc ‖familyQ a r‖ ^ 2
      = RCLike.re (inner ℂ (familyQ a r) (familyQ a r)) :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (familyQ a r)
    _ = RCLike.re (∫ x in a.baseDomain, pair r.val r.val x
          ∂(baseMeasure (R := R) (P := P) (U := U))) := by
        rw [familyQ_inner_eq_integral a r r]
    _ = ∫ x in a.baseDomain, RCLike.re (pair r.val r.val x)
          ∂(baseMeasure (R := R) (P := P) (U := U)) := (integral_re hint).symm
    _ = ∫ x in a.baseDomain, (normSquare r.val x : ℝ)
          ∂(baseMeasure (R := R) (P := P) (U := U)) := by
      refine integral_congr_ae ?_
      have hpt : ∀ᵐ x ∂((baseMeasure (R := R) (P := P) (U := U)).restrict a.baseDomain),
          RCLike.re (pair r.val r.val x) = (normSquare r.val x : ℝ) := by
        rw [MeasureTheory.ae_restrict_iff' hP.base_measurable]
        filter_upwards with b hb
        obtain ⟨y, rfl⟩ := hb
        rw [← q_coordinates a y, pair_chart, normSquare_chart,
          ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
            (coefficient r.val a (coordinates a y))]
        push_cast
        rfl
      exact hpt

private theorem localCoefficient_ae_eq (r s : SquareFiniteFamily (U := U) (H := H))
    (hrs : AeEquivalent r.val s.val) :
    localCoefficient a r.val =ᵐ[a.liftedMeasure] localCoefficient a s.val := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hbase : ∀ᵐ x ∂(Measure.map a.toBase a.liftedMeasure),
      normSquare (r.val - s.val) x = 0 := by
    rw [hP.exact_pushforward]
    exact ae_mono Measure.restrict_le_self hrs
  have hlift := ae_of_ae_map hP.measurable.aemeasurable hbase
  filter_upwards [hlift] with y hy
  rw [← q_coordinates a y, normSquare_chart] at hy
  have hz : coefficient (r.val - s.val) a (coordinates a y) = 0 := by
    simpa using hy
  change localCoefficient a r.val y - localCoefficient a s.val y = 0 at hz
  exact sub_eq_zero.mp hz

 theorem familyQ_ae_eq (r s : SquareFiniteFamily (U := U) (H := H))
    (hrs : AeEquivalent r.val s.val) : familyQ a r = familyQ a s := by
  apply Subtype.ext
  apply Lp.ext
  exact (MemLp.coeFn_toLp (localCoefficient_memLp a r)).trans
    ((localCoefficient_ae_eq a r s hrs).trans
      (MemLp.coeFn_toLp (localCoefficient_memLp a s)).symm)

 theorem familyQ_add (r s : SquareFiniteFamily (U := U) (H := H)) :
    familyQ a (r + s) = familyQ a r + familyQ a s := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (localCoefficient_memLp a (r + s)),
    MemLp.coeFn_toLp (localCoefficient_memLp a r),
    MemLp.coeFn_toLp (localCoefficient_memLp a s),
    Lp.coeFn_add (familyLp a r) (familyLp a s)] with y hsum hr hs hadd
  change familyLp a (r + s) y = (familyLp a r + familyLp a s) y
  rw [hadd]
  simp only [familyLp, Pi.add_apply]
  rw [hsum, hr, hs]
  rfl

 theorem familyQ_smul (c : ℂ) (r : SquareFiniteFamily (U := U) (H := H)) :
    familyQ a (c • r) = c • familyQ a r := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (localCoefficient_memLp a (c • r)),
    MemLp.coeFn_toLp (localCoefficient_memLp a r),
    Lp.coeFn_smul c (familyLp a r)] with y hsmul hr hcoe
  change familyLp a (c • r) y = (c • familyLp a r) y
  rw [hcoe]
  simp only [familyLp, Pi.smul_apply]
  rw [hsmul, hr]
  rfl

def restrictionLinear : IntrinsicHilbert cover →ₗ[ℂ] Q a where
  toFun := Quotient.lift (familyQ a) (by
    intro r s hrs
    apply familyQ_ae_eq a r s
    have heq : toAeQuotient r = toAeQuotient s := by
      change Quotient.mk _ r = Quotient.mk _ s
      exact Quotient.sound hrs
    exact (toAeQuotient_eq_iff r s).mp heq)
  map_add' := by
    intro v w
    obtain ⟨r, rfl⟩ := toAeQuotient_surjective (intrinsicClass cover v)
    obtain ⟨s, rfl⟩ := toAeQuotient_surjective (intrinsicClass cover w)
    erw [← toAeQuotient_add r s]
    exact familyQ_add a r s
  map_smul' := by
    intro c v
    obtain ⟨r, rfl⟩ := toAeQuotient_surjective (intrinsicClass cover v)
    erw [← toAeQuotient_smul c r]
    exact familyQ_smul a c r

theorem restrictionLinear_norm_le (v : IntrinsicHilbert cover) :
    ‖restrictionLinear cover a v‖ ≤ ‖v‖ := by
  obtain ⟨r, hr⟩ := toAeQuotient_surjective (intrinsicClass cover v)
  have hres : restrictionLinear cover a v = familyQ a r := by
    have hv : v = toAeQuotient r := by rw [hr]; rfl
    rw [hv]
    rfl
  have hsq : ‖restrictionLinear cover a v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hres, familyQ_norm_sq_eq_integral a r,
      KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral cover v r hr]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _)
      (integrable_normSquare r)
  nlinarith [norm_nonneg (restrictionLinear cover a v), norm_nonneg v]

def res : IntrinsicHilbert cover →L[ℂ] Q a :=
  (restrictionLinear cover a).mkContinuous 1 (by
    intro v
    simpa only [one_mul] using restrictionLinear_norm_le cover a v)

theorem res_eq_familyQ (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v) :
    res cover a v = familyQ a r := by
  have hv : v = toAeQuotient (R := R) (U := U) (H := H) r := by
    rw [hr]
    rfl
  rw [hv]
  rfl

theorem res_represented (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v) :
    (fun y => (res cover a v : Lp (E F) 2 a.liftedMeasure) y) =ᵐ[a.liftedMeasure]
      localCoefficient a r.val := by
  rw [res_eq_familyQ cover a v r hr]
  exact MemLp.coeFn_toLp (localCoefficient_memLp a r)

theorem res_norm_le (v : IntrinsicHilbert cover) : ‖res cover a v‖ ≤ ‖v‖ := by
  calc ‖res cover a v‖ ≤ ‖res cover a‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ := by
      gcongr
      exact LinearMap.mkContinuous_norm_le _ zero_le_one _
    _ = ‖v‖ := one_mul _

theorem res_inner_eq_integral (v w : IntrinsicHilbert cover)
    (r s : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v)
    (hs : toAeQuotient s = intrinsicClass cover w) :
    inner ℂ (res cover a v) (res cover a w) =
      ∫ x in a.baseDomain, pair r.val s.val x
        ∂(KPContActualCotangentMeasurableFamilies.baseMeasure (R := R) (P := P) (U := U)) := by
  rw [res_eq_familyQ cover a v r hr, res_eq_familyQ cover a w s hs]
  exact familyQ_inner_eq_integral a r s

theorem res_norm_sq_eq_integral (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v) :
    ‖res cover a v‖ ^ 2 = ∫ x in a.baseDomain, (normSquare r.val x : ℝ)
      ∂(KPContActualCotangentMeasurableFamilies.baseMeasure (R := R) (P := P) (U := U)) := by
  rw [res_eq_familyQ cover a v r hr]
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  have hint : Integrable (fun x => pair r.val r.val x)
      ((baseMeasure (R := R) (P := P) (U := U)).restrict a.baseDomain) :=
    (integrable_pair r r).mono_measure Measure.restrict_le_self
  calc ‖familyQ a r‖ ^ 2
      = RCLike.re (inner ℂ (familyQ a r) (familyQ a r)) :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (familyQ a r)
    _ = RCLike.re (∫ x in a.baseDomain, pair r.val r.val x
          ∂(baseMeasure (R := R) (P := P) (U := U))) := by
        rw [familyQ_inner_eq_integral a r r]
    _ = ∫ x in a.baseDomain, RCLike.re (pair r.val r.val x)
          ∂(baseMeasure (R := R) (P := P) (U := U)) := (integral_re hint).symm
    _ = ∫ x in a.baseDomain, (normSquare r.val x : ℝ)
          ∂(baseMeasure (R := R) (P := P) (U := U)) := by
      refine integral_congr_ae ?_
      have hpt : ∀ᵐ x ∂((baseMeasure (R := R) (P := P) (U := U)).restrict a.baseDomain),
          RCLike.re (pair r.val r.val x) = (normSquare r.val x : ℝ) := by
        rw [MeasureTheory.ae_restrict_iff' hP.base_measurable]
        filter_upwards with b hb
        obtain ⟨y, rfl⟩ := hb
        rw [← q_coordinates a y, pair_chart, normSquare_chart,
          ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
            (coefficient r.val a (coordinates a y))]
        push_cast
        rfl
      exact hpt

theorem original_normalization :
    a.liftedMeasure =
      ((H.disintegration U).componentWeight a.component /
        (Nat.card a.Isotropy : ℝ≥0∞)) •
      Measure.comap (Subtype.val : a.domain → KPCuspGenuineMonodromy.SymmetricSpace F)
        ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain) := rfl

def coefficientIndex : (Fin (d F) × Fin 3) ≃ Fin (3 * d F) :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

def coefficientReindex : E F ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (3 * d F)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (coefficientIndex (F := F))

def euclideanData : KPMeasurableLocalL2.Data a.domain
    (EuclideanSpace ℂ (Fin (3 * d F))) (Gamma a) where
  measure := a.liftedMeasure
  action := actualActionEquiv a
  action_one := (localData a).action_one
  action_mul := (localData a).action_mul
  invariant_measure := action_preserving a
  tensor γ y := ((coefficientReindex (F := F)).symm.trans (actualTensor a γ y)).trans
    (coefficientReindex (F := F))
  measurable_tensor := by
    intro γ
    simp only [LinearIsometryEquiv.trans_apply]
    have h1 : Measurable (fun p : a.domain × EuclideanSpace ℂ (Fin (3 * d F)) =>
        (p.1, (coefficientReindex (F := F)).symm p.2)) :=
      measurable_fst.prodMk ((coefficientReindex (F := F)).symm.toContinuousLinearEquiv.continuous.measurable.comp measurable_snd)
    have h2 : Measurable (fun p : a.domain × EuclideanSpace ℂ (Fin (3 * d F)) =>
        actualTensor a γ p.1 ((coefficientReindex (F := F)).symm p.2)) := by
      simpa only [Function.comp_def, Function.comp_apply] using (tensor_measurable a γ).comp h1
    exact (coefficientReindex (F := F)).toContinuousLinearEquiv.continuous.measurable.comp h2
  tensor_one := by
    intro y
    ext v
    simp [LinearIsometryEquiv.trans_apply, tensor_one a y]
  tensor_mul := by
    intro γ δ y v
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
    rw [tensor_mul a γ δ y]

def euclideanFullPiece : KPMeasurableLocalL2.Piece (euclideanData a) where
  set := Set.univ
  measurableSet := MeasurableSet.univ
  invariant _ _ := Iff.rfl

def EuclideanQ : Submodule ℂ (Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) :=
  KPMeasurableLocalL2.Q (euclideanData a) (euclideanFullPiece a)

instance euclideanQInnerProductSpace : InnerProductSpace ℂ (EuclideanQ a) :=
  KPMeasurableLocalL2.Q_innerProductSpace (euclideanData a) (euclideanFullPiece a)

def reindexQ : Q a ≃ₗᵢ[ℂ] EuclideanQ a where
  toFun f := ⟨(coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (f : Lp (E F) 2 a.liftedMeasure), by
      let L := (coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
      have hf : KPMeasurableLocalL2.SupportedCovariant (localData a) (fullPiece a) f.val := f.property
      change KPMeasurableLocalL2.SupportedCovariant (euclideanData a) (euclideanFullPiece a) (L.compLp f.val)
      refine ⟨?_, ?_⟩
      · intro γ
        have heq := L.coeFn_compLp f.val
        have hact := (action_preserving a γ).quasiMeasurePreserving.ae heq
        filter_upwards [heq, hact, hf.1 γ] with y hy hyact hcov
        change L.compLp f.val (actualActionEquiv a γ y) =
          ((coefficientReindex (F := F)).symm.trans (actualTensor a γ y)).trans
            (coefficientReindex (F := F)) (L.compLp f.val y)
        rw [hyact, hy]
        change coefficientReindex (F := F) (f.val (actualActionEquiv a γ y)) = _
        change f.val (actualActionEquiv a γ y) = actualTensor a γ y (f.val y) at hcov
        rw [hcov]
        simp [L, LinearIsometryEquiv.trans_apply]
      · filter_upwards with y hy
        exact absurd (Set.mem_univ y) hy⟩
  invFun f := ⟨(coefficientReindex (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (f : Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure), by
      let L := (coefficientReindex (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hf : KPMeasurableLocalL2.SupportedCovariant (euclideanData a) (euclideanFullPiece a) f.val := f.property
      change KPMeasurableLocalL2.SupportedCovariant (localData a) (fullPiece a) (L.compLp f.val)
      refine ⟨?_, ?_⟩
      · intro γ
        have heq := L.coeFn_compLp f.val
        have hact := (action_preserving a γ).quasiMeasurePreserving.ae heq
        filter_upwards [heq, hact, hf.1 γ] with y hy hyact hcov
        change L.compLp f.val (actualActionEquiv a γ y) = actualTensor a γ y (L.compLp f.val y)
        rw [hyact, hy]
        change (coefficientReindex (F := F)).symm (f.val (actualActionEquiv a γ y)) = _
        change f.val (actualActionEquiv a γ y) =
          ((coefficientReindex (F := F)).symm.trans (actualTensor a γ y)).trans
            (coefficientReindex (F := F)) (f.val y) at hcov
        rw [hcov]
        simp [L, LinearIsometryEquiv.trans_apply]
      · filter_upwards with y hy
        exact absurd (Set.mem_univ y) hy⟩
  left_inv := by
    intro f
    apply Subtype.ext
    apply Lp.ext
    let L := (coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
    let M := (coefficientReindex (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    filter_upwards [M.coeFn_compLp (L.compLp f.val), L.coeFn_compLp f.val] with y hy hz
    change M.compLp (L.compLp f.val) y = f.val y
    rw [hy, hz]
    exact (coefficientReindex (F := F)).symm_apply_apply _
  right_inv := by
    intro f
    apply Subtype.ext
    apply Lp.ext
    let L := (coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
    let M := (coefficientReindex (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    filter_upwards [L.coeFn_compLp (M.compLp f.val), M.coeFn_compLp f.val] with y hy hz
    change L.compLp (M.compLp f.val) y = f.val y
    rw [hy, hz]
    exact (coefficientReindex (F := F)).apply_symm_apply _
  map_add' := by
    intro f g
    apply Subtype.ext
    exact map_add ((coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 a.liftedMeasure) f.val g.val
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact map_smul ((coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap.compLpₗ 2 a.liftedMeasure) c f.val
  norm_map' := by
    intro f
    let L := (coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
    change ‖L.compLp f.val‖ = ‖f.val‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [L.coeFn_compLp f.val] with y hy
    rw [hy]
    exact (coefficientReindex (F := F)).norm_map _

def resEuclidean : IntrinsicHilbert cover →L[ℂ] EuclideanQ a :=
  (reindexQ a).toContinuousLinearEquiv.toContinuousLinearMap.comp (res cover a)

theorem resEuclidean_represented (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v) :
    (fun y => (resEuclidean cover a v :
      Lp (EuclideanSpace ℂ (Fin (3 * d F))) 2 a.liftedMeasure) y) =ᵐ[a.liftedMeasure]
      (fun y => coefficientReindex (F := F) (localCoefficient a r.val y)) := by
  let L := (coefficientReindex (F := F)).toContinuousLinearEquiv.toContinuousLinearMap
  have hres := res_represented cover a v r hr
  have heq := L.coeFn_compLp (res cover a v).val
  filter_upwards [heq, hres] with y hy hz
  change L.compLp (res cover a v).val y = _
  rw [hy, hz]
  rfl

theorem resEuclidean_norm (v : IntrinsicHilbert cover) :
    ‖resEuclidean cover a v‖ = ‖res cover a v‖ := by
  exact LinearIsometryEquiv.norm_map (reindexQ a) (res cover a v)

end DedekindZetaZeroFree.KPContActualCotangentChartRestriction

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking KPContActualCotangentMeasurableFamilies
open KPContActualCotangentIntrinsicHilbertIntegral KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy

end DedekindZetaZeroFree

end
