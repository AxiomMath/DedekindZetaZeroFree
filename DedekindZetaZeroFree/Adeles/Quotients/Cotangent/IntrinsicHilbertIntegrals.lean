module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.HilbertPieceReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentIntrinsicHilbertIntegral

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum
open KPContActualCotangentPieceExtraction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (cover : CountableCover F ζ hζ U R P H)

def IntrinsicHilbert (_cover : CountableCover F ζ hζ U R P H) :=
  CotangentAeQuotient (U := U) (H := H)

instance intrinsicAddCommGroup : AddCommGroup (IntrinsicHilbert cover) :=
  inferInstanceAs (AddCommGroup (CotangentAeQuotient (U := U) (H := H)))

instance intrinsicModule : Module ℂ (IntrinsicHilbert cover) :=
  inferInstanceAs (Module ℂ (CotangentAeQuotient (U := U) (H := H)))

def intrinsicClass : IntrinsicHilbert cover ≃ₗ[ℂ] CotangentAeQuotient (U := U) (H := H) :=
  LinearEquiv.refl ℂ (CotangentAeQuotient (U := U) (H := H))

def realizationEquiv : PieceHilbert cover ≃ₗ[ℂ] IntrinsicHilbert cover :=
  KPContActualCotangentPieceReconstruction.equiv cover

instance intrinsicNormedAddCommGroup : NormedAddCommGroup (IntrinsicHilbert cover) :=
  NormedAddCommGroup.induced _ _ (realizationEquiv cover).symm
    (realizationEquiv cover).symm.injective

instance intrinsicNormedSpace : NormedSpace ℂ (IntrinsicHilbert cover) :=
  NormedSpace.induced ℂ _ _ (realizationEquiv cover).symm

instance intrinsicInnerProductSpace : InnerProductSpace ℂ (IntrinsicHilbert cover) :=
  InnerProductSpace.induced (realizationEquiv cover).symm

instance intrinsicCompleteSpace : CompleteSpace (IntrinsicHilbert cover) :=
  let e : PieceHilbert cover ≃ₗᵢ[ℂ] IntrinsicHilbert cover :=
    { realizationEquiv cover with
      norm_map' := fun x => by
        show ‖(realizationEquiv cover).symm (realizationEquiv cover x)‖ = ‖x‖
        rw [LinearEquiv.symm_apply_apply] }
  e.toIsometryEquiv.symm.completeSpace

def realizationIsometry : PieceHilbert cover ≃ₗᵢ[ℂ] IntrinsicHilbert cover where
  __ := realizationEquiv cover
  norm_map' := fun x => by
    show ‖(realizationEquiv cover).symm (realizationEquiv cover x)‖ = ‖x‖
    rw [LinearEquiv.symm_apply_apply]

theorem realizationIsometry_toLinearEquiv :
    (realizationIsometry cover).toLinearEquiv = realizationEquiv cover := by
  rfl

theorem norm_eq_extraction (v : IntrinsicHilbert cover) :
    ‖v‖ = ‖Ext cover (intrinsicClass cover v)‖ := by
  show ‖(realizationEquiv cover).symm v‖ = ‖Ext cover v‖
  rfl

theorem inner_eq_extraction (v w : IntrinsicHilbert cover) :
    inner ℂ v w = inner ℂ (Ext cover (intrinsicClass cover v))
      (Ext cover (intrinsicClass cover w)) := by
  show inner ℂ ((realizationEquiv cover).symm v) ((realizationEquiv cover).symm w) =
    inner ℂ (Ext cover v) (Ext cover w)
  rfl

private theorem q_coordinates (a : ShrunkChart F ζ hζ U R P H) (y : a.domain) :
    KPContCotangentOverlapRationalBranches.q a
      (KPContActualCotangentPieceHilbertSum.coordinates a y).val = a.toBase y := by
  have h : KPContCotangentActualOverlap.labeledA
      (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
      (KPContCotangentActualOverlap.labeledAInv
        (KPContCotangentActualOverlap.placeEquiv F ζ hζ) y.val) = y.val := by
    funext k; simp [KPContCotangentActualOverlap.labeledA,
      KPContCotangentActualOverlap.labeledAInv]
  simp only [KPContCotangentOverlapRationalBranches.q, ShrunkChart.toBase,
    KPContActualCotangentPieceHilbertSum.coordinates, Subtype.coe_mk, h]

private theorem ofReal_norm_inner_le
    (u v : KPContActualCotangentMeasurableFamilies.Coefficients F) :
    ENNReal.ofReal ‖inner ℂ u v‖ ≤
      ENNReal.ofReal ((‖u‖₊ ^ 2 : NNReal) : ℝ) +
        ENNReal.ofReal ((‖v‖₊ ^ 2 : NNReal) : ℝ) := by
  have hreal : ‖inner ℂ u v‖ ≤
      ((‖u‖₊ ^ 2 : NNReal) : ℝ) + ((‖v‖₊ ^ 2 : NNReal) : ℝ) := by
    simp only [NNReal.coe_pow, coe_nnnorm]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) u v
    have h3 : ‖u‖ * ‖v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      nlinarith [two_mul_le_add_sq ‖u‖ ‖v‖, norm_nonneg u, norm_nonneg v]
    linarith
  calc ENNReal.ofReal ‖inner ℂ u v‖
      ≤ ENNReal.ofReal (((‖u‖₊ ^ 2 : NNReal) : ℝ) + ((‖v‖₊ ^ 2 : NNReal) : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((‖u‖₊ ^ 2 : NNReal) : ℝ) +
        ENNReal.ofReal ((‖v‖₊ ^ 2 : NNReal) : ℝ) :=
        ENNReal.ofReal_add (by positivity) (by positivity)

theorem integrable_pair (r s : SquareFiniteFamily (U := U) (H := H)) :
    Integrable (pair r.val s.val) (baseMeasure (R := R) (P := P) (U := U)) := by
  classical
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  have hBR := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hmeas : Measurable
      (fun x => ENNReal.ofReal (normSquare r.val x : ℝ)) :=
    ((measurable_normSquare r.val).coe_nnreal_real).ennreal_ofReal
  refine ⟨(measurable_pair r.val s.val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hbound : ∀ x : KPFiniteCuspAtlas.rawXU F ζ hζ U,
      ENNReal.ofReal ‖pair r.val s.val x‖ ≤
        ENNReal.ofReal (normSquare r.val x : ℝ) +
          ENNReal.ofReal (normSquare s.val x : ℝ) := by
    intro x
    have hmem : x ∈ ⋃ n, KPContActualCotangentBorelRefinement.basePiece cover n := by
      rw [hBR.covers]; exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨y, hy⟩ := Set.mem_range.mp (hBR.base_subset n hn)
    have hq : KPContCotangentOverlapRationalBranches.q (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y).val = x := by
      rw [q_coordinates (cover.chart n) y, hy]
    rw [← hq]
    rw [pair_chart r.val s.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y),
      normSquare_chart r.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y),
      normSquare_chart s.val (cover.chart n)
        (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) y)]
    exact ofReal_norm_inner_le _ _
  calc (∫⁻ x, ENNReal.ofReal ‖pair r.val s.val x‖
        ∂(baseMeasure (R := R) (P := P) (U := U)))
      ≤ ∫⁻ x, (ENNReal.ofReal (normSquare r.val x : ℝ) +
          ENNReal.ofReal (normSquare s.val x : ℝ))
        ∂(baseMeasure (R := R) (P := P) (U := U)) := lintegral_mono hbound
    _ = (∫⁻ x, ENNReal.ofReal (normSquare r.val x : ℝ)
          ∂(baseMeasure (R := R) (P := P) (U := U))) +
        (∫⁻ x, ENNReal.ofReal (normSquare s.val x : ℝ)
          ∂(baseMeasure (R := R) (P := P) (U := U))) :=
        lintegral_add_left hmeas _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨r.property, s.property⟩

theorem integrable_normSquare (r : SquareFiniteFamily (U := U) (H := H)) :
    Integrable (fun x => (normSquare r.val x : ℝ))
      (baseMeasure (R := R) (P := P) (U := U)) := by
  refine ⟨((measurable_normSquare r.val).coe_nnreal_real).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofNNReal]
  have h : (∫⁻ x, ENNReal.ofReal ((normSquare r.val x : ℝ))
      ∂(baseMeasure (R := R) (P := P) (U := U))) < ⊤ := r.property
  simpa only [ENNReal.ofReal_coe_nnreal] using h

private theorem piece_inner_eq (cover : CountableCover F ζ hζ U R P H)
    (r s : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    inner ℂ (component cover r n) (component cover s n) =
      ∫ y in KPContActualCotangentBorelRefinement.liftedPiece cover n,
        pair r.val s.val ((cover.chart n).toBase y) ∂(cover.chart n).liftedMeasure := by
  have hmeas :=
    (kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).lifted_measurable n
  change inner ℂ ((component cover r n : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 (cover.chart n).liftedMeasure))
      ((component cover s n : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 (cover.chart n).liftedMeasure)) =
    ∫ y in KPContActualCotangentBorelRefinement.liftedPiece cover n,
      pair r.val s.val ((cover.chart n).toBase y) ∂(cover.chart n).liftedMeasure
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x => inner ℂ
        ((component cover r n : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 (cover.chart n).liftedMeasure) x)
        ((component cover s n : Lp (KPContCotangentActualGenuineTwistIsotropy.E F) 2 (cover.chart n).liftedMeasure) x)) =ᵐ[
      (cover.chart n).liftedMeasure]
      (fun x => inner ℂ (KPContActualCotangentPieceExtraction.e cover r.val n x)
        (KPContActualCotangentPieceExtraction.e cover s.val n x)) := by
    filter_upwards [(memLp_e cover r.val r.property n).coeFn_toLp,
      (memLp_e cover s.val s.property n).coeFn_toLp] with x hx hy
    simp only [pieceLp, component]
    rw [hx, hy]
  rw [integral_congr_ae hae]
  have hind : ∀ x, inner ℂ (KPContActualCotangentPieceExtraction.e cover r.val n x)
        (KPContActualCotangentPieceExtraction.e cover s.val n x) =
      (KPContActualCotangentBorelRefinement.liftedPiece cover n).indicator
        (fun y => inner ℂ (localCoefficient cover r.val n y)
          (localCoefficient cover s.val n y)) x := by
    intro x
    by_cases hx : x ∈ KPContActualCotangentBorelRefinement.liftedPiece cover n
    · rw [Set.indicator_of_mem hx]
      simp only [KPContActualCotangentPieceExtraction.e, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      simp only [KPContActualCotangentPieceExtraction.e, Set.indicator_of_notMem hx,
        inner_zero_left]
  rw [integral_congr_ae (Filter.Eventually.of_forall hind), integral_indicator hmeas]
  exact setIntegral_congr_fun hmeas fun x _ => by
    rw [← q_coordinates (cover.chart n) x, pair_chart r.val s.val (cover.chart n)
      (KPContActualCotangentPieceHilbertSum.coordinates (cover.chart n) x)]
    rfl

set_option maxHeartbeats 1600000 in

theorem inner_eq_integral (v w : IntrinsicHilbert cover)
    (r s : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v)
    (hs : toAeQuotient s = intrinsicClass cover w) :
    inner ℂ v w = ∫ x, pair r.val s.val x
      ∂(baseMeasure (R := R) (P := P) (U := U)) := by
  classical
  obtain ⟨-, -, -, -, -, -, hG⟩ :=
    kp_cont_actual_cotangent_piece_extraction F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H
      cover
  have hExt_r : Ext cover (toAeQuotient r) = extractFamily cover r := by
    apply lp.ext; funext n; rw [hG r n]; rfl
  have hExt_s : Ext cover (toAeQuotient s) = extractFamily cover s := by
    apply lp.ext; funext n; rw [hG s n]; rfl
  have hBR := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  rw [inner_eq_extraction cover v w, ← hr, ← hs, hExt_r, hExt_s,
    inner_eq_tsum cover (extractFamily cover r) (extractFamily cover s)]
  rw [show (∑' n, inner ℂ ((extractFamily cover r) n) ((extractFamily cover s) n)) =
      ∑' n, ∫ y in KPContActualCotangentBorelRefinement.liftedPiece cover n,
        pair r.val s.val ((cover.chart n).toBase y) ∂(cover.chart n).liftedMeasure
      from tsum_congr fun n => piece_inner_eq cover r s n]
  rw [← hBR.integral_eq_tsum (pair r.val s.val) (integrable_pair r s)]

theorem norm_sq_eq_integral (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hr : toAeQuotient r = intrinsicClass cover v) :
    ‖v‖ ^ 2 = ∫ x, (normSquare r.val x : ℝ)
      ∂(baseMeasure (R := R) (P := P) (U := U)) := by
  classical
  obtain ⟨-, -, hC, -, -, -, hG⟩ :=
    kp_cont_actual_cotangent_piece_extraction F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H
      cover
  have hExt : Ext cover (toAeQuotient r) = extractFamily cover r := by
    apply lp.ext
    funext n
    rw [hG r n]
    rfl
  have hnorm : ‖v‖ = ‖extractFamily cover r‖ := by
    rw [norm_eq_extraction cover v, ← hr, hExt]
  have hsum : ‖extractFamily cover r‖ ^ 2 = ∑' n, ‖component cover r n‖ ^ 2 :=
    norm_sq_eq_tsum cover (extractFamily cover r)
  have hpt : ∀ n, ((‖component cover r n‖₊ ^ 2 : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal (‖component cover r n‖ ^ 2) := by
    intro n
    have h2 : ((‖component cover r n‖₊ ^ 2 : NNReal) : ℝ) = ‖component cover r n‖ ^ 2 := by
      rw [NNReal.coe_pow, coe_nnnorm]
    rw [← h2, ENNReal.ofReal_coe_nnreal]
  have hsumm : Summable (fun n => (‖component cover r n‖₊ ^ 2 : NNReal)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable, tsum_congr hpt]
    exact (hC r).2.1.ne
  have hcoe : (↑(∑' n, (‖component cover r n‖₊ ^ 2 : NNReal)) : ℝ≥0∞) =
      ∑' n, ENNReal.ofReal (‖component cover r n‖ ^ 2) := by
    rw [ENNReal.coe_tsum hsumm]
    exact tsum_congr hpt
  have hofReal : ENNReal.ofReal (∑' n, ‖component cover r n‖ ^ 2) =
      (↑(∑' n, (‖component cover r n‖₊ ^ 2 : NNReal)) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := ∑' n, (‖component cover r n‖₊ ^ 2 : NNReal))]
    congr 1
    rw [NNReal.coe_tsum]
    exact tsum_congr fun n => by rw [NNReal.coe_pow, coe_nnnorm]
  have hint : Integrable (fun x => (normSquare r.val x : ℝ))
      (baseMeasure (R := R) (P := P) (U := U)) := KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare r
  have key : ENNReal.ofReal (‖v‖ ^ 2) =
      ENNReal.ofReal (∫ x, (normSquare r.val x : ℝ)
        ∂(baseMeasure (R := R) (P := P) (U := U))) := by
    rw [hnorm, hsum, hofReal, hcoe, (hC r).1,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity)]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (integral_nonneg fun x => by positivity)).mp key

def changeCover (other : CountableCover F ζ hζ U R P H) :
    IntrinsicHilbert cover ≃ₗᵢ[ℂ] IntrinsicHilbert other where
  __ := (intrinsicClass cover).trans (intrinsicClass other).symm
  norm_map' := fun v => by
    obtain ⟨r, hr⟩ := toAeQuotient_surjective (U := U) (H := H) v
    have h1 := KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral cover v r hr
    have h2 := KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral other
      (((intrinsicClass cover).trans (intrinsicClass other).symm) v) r (by rw [hr]; rfl)
    have hsq : ‖((intrinsicClass cover).trans (intrinsicClass other).symm) v‖ ^ 2 =
        ‖v‖ ^ 2 := by rw [h2, h1]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hsq

theorem changeCover_class (other : CountableCover F ζ hζ U R P H)
    (v : IntrinsicHilbert cover) :
    intrinsicClass other (changeCover cover other v) = intrinsicClass cover v := by
  rfl

theorem scalarSector_isClosed :
    IsClosed (KPContSectorClosedLpSubspace.H F ζ hζ R U :
      Set (KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)) :=
  KPContSectorClosedLpSubspace.H_isClosed F ζ hζ R U

structure Properties : Prop where
  reconstruction_isometry :
    (realizationIsometry cover).toLinearEquiv = realizationEquiv cover
  extraction_norm : ∀ v : IntrinsicHilbert cover,
    ‖v‖ = ‖Ext cover (intrinsicClass cover v)‖
  extraction_inner : ∀ v w : IntrinsicHilbert cover,
    inner ℂ v w = inner ℂ (Ext cover (intrinsicClass cover v))
      (Ext cover (intrinsicClass cover w))
  pairing_integrable : ∀ r s : SquareFiniteFamily (U := U) (H := H),
    Integrable (pair r.val s.val) (baseMeasure (R := R) (P := P) (U := U))
  square_integrable : ∀ r : SquareFiniteFamily (U := U) (H := H),
    Integrable (fun x => (normSquare r.val x : ℝ))
      (baseMeasure (R := R) (P := P) (U := U))
  inner_integral : ∀ (v w : IntrinsicHilbert cover)
    (r s : SquareFiniteFamily (U := U) (H := H)),
    toAeQuotient r = intrinsicClass cover v →
    toAeQuotient s = intrinsicClass cover w →
    inner ℂ v w = ∫ x, pair r.val s.val x
      ∂(baseMeasure (R := R) (P := P) (U := U))
  norm_integral : ∀ (v : IntrinsicHilbert cover)
    (r : SquareFiniteFamily (U := U) (H := H)),
    toAeQuotient r = intrinsicClass cover v →
    ‖v‖ ^ 2 = ∫ x, (normSquare r.val x : ℝ)
      ∂(baseMeasure (R := R) (P := P) (U := U))
  cover_independent : ∀ (other : CountableCover F ζ hζ U R P H)
    (v : IntrinsicHilbert cover),
    intrinsicClass other (changeCover cover other v) = intrinsicClass cover v
  scalar_closed : IsClosed (KPContSectorClosedLpSubspace.H F ζ hζ R U :
    Set (KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U))

end DedekindZetaZeroFree.KPContActualCotangentIntrinsicHilbertIntegral

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_intrinsic_hilbert_integral
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentIntrinsicHilbertIntegral.Properties cover :=
  { reconstruction_isometry := KPContActualCotangentIntrinsicHilbertIntegral.realizationIsometry_toLinearEquiv cover
    extraction_norm := KPContActualCotangentIntrinsicHilbertIntegral.norm_eq_extraction cover
    extraction_inner := KPContActualCotangentIntrinsicHilbertIntegral.inner_eq_extraction cover
    pairing_integrable := KPContActualCotangentIntrinsicHilbertIntegral.integrable_pair
    square_integrable := KPContActualCotangentIntrinsicHilbertIntegral.integrable_normSquare
    inner_integral := KPContActualCotangentIntrinsicHilbertIntegral.inner_eq_integral cover
    norm_integral := KPContActualCotangentIntrinsicHilbertIntegral.norm_sq_eq_integral cover
    cover_independent := KPContActualCotangentIntrinsicHilbertIntegral.changeCover_class cover
    scalar_closed := KPContActualCotangentIntrinsicHilbertIntegral.scalarSector_isClosed }

end DedekindZetaZeroFree

end
