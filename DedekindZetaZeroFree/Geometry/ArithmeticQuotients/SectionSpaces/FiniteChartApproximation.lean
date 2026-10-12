module

public import DedekindZetaZeroFree.Adeles.Quotients.EquivariantSections.CompactTestDescent
public import DedekindZetaZeroFree.Adeles.Quotients.EquivariantSections.FinitePartitionError

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContSectorLineL2Isometry KPContSectorSmoothFramesSupport
open KPContActualCotangentMeasurableFamilies
open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings

private theorem lifted_error_eq
    {α β E V : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {μ : Measure α} {ν : Measure β} (e : E ≃ₗᵢ[ℂ] V)
    {q : α → β} (hq : MeasurePreserving q μ ν)
    (f : Lp V 2 ν) (g : β → V) (hg : MemLp g 2 ν)
    (c : α → E)
    (hc : (fun x => e (c x)) =ᵐ[μ] (fun x => f (q x) - g (q x))) :
    eLpNorm c 2 μ = ‖f - hg.toLp g‖ₑ := by
  have hm := ((Lp.memLp f).sub hg).comp_measurePreserving hq
  have he : c =ᵐ[μ] (fun x => e.symm (f (q x) - g (q x))) := by
    filter_upwards [hc] with x hx
    simpa only [LinearIsometryEquiv.symm_apply_apply] using congrArg e.symm hx
  rw [eLpNorm_congr_ae he]
  have hn := eLpNorm_congr_norm_ae (p := 2)
    (e.symm.continuous.comp_aestronglyMeasurable hm.aestronglyMeasurable)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => e.symm.norm_map _))
  change eLpNorm (fun x => e.symm ((((f : β → V) - g) ∘ q) x)) 2 μ = _
  rw [hn, eLpNorm_comp_measurePreserving
    ((Lp.memLp f).sub hg).aestronglyMeasurable hq, Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub f (hg.toLp g), hg.coeFn_toLp] with x hx hy
  simpa only [Pi.sub_apply, hy] using hx.symm

theorem finite_chart_approximation
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsCompact K) (hKm : MeasurableSet K) (hO : IsOpen O)
    (n : ℕ)
    (C : Fin n → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (partition : KPContActualSectorFiniteSupportPartition.FinitePartition F ζ hζ U R P H C K O)
    (s : BorelL2Sections F ζ hζ U R P H)
    (r : SquareFiniteFamily (U := U) (H := H))
    (hs : ∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → sectionNorm F ζ hζ U R P H s.val b = 0)
    (hr : ∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → normSquare r.val b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : ∀ i : Fin n, localScalarTests (C i))
      (w : ∀ i : Fin n, localCotangentTests (C i)),
      ‖toSector F ζ hζ U R P H s - iota (∑ i, scalarZeroExtension (C i) (f i))‖ < ε ∧
      ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
        j (∑ i, cotangentZeroExtension (C i) (w i))‖ < ε := by
  let A := kp_cont_actual_sector_chart_equivariant_inputs
    F ζ hζ μG hμG U R hR P H realization C K O partition
  let δ := ε / (n + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hn : 1 ≤ 3 * KPContCotangentActualOverlap.d F := by
    have := A.dimension_positive
    omega
  have hscalar : ∀ i : Fin n, ∃ f : localScalarTests (C i),
      eLpNorm (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) *
          ((C i).coefficient s.val y : ℂ) -
          f.val (KPContActualCotangentPieceHilbertSum.coordinates (C i) y))
        2 (C i).liftedMeasure < ENNReal.ofReal δ := by
    intro i
    letI : Fintype (KPContCotangentActualGenuineTwistIsotropy.Gamma (C i)) :=
      Fintype.ofFinite _
    obtain ⟨l, hl, hrep⟩ := A.scalar_localization i (toSector F ζ hζ U R P H s)
    have he : mk F ζ hζ U R P H s =
        sectorLineIsometry F ζ hζ U R P H (toSector F ζ hζ U R P H s) := by
      change mk F ζ hζ U R P H s =
        (lineToSector F ζ hζ U R P H).symm
          ((lineToSector F ζ hζ U R P H) (mk F ζ hζ U R P H s))
      exact ((lineToSector F ζ hζ U R P H).symm_apply_apply _).symm
    obtain ⟨g, hg, hsm, hcomp, hsupp, heq, herr⟩ :=
      kp_cont_chart_equivariant_l2_density _ 1 hn (by omega) _
        (KPContActualSectorChartEquivariantInputs.scalarData (C i)) l hl δ hδ
    obtain ⟨f, hf⟩ := KPContActualCompactEquivariantDescent.scalar (C i) g hsm hcomp hsupp heq
    refine ⟨f, ?_⟩
    have hq : MeasurePreserving
        (fun y : (C i).domain => KPContActualSectorChartEquivariantInputs.fromActual
          (ζ := ζ) (hζ := hζ) y.val)
        (C i).liftedMeasure (KPContActualSectorChartEquivariantInputs.measure (C i)) :=
      ⟨(KPContActualSectorChartEquivariantInputs.baseReindex (F := F)).continuous.comp
        (continuous_subtype_val.comp
          (KPContActualCotangentPieceHilbertSum.coordinates_continuous (C i))) |>.measurable,
        A.exact_measure i⟩
    have hx := lifted_error_eq KPContActualSectorChartEquivariantInputs.scalarReindex hq l g hg
      (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) *
          ((C i).coefficient s.val y : ℂ) -
          f.val (KPContActualCotangentPieceHilbertSum.coordinates (C i) y)) (by
        filter_upwards [hrep s he] with y hy
        rw [map_sub, hf]
        exact congrArg (fun z => z - g (KPContActualSectorChartEquivariantInputs.fromActual
          (ζ := ζ) (hζ := hζ) y.val)) hy.symm)
    rw [hx, ← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr herr
  have htensor : ∀ i : Fin n, ∃ w : localCotangentTests (C i),
      eLpNorm (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) •
          KPContActualCotangentChartRestriction.localCoefficient (C i) r.val y -
          w.val (KPContActualCotangentPieceHilbertSum.coordinates (C i) y))
        2 (C i).liftedMeasure < ENNReal.ofReal δ := by
    intro i
    letI : Fintype (KPContCotangentActualGenuineTwistIsotropy.Gamma (C i)) :=
      Fintype.ofFinite _
    obtain ⟨l, hl, hrep⟩ := A.cotangent_localization i
      (KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r)
    obtain ⟨g, hg, hsm, hcomp, hsupp, heq, herr⟩ :=
      kp_cont_chart_equivariant_l2_density _ _ hn hn _
        (KPContActualSectorChartEquivariantInputs.cotangentData (C i)) l hl δ hδ
    obtain ⟨w, hw⟩ := KPContActualCompactEquivariantDescent.cotangent (C i) g hsm hcomp hsupp heq
    refine ⟨w, ?_⟩
    have hq : MeasurePreserving
        (fun y : (C i).domain => KPContActualSectorChartEquivariantInputs.fromActual
          (ζ := ζ) (hζ := hζ) y.val)
        (C i).liftedMeasure (KPContActualSectorChartEquivariantInputs.measure (C i)) :=
      ⟨(KPContActualSectorChartEquivariantInputs.baseReindex (F := F)).continuous.comp
        (continuous_subtype_val.comp
          (KPContActualCotangentPieceHilbertSum.coordinates_continuous (C i))) |>.measurable,
        A.exact_measure i⟩
    have hx := lifted_error_eq KPContActualCotangentChartRestriction.coefficientReindex hq l g hg
      (fun y : (C i).domain =>
        (partition.multiplier i ((C i).toBase y) : ℂ) •
          KPContActualCotangentChartRestriction.localCoefficient (C i) r.val y -
          w.val (KPContActualCotangentPieceHilbertSum.coordinates (C i) y)) (by
        filter_upwards [hrep r rfl] with y hy
        rw [map_sub, map_smul, hw]
        exact congrArg (fun z => z - g (KPContActualSectorChartEquivariantInputs.fromActual
          (ζ := ζ) (hζ := hζ) y.val)) hy.symm)
    rw [hx, ← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr herr
  choose f hf using hscalar
  choose w hw using htensor
  refine ⟨f, w, ?_, ?_⟩
  · have hb := KPContActualFinitePartitionError.scalar F ζ hζ U R P H K O hK n C partition s hs f
    have he : ENNReal.ofReal ((n : ℝ) * δ) < ENNReal.ofReal ε := by
      apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by nlinarith)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hf i).le)
    have : ENNReal.ofReal ‖toSector F ζ hζ U R P H s -
        iota (∑ i, scalarZeroExtension (C i) (f i))‖ < ENNReal.ofReal ε := by
      rw [ofReal_norm_eq_enorm]
      apply lt_of_le_of_lt (hb.trans hsum)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast] using he
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp this
  · have hb := KPContActualFinitePartitionError.cotangent F ζ hζ U R P H K O hK n C partition r hr w
    have he : ENNReal.ofReal ((n : ℝ) * δ) < ENNReal.ofReal ε := by
      apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
      dsimp [δ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by nlinarith)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hw i).le)
    have : ENNReal.ofReal ‖KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H r -
        j (∑ i, cotangentZeroExtension (C i) (w i))‖ < ENNReal.ofReal ε := by
      rw [ofReal_norm_eq_enorm]
      apply lt_of_le_of_lt (hb.trans hsum)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast] using he
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp this

end DedekindZetaZeroFree.RepresentationTheory.ActualSectorTestDensity

end
