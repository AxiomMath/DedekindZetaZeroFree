module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CubicPowerPushforward
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

open scoped Valued Topology ENNReal WithZeroTopology
open MeasureTheory
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
open KPLocalPrincipalSeries
noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
private lemma no_atoms (μ : Measure K) [μ.IsAddHaarMeasure] : NullSingletonClass μ := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance
private lemma units_borel : BorelSpace Kˣ := by
  constructor
  unfold Units.instMeasurableSpace
  rw [‹BorelSpace K›.measurable_eq, ← borel_comap]
  rw [← (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced]
private lemma haar (μ : Measure K) [μ.IsAddHaarMeasure] : (KPCubicHaar.multiplicativeHaar K μ).IsHaarMeasure := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hc : IsCompact (KPCubicUnitIndices.Integers K : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have ho : IsOpen (KPCubicUnitIndices.Integers K : Set K) := Valued.isOpen_integer K
  have hp : 0 < μ (KPCubicUnitIndices.Integers K : Set K) :=
    ho.measure_pos (μ := μ) ⟨0, by simp⟩
  exact (kp_rankone_cubic_haar_power_measure K μ _
    (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1
private lemma abs_measurable : Measurable (KPCubicHaar.abs K) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  apply ContinuousOn.measurable_of_countable_compl (s := ({0} : Set K)ᶜ)
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := by simpa using hx
    have hv : ValuativeRel.valuation K x ≠ 0 := by simpa using hx0
    have he : ∀ᶠ y in 𝓝 x, ValuativeRel.valuation K y = ValuativeRel.valuation K x :=
      (WithZeroTopology.tendsto_of_ne_zero hv).mp
        (IsValuativeTopology.continuous_valuation.continuousAt :
          ContinuousAt (ValuativeRel.valuation K) x)
    apply (continuousAt_const (y := KPCubicHaar.abs K x)).congr
    filter_upwards [he] with y hy
    have hy0 : y ≠ 0 := by intro h; simp [h] at hy; exact hv hy.symm
    simp [KPCubicHaar.abs, hx0, hy0, hy]
  · simp

theorem inverse_substitution
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (g : K → ℂ) (G : Kˣ → ℂ) (hg : Integrable g μ)
    (hG : ∀ v : Kˣ, g (-((v⁻¹ : Kˣ) : K)) = (KPCubicHaar.abs K (v : K) : ℂ) * G v) :
    Integrable G (KPCubicHaar.multiplicativeHaar K μ) ∧
      (∫ x : K, g x ∂μ) = ∫ v : Kˣ, G v ∂KPCubicHaar.multiplicativeHaar K μ := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := units_borel K
  letI := no_atoms K μ
  letI := haar K μ
  let D : K → ℝ≥0∞ := fun x => ENNReal.ofReal ((KPCubicHaar.abs K x)⁻¹)
  let f : K → ℂ := fun x => (KPCubicHaar.abs K x : ℂ) * g x
  have hD : Measurable D := (abs_measurable K).inv.ennreal_ofReal
  have hc : (fun x => (D x).toReal • f x) =ᵐ[μ] g := by
    filter_upwards [μ.ae_ne 0] with x hx
    have hp := KPCubicHaar.abs_pos K hx
    simp [D, f, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le),
      Complex.real_smul, ← mul_assoc, hp.ne']
  have hf : Integrable f (μ.withDensity D) := by
    apply (integrable_withDensity_iff_integrable_smul' hD (by simp [D])).mpr
    exact hg.congr hc.symm
  have hi : (∫ x, f x ∂μ.withDensity D) = ∫ x, g x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hD (by simp [D])]
    exact integral_congr_ae hc
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hr : μ.restrict (Set.range (Units.val : Kˣ → K)) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [μ.ae_ne 0] with x hx
    exact ⟨Units.mk0 x hx, rfl⟩
  have hmap : Measure.map (Units.val : Kˣ → K) (KPCubicHaar.multiplicativeHaar K μ) =
      μ.withDensity D := by
    change Measure.map Units.val ((μ.withDensity D).comap Units.val) = _
    rw [ev.map_comap, restrict_withDensity ev.measurableSet_range, hr]
  have hF : Integrable (fun v : Kˣ => f (v : K)) (KPCubicHaar.multiplicativeHaar K μ) := by
    exact (ev.integrable_map_iff (g := f)).mp (hmap.symm ▸ hf)
  have hI : (∫ v : Kˣ, f (v : K) ∂KPCubicHaar.multiplicativeHaar K μ) = ∫ x, g x ∂μ := by
    rw [← ev.integral_map, hmap, hi]
  have hneg : KPCubicHaar.abs K (-1 : K) = 1 := by
    have hh : 0 ≤ KPCubicHaar.abs K (-1 : K) := (KPCubicHaar.abs_pos K (by simp)).le
    have he := KPCubicHaar.abs_mul K (-1 : K) (-1 : K)
    simp only [neg_mul_neg, one_mul, KPCubicHaar.abs_one] at he
    nlinarith
  have heq (v : Kˣ) : f ((-v⁻¹ : Kˣ) : K) = G v := by
    have hp := KPCubicHaar.abs_pos K v.ne_zero
    have ha : KPCubicHaar.abs K (-((v⁻¹ : Kˣ) : K)) = (KPCubicHaar.abs K (v : K))⁻¹ := by
      rw [neg_eq_neg_one_mul, KPCubicHaar.abs_mul, hneg, one_mul,
        Units.val_inv_eq_inv_val, KPCubicHaar.abs_inv]
    simp only [f, Units.val_neg, hG, ha, Complex.ofReal_inv]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hp.ne'), one_mul]
  have hinv : (KPCubicHaar.multiplicativeHaar K μ).IsInvInvariant := by
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    haveI : SecondCountableTopology K := inferInstance
    haveI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
    haveI : (KPCubicHaar.multiplicativeHaar K μ).Regular := inferInstance
    infer_instance
  letI := hinv
  have htrans := (hF.comp_mul_left (-1 : Kˣ)).comp_inv
  have htransI := integral_inv_eq_self (fun v : Kˣ => f ((-1 * v : Kˣ) : K))
    (KPCubicHaar.multiplicativeHaar K μ)
  simp only [neg_one_mul] at htrans htransI
  simp only [heq] at htrans htransI
  refine ⟨htrans, ?_⟩
  rw [htransI]
  have hn := integral_mul_left_eq_self (μ := KPCubicHaar.multiplicativeHaar K μ)
    (fun v : Kˣ => f (v : K)) (-1 : Kˣ)
  simpa only [neg_one_mul] using hI.symm.trans hn.symm

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport
