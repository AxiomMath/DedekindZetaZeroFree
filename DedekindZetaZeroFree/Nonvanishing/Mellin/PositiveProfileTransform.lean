module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ProbeAndUniformSection
public import DedekindZetaZeroFree.Theta.Profiles.ThirdBesselMellinTransform

@[expose] public section

noncomputable section
open scoped NumberField Classical ENNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.GaussianSmoothing
open MomentSources ThetaProfileHaarSheets ThetaPositiveSheetMellin
open _root_.DedekindZetaZeroFree renaming radial_integrable → radial_integrable
open _root_.DedekindZetaZeroFree.ThetaPositiveSheetMellin renaming PA → PA
open _root_.DedekindZetaZeroFree.ThetaPositiveSheetMellin renaming polarEquiv → polarEquiv
open _root_.DedekindZetaZeroFree.ThetaPositiveSheetMellin renaming polarEquiv_eq → polarEquiv_eq
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem compact_subgroup_norm_one {K : Type*} [NormedField K]
    (U : Subgroup Kˣ) (hU : IsCompact (U : Set Kˣ)) (z : Kˣ) (hz : z ∈ U) :
    ‖(z : K)‖ = 1 := by
  obtain ⟨a, ha, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩
    (Units.continuous_val.norm.continuousOn)
  have hle (u : Kˣ) (hu : u ∈ U) : ‖(u : K)‖ ≤ 1 := by
    have h := hmax (U.mul_mem hu ha)
    change ‖((u * a : Kˣ) : K)‖ ≤ ‖(a : K)‖ at h
    rw [Units.val_mul, norm_mul] at h
    nlinarith [norm_pos_iff.mpr a.ne_zero]
  have h1 := hle z hz
  have h2 := hle z⁻¹ (U.inv_mem hz)
  have hm : ‖(z : K)‖ * ‖((z⁻¹ : Kˣ) : K)‖ = 1 := by
    rw [← norm_mul]; simp
  nlinarith [norm_nonneg (z : K), norm_nonneg ((z⁻¹ : Kˣ) : K)]

def radial (P : Packet R Q) (y : R.A.G) : ℝ :=
  (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
    ∏ w : InfinitePlace F, thirdBesselRadialProfile (P.scale w) (‖(y.1 w : w.Completion)‖ ^ 2)

def polarC0 (N : TraceHaarTransport R) (P : Packet R Q) : ℝ :=
  (∏ p : R.A.Sf, (N.finiteMultHaar p (P.cutoff p : Set (p.val.adicCompletion F)ˣ)).toReal) *
  (∏ w : InfinitePlace F, (N.angularHaar w Set.univ).toReal) *
    ∏ w : InfinitePlace F, (2 / P.scale w ^ 2)

theorem polarC0_pos (N : TraceHaarTransport R) (P : Packet R Q) : 0 < polarC0 N P := by
  letI := N.finiteMultHaar_isHaar
  letI := N.angularHaar_isHaar
  unfold polarC0
  apply mul_pos
  · apply mul_pos
    · apply Finset.prod_pos
      intro p _
      exact ENNReal.toReal_pos ((P.cutoff_open p).measure_ne_zero _ ⟨1, (P.cutoff p).one_mem⟩)
        (P.cutoff_compact p).measure_ne_top
    · apply Finset.prod_pos
      intro w _
      exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ Set.univ_nonempty)
        isCompact_univ.measure_ne_top
  · exact Finset.prod_pos (fun w _ => div_pos (by norm_num) (sq_pos_of_pos (P.scale_pos w)))

theorem radial_nonneg (P : Packet R Q) (y : R.A.G) : 0 ≤ radial P y := by
  unfold radial
  apply mul_nonneg (by split_ifs <;> norm_num)
  apply Finset.prod_nonneg
  intro w _
  exact (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (y.1 w).ne_zero))
    (KThird_pos _ (mul_pos (P.scale_pos w)
      (Real.sqrt_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr (y.1 w).ne_zero)))))).le

theorem continuous_radial (P : Packet R Q) : Continuous (radial P) := by
  have hi : IsClopen (Set.pi Set.univ
      (fun p : R.A.Sf => (P.cutoff p : Set (p.val.adicCompletion F)ˣ))) :=
    ⟨isClosed_set_pi (fun p _ => (P.cutoff p).isClosed_of_isOpen (P.cutoff_open p)),
      isOpen_set_pi Set.finite_univ (fun p _ => P.cutoff_open p)⟩
  have he : radial P = fun y : R.A.G =>
      (Set.pi Set.univ (fun p => (P.cutoff p : Set _))).indicator (fun _ => (1 : ℝ)) y.2 *
        ∏ w, thirdBesselRadialProfile (P.scale w) (‖(y.1 w : w.Completion)‖ ^ 2) := by
    funext y
    simp [radial, Set.indicator, Set.mem_pi]
  rw [he]
  apply (hi.continuous_indicator continuous_const).comp continuous_snd |>.mul
  apply continuous_finset_prod
  intro w _
  have ht : Continuous (fun y : R.A.G => ‖(y.1 w : w.Completion)‖ ^ 2) :=
    ((Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)).norm).pow 2
  have harg : Continuous (fun y : R.A.G => P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2)) :=
    continuous_const.mul (Real.continuous_sqrt.comp ht)
  exact ht.mul (KThird_continuousOn.comp_continuous harg (fun y =>
    mul_pos (P.scale_pos w) (Real.sqrt_pos.mpr
      (sq_pos_of_pos (norm_pos_iff.mpr (y.1 w).ne_zero)))))

lemma axis_radial_integrable (c : ℝ) (hc : 0 < c) (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    Integrable (fun t : PositiveAxis => (thirdBesselRadialProfile c t.val : ℂ) * (t.val : ℂ)^s)
      positiveHaar := by
  let g := fun t : ℝ => (thirdBesselRadialProfile c t : ℂ) * (t : ℂ)^s
  change Integrable (g ∘ Subtype.val) positiveHaar
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  rw [← he.integrable_map_iff,
    positiveHaar_map_val, restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hi := radial_integrable c hc s hs
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [g, ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le),
    Complex.real_smul, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma axis_radial_mellin (c : ℝ) (hc : 0 < c) (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    (∫ t : PositiveAxis, (thirdBesselRadialProfile c t.val : ℂ) * (t.val : ℂ)^s ∂positiveHaar) =
      (2 / c^2 : ℝ) * (4 / c^2 : ℝ)^ (s : ℂ) * Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6) := by
  have he : MeasurableEmbedding (Subtype.val : PositiveAxis → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  rw [← he.integral_map (g := fun t : ℝ => (thirdBesselRadialProfile c t : ℂ) * (t : ℂ)^s),
    positiveHaar_map_val, restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  convert thirdBesselRadialProfile_mellin c hc s hs using 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le), smul_eq_mul, Complex.real_smul]
  ring

lemma norm_sq_sqrtUnit (A : SArithmeticData F) (w : InfinitePlace F) (x : PositiveAxis) :
    ‖(sqrtUnit A w x : w.Completion)‖ ^ 2 = x.val := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq
    (sqrtUnit A w x : w.Completion) 0
  have he : InfinitePlace.Completion.extensionEmbedding w (sqrtUnit A w x : w.Completion) =
      (Real.sqrt x.val : ℂ) := by
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm
        (Real.sqrt x.val : ℂ)) = _
    exact RingEquiv.apply_symm_apply _ _
  simp only [map_zero, dist_zero_right, he] at h
  rw [← h]
  simp [abs_of_pos (Real.sqrt_pos.mpr x.property), Real.sq_sqrt x.property.le]

lemma polarUnit_norm_sq (A : SArithmeticData F) (w : InfinitePlace F) (p : PositiveAxis × Circle) :
    ‖(polarUnit A w p : w.Completion)‖ ^ 2 = p.1.val := by
  rw [polarUnit, Units.val_mul, norm_mul, mul_pow, norm_sq_sqrtUnit]
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq
    ((Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (A.complex_place w)).symm.toMonoidHom p.2.toUnits : w.Completionˣ) : w.Completion) 0
  have he : InfinitePlace.Completion.extensionEmbedding w
      ((Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (A.complex_place w)).symm.toMonoidHom p.2.toUnits : w.Completionˣ) : w.Completion) = (p.2 : ℂ) := by
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm (p.2 : ℂ)) = _
    exact RingEquiv.apply_symm_apply _ _
  simp only [map_zero, dist_zero_right, he, Circle.norm_coe] at h
  rw [← h]; simp

lemma arch_integrable (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [ν.IsHaarMeasure] (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    Integrable (fun z : w.Completionˣ =>
      (thirdBesselRadialProfile c (‖(z : w.Completion)‖ ^ 2) : ℂ) *
        ((‖(z : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s) (archHaar A w ν) := by
  have hp : polarUnit A w = polarEquiv A w := funext (fun p => (polarEquiv_eq A w p).symm)
  unfold archHaar
  rw [hp]
  apply (polarEquiv A w).toHomeomorph.measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun p : PA × Circle =>
    (thirdBesselRadialProfile c (‖(polarEquiv A w p : w.Completion)‖ ^ 2) : ℂ) *
      ((‖(polarEquiv A w p : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s) _
  simp_rw [polarEquiv_eq, polarUnit_norm_sq]
  exact (axis_radial_integrable c hc s hs).comp_fst (ν := ν)

lemma arch_mellin (A : SArithmeticData F) (w : InfinitePlace F)
    (ν : Measure Circle) [ν.IsHaarMeasure] (c : ℝ) (hc : 0 < c)
    (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    (∫ z : w.Completionˣ, (thirdBesselRadialProfile c (‖(z : w.Completion)‖ ^ 2) : ℂ) *
      ((‖(z : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s ∂archHaar A w ν) =
      (ν Set.univ).toReal * (2 / c^2 : ℝ) * (4 / c^2 : ℝ)^(s : ℂ) *
        (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6)) := by
  have hp : polarUnit A w = polarEquiv A w := funext (fun p => (polarEquiv_eq A w p).symm)
  unfold archHaar
  rw [hp]
  have ht : (⇑(polarEquiv A w)) = ⇑(polarEquiv A w).toHomeomorph := rfl
  rw [ht, (polarEquiv A w).toHomeomorph.measurableEmbedding.integral_map]
  change (∫ p : PA × Circle,
    (thirdBesselRadialProfile c (‖(polarEquiv A w p : w.Completion)‖ ^ 2) : ℂ) *
      ((‖(polarEquiv A w p : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s ∂_) = _
  simp_rw [polarEquiv_eq, polarUnit_norm_sq]
  change (∫ p : PA × Circle, (fun t : PA =>
    (thirdBesselRadialProfile c t.val : ℂ) * (t.val : ℂ)^s) p.1 ∂_) = _
  rw [integral_fun_fst (μ := positiveHaar) (ν := ν)
    (fun t : PA => (thirdBesselRadialProfile c t.val : ℂ) * (t.val : ℂ)^s),
    axis_radial_mellin c hc s hs]
  simp only [smul_eq_mul, Complex.real_smul, measureReal_def]
  ring

private lemma ofReal_prod_cpow {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (s : ℂ) :
    ((∏ i ∈ t, a i : ℝ) : ℂ)^s = ∏ i ∈ t, (a i : ℂ)^s := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ha i) (Finset.prod_nonneg (fun j _ => ha j)),
      ih, Finset.prod_insert hi]

theorem global_mellin (N : TraceHaarTransport R) (P : Packet R Q)
    (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    Integrable (fun y : R.A.G => (radial P y : ℂ) * (R.A.norm y : ℂ)^s) N.groupHaar ∧
    (∫ y : R.A.G, (radial P y : ℂ) * (R.A.norm y : ℂ)^s ∂N.groupHaar) =
      (polarC0 N P : ℂ) * (P.A₀ : ℂ)^s *
        (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))^Fintype.card (InfinitePlace F) := by
  letI := N.finiteMultHaar_isHaar
  letI := N.angularHaar_isHaar
  let a := fun z : ((w : InfinitePlace F) → w.Completionˣ) => ∏ w,
    (thirdBesselRadialProfile (P.scale w) (‖(z w : w.Completion)‖ ^ 2) : ℂ) *
      ((‖(z w : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s
  let b := fun z : ((p : R.A.Sf) → (p.val.adicCompletion F)ˣ) => ∏ p,
    (P.cutoff p : Set _).indicator (fun _ => (1 : ℂ)) (z p)
  have heq (y : R.A.G) : (radial P y : ℂ) * (R.A.norm y : ℂ)^s = a y.1 * b y.2 := by
    by_cases hmem : ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p
    · have hb : b y.2 = 1 := Finset.prod_eq_one (fun p _ => Set.indicator_of_mem (hmem p) _)
      have hfin : (∏ p : R.A.Sf, ‖(y.2 p : p.val.adicCompletion F)‖) = 1 :=
        Finset.prod_eq_one (fun p _ => compact_subgroup_norm_one _ (P.cutoff_compact p) _ (hmem p))
      simp only [radial, if_pos hmem, one_mul, SArithmeticData.norm, hfin, mul_one, hb]
      rw [ofReal_prod_cpow]
      · simp [a, Finset.prod_mul_distrib, Complex.ofReal_prod]
      · intro w; positivity
    · obtain ⟨p, hp⟩ := not_forall.mp hmem
      have hb : b y.2 = 0 := Finset.prod_eq_zero (Finset.mem_univ p) (Set.indicator_of_notMem hp _)
      rw [radial, if_neg hmem, zero_mul, Complex.ofReal_zero, zero_mul, hb, mul_zero]
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (R.A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ p : R.A.Sf, TopologicalSpace.SeparableSpace (p.val.adicCompletion F) :=
    fun p => TopologicalSpace.SeparableSpace.of_denseRange _ (p.val.denseRange_algebraMap F)
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F) := fun p => inferInstance
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ w : InfinitePlace F, LocallyCompactSpace w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (R.A.complex_place w)).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have ha : Integrable a (Measure.pi (fun w => archHaar R.A w (N.angularHaar w))) :=
    Integrable.fintype_prod_dep (fun w => arch_integrable R.A w _ _ (P.scale_pos w) s hs)
  have hb : Integrable b (Measure.pi N.finiteMultHaar) := by
    apply Integrable.fintype_prod_dep
    intro p
    exact (integrable_indicator_iff (P.cutoff_open p).measurableSet).mpr
      (integrableOn_const (C := (1 : ℂ)) (μ := N.finiteMultHaar p) (P.cutoff_compact p).measure_ne_top)
  rw [N.polar_transport]
  unfold productHaar
  rw [groupMeasurableSpace_eq_prod R.A, Measure.map_id']
  simp_rw [heq]
  refine ⟨ha.mul_prod hb, ?_⟩
  rw [integral_prod_mul]
  unfold a b
  rw [integral_fintype_prod_eq_prod (fun (w : InfinitePlace F) (z : w.Completionˣ) =>
      (thirdBesselRadialProfile (P.scale w) (‖(z : w.Completion)‖ ^ 2) : ℂ) *
        ((‖(z : w.Completion)‖ ^ 2 : ℝ) : ℂ)^s),
    integral_fintype_prod_eq_prod (fun (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ) =>
      (P.cutoff p : Set _).indicator (fun _ => (1 : ℂ)) z)]
  simp_rw [arch_mellin R.A _ _ _ (P.scale_pos _) s hs,
    integral_indicator_const (μ := N.finiteMultHaar _) (1 : ℂ) (P.cutoff_open _).measurableSet]
  simp only [measureReal_def, Complex.real_smul, mul_one]
  unfold polarC0 Packet.A₀
  rw [ofReal_prod_cpow _ _ (fun w => (div_pos (by norm_num) (sq_pos_of_pos (P.scale_pos w))).le)]
  simp only [Complex.ofReal_mul, Complex.ofReal_prod]
  rw [← Finset.card_univ,
    ← Finset.prod_const (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))]
  simp only [Finset.prod_mul_distrib]
  ring
end DedekindZetaZeroFree.GaussianSmoothing

end
