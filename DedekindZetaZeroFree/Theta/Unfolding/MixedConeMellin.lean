module

public import DedekindZetaZeroFree.Theta.Unfolding.MixedConeMellinSummability
public import DedekindZetaZeroFree.Theta.Unfolding.UnitSlabRadialAngularIntegration

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.Theta
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

/-!
The change-of-variables and unit-slab helpers below adapt proof code from
LeanPool/lean-pool, commit 68aa6ee63d20ad76bcc15f595adfc72949991f06,
`CompletedZeta/ConeGaussianRadial.lean` and `IdealThetaUnfolding.lean`.
Copyright (c) 2026 The FLT Project. Released under Apache 2.0;
see `DedekindZetaZeroFree/LICENSE`.
-/

def mixedConeRadialKernel (x : K) (s : ℂ) (y : realSpace K) : ℂ :=
  (mixedRadialJacobian K y : ℂ) * mixedMellinGaussian K x s (expMapBasis y)

private theorem mixedCone_expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) =
      Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Ioi (0 : ℝ)) := by
  ext q
  constructor
  · rintro ⟨x, -, rfl⟩
    exact Set.mem_univ_pi.mpr fun w ↦ expMapBasis_pos x w
  · intro hq
    have htarget : q ∈ expMapBasis.target := hq
    exact ⟨expMapBasis.symm q, Set.mem_univ _, expMapBasis.right_inv htarget⟩

private theorem mixedCone_pi_restrict :
    Measure.pi (fun _ : InfinitePlace K ↦ (volume : Measure ℝ).restrict (Set.Ioi 0)) =
      (volume : Measure (realSpace K)).restrict
        (Set.univ.pi (fun _ : InfinitePlace K ↦ Set.Ioi (0 : ℝ))) := by
  rw [← Measure.restrict_pi_pi, ← MeasureTheory.volume_pi]

theorem integral_mixedConeRadialKernel (x : K) (s : ℂ) :
    (∫ y : realSpace K, mixedConeRadialKernel K x s y) =
      ∫ q : realSpace K, mixedMellinGaussian K x s q
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ]
  symm
  convert setIntegral_expMapBasis_image (K := K) MeasurableSet.univ
    (mixedMellinGaussian K x s) using 1
  simp only [MeasureTheory.setIntegral_univ, mixedConeRadialKernel,
    mixedRadialJacobian, smul_eq_mul, Complex.real_smul,
    mul_comm (b := (Module.finrank ℚ K : ℝ))]

theorem integrable_mixedConeRadialKernel {x : K} (hx : x ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : Integrable (mixedConeRadialKernel K x s) := by
  have h := integrable_mixedMellinGaussian K x hx s hs
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ] at h
  have h' := (integrableOn_expMapBasis_image_iff (K := K) MeasurableSet.univ
    (mixedMellinGaussian K x s)).mp h
  change Integrable (fun y ↦ (mixedRadialJacobian K y : ℂ) *
    mixedMellinGaussian K x s (expMapBasis y))
  simpa only [integrableOn_univ, mixedConeRadialKernel, mixedRadialJacobian,
    smul_eq_mul, Complex.real_smul, mul_comm (b := (Module.finrank ℚ K : ℝ))] using h'

theorem integral_norm_mixedConeRadialKernel (x : K) (s : ℂ) :
    (∫ y : realSpace K, ‖mixedConeRadialKernel K x s y‖) =
      ∫ q : realSpace K, ‖mixedMellinGaussian K x s q‖
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  classical
  rw [mixedCone_pi_restrict, ← mixedCone_expMapBasis_image_univ]
  symm
  convert setIntegral_expMapBasis_image (K := K) MeasurableSet.univ
    (fun q ↦ ‖mixedMellinGaussian K x s q‖) using 1
  simp only [setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with y
  have hprod : 0 < ∏ v : {v : InfinitePlace K // IsComplex v}, expMapBasis y v.1 :=
    Finset.prod_pos fun _ _ ↦ expMapBasis_pos _ _
  have hreg := Units.regulator_pos K
  have hpos : 0 ≤ mixedRadialJacobian K y := by
    unfold mixedRadialJacobian
    positivity
  rw [mixedConeRadialKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hpos]
  simp only [smul_eq_mul, mixedRadialJacobian,
    mul_comm (b := (Module.finrank ℚ K : ℝ))]

theorem mixedConeRadialKernel_add_unitCoordinateShift
    (x : K) (s : ℂ) (y : realSpace K) (z : unitShiftIndex K) :
    mixedConeRadialKernel K x s (y + unitCoordinateShift z) =
      mixedConeRadialKernel K
        (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * x) s y := by
  simp only [mixedConeRadialKernel, mixedRadialJacobian_mul_mixedMellinGaussian]
  have hrad : (y + unitCoordinateShift z) Units.dirichletUnitTheorem.w₀ =
      y Units.dirichletUnitTheorem.w₀ := by
    simp [unitCoordinateShift]
  rw [hrad, expMapBasis_add_unitCoordinateShift, mixedGaussian_mul_unit]
  rfl

theorem hasSum_integral_norm_mixedConeRadialKernel_unitSlab
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun z : unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        ‖mixedConeRadialKernel K
          (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * idealSetElement K J a) s y‖)
      (∫ y : realSpace K, ‖mixedConeRadialKernel K (idealSetElement K J a) s y‖) := by
  classical
  let f : realSpace K → ℝ := fun y ↦
    ‖mixedConeRadialKernel K (idealSetElement K J a) s y‖
  have hf : Integrable f :=
    (integrable_mixedConeRadialKernel K (idealSetElement_ne_zero K J a) hs).norm
  have hp := hasSum_integral_iUnion (f := f)
    (fun z : unitShiftIndex K ↦ measurableSet_unitFundamentalTranslate z)
    pairwise_disjoint_unitFundamentalTranslate (by
      rw [iUnion_unitFundamentalTranslate]
      simpa only [integrableOn_univ] using hf)
  have hp' : HasSum (fun z : unitShiftIndex K ↦
      ∫ y in unitFundamentalTranslate z, f y) (∫ y, f y) := by
    simpa only [iUnion_unitFundamentalTranslate, setIntegral_univ] using hp
  refine hp'.congr_fun fun z ↦ ?_
  rw [setIntegral_unitFundamentalTranslate f z]
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  exact congrArg norm (mixedConeRadialKernel_add_unitCoordinateShift K
    (idealSetElement K J a) s y z).symm

theorem summable_prod_integral_norm_mixedConeRadialKernel_unitSlab
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : idealSet K J × unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        ‖mixedConeRadialKernel K
          (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y‖) := by
  classical
  apply (summable_prod_of_nonneg fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _).mpr
  constructor
  · intro a
    exact (hasSum_integral_norm_mixedConeRadialKernel_unitSlab K J a
      (lt_trans zero_lt_one hs)).summable
  · refine (summable_integral_norm_mixedMellinGaussian_idealSet K J hs).congr fun a ↦ ?_
    rw [(hasSum_integral_norm_mixedConeRadialKernel_unitSlab K J a
      (lt_trans zero_lt_one hs)).tsum_eq, integral_norm_mixedConeRadialKernel]

theorem integral_mixedConeRadialKernel_eq_tsum_unitSlab
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ y : realSpace K, mixedConeRadialKernel K x s y) =
      ∑' z : unitShiftIndex K, ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * x) s y := by
  rw [integral_eq_tsum_setIntegral_add_unitCoordinateShift _
    (integrable_mixedConeRadialKernel K hx hs)]
  apply tsum_congr
  intro z
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  exact mixedConeRadialKernel_add_unitCoordinateShift K x s y z

open Classical in
noncomputable def coneIdealElementShapeMap
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  ⟨traceRadialScale K q hq
      (traceEmbedding K (((x : 𝓞 K) : K))),
      (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
        K (FractionalIdeal.mk0 K J) q hq _).2 (by
          rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
          exact ⟨x, x.prop, rfl⟩)⟩

theorem coneIdealElementShapeMap_bijective
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (coneIdealElementShapeMap K J q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (((x : 𝓞 K) : K)) =
          traceEmbedding K (((y : 𝓞 K) : K)) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K (FractionalIdeal.mk0 K J) :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice
        K (FractionalIdeal.mk0 K J) hv
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K ((y : 𝓞 K) : K)) = v
    simp_all

noncomputable def coneIdealElementShapeEquiv
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥(J : Ideal (𝓞 K)) ≃
      shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq :=
  Equiv.ofBijective (coneIdealElementShapeMap K J q hq)
    (coneIdealElementShapeMap_bijective K J q hq)

@[simp]
theorem coneIdealElementShapeEquiv_coe
    (J : (Ideal (𝓞 K))⁰)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥(J : Ideal (𝓞 K))) :
    ((coneIdealElementShapeEquiv K J q hq x :
        shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq
        (traceEmbedding K (((x : 𝓞 K) : K))) :=
  by rfl

open Classical in
def coneNonzeroEquivSingletonCompl
    (J : (Ideal (𝓞 K))⁰) :
    nonzeroIdealElement K J ≃
      {x : ↥(J : Ideal (𝓞 K)) // x ∉ ({0} : Finset ↥(J : Ideal (𝓞 K)))} where
  toFun x :=
    ⟨⟨x.1, x.2.1⟩, by
      simp only [Finset.mem_singleton]
      intro hx
      exact x.2.2 (congrArg Subtype.val hx)⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      intro hx
      apply x.2
      simp_all⟩
  left_inv x := by
    simp
  right_inv x := by
    apply Subtype.ext
    simp

private theorem coneTheta_eq_one_add_nonzero
    (J : (Ideal (𝓞 K))⁰) (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) q hq =
      1 + ∑' x : nonzeroIdealElement K J, mixedGaussian K (((x : 𝓞 K) : K)) q := by
  classical
  let f : ↥(J : Ideal (𝓞 K)) → ℂ := fun x ↦ mixedGaussian K (((x : 𝓞 K) : K)) q
  have hsL := summable_latticeTheta
    (shapeIdealLattice K (FractionalIdeal.mk0 K J) q hq) Real.pi_pos
  have hs : Summable f := by
    have h := (Equiv.summable_iff (coneIdealElementShapeEquiv K J q hq)).mpr hsL
    exact h.congr fun x ↦ by
      dsimp only [Function.comp_apply, f]
      rw [coneIdealElementShapeEquiv_coe, ← mixedGaussian_eq_latticeGaussian]
  have heq : fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) q hq = ∑' x, f x := by
    rw [fractionalShapeIdealTheta, latticeTheta,
      ← (coneIdealElementShapeEquiv K J q hq).tsum_eq]
    apply tsum_congr
    intro x
    rw [coneIdealElementShapeEquiv_coe, ← mixedGaussian_eq_latticeGaussian]
  rw [heq, ← hs.sum_add_tsum_subtype_compl ({0} : Finset ↥(J : Ideal (𝓞 K)))]
  simp only [Finset.sum_singleton]
  have hz : f 0 = 1 := by simp [f, mixedGaussian]
  rw [hz, ← (coneNonzeroEquivSingletonCompl K J).tsum_eq]
  rfl

private theorem coneRadialConstant_ne_zero :
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  have hn : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  exact (mul_pos (mul_pos (by positivity) hn) (Units.regulator_pos K)).ne'

private theorem cone_tsum_radialKernel
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) (y : realSpace K) :
    (∑' x : nonzeroIdealElement K J, mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y) =
      (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
        Units.regulator K : ℝ) : ℂ) *
      (Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
      (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J) (expMapBasis y)
        (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1)) := by
  rw [coneTheta_eq_one_add_nonzero]
  simp only [add_sub_cancel_left]
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro x
  exact mixedRadialJacobian_mul_mixedMellinGaussian K y (((x : 𝓞 K) : K)) s

private theorem cone_summable_integral_norm
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun x : nonzeroIdealElement K J ↦ ∫ y in unitFundamentalParamSet K,
      ‖mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y‖) := by
  rw [← (idealElementMulDecompositionEquiv K J).summable_iff]
  convert summable_prod_integral_norm_mixedConeRadialKernel_unitSlab K J hs using 1
  funext p
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  rw [idealElementMulDecompositionEquiv_coe]

private theorem cone_integrable_tsum {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [Countable ι] {F : ι → α → ℂ}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  let G : ι → α →₁[μ] ℂ := fun i ↦ (hF_int i).toL1 (F i)
  have hnorm (i : ι) : ‖G i‖ = ∫ a, ‖F i a‖ ∂μ := by
    rw [show G i = (hF_int i).toL1 (F i) by rfl,
      Integrable.norm_toL1, integral_norm_eq_lintegral_enorm
        (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hG_norm : Summable fun i ↦ ‖G i‖ := hF_sum.congr fun i ↦ (hnorm i).symm
  have hG_enorm : ∑' i, ‖G i‖ₑ ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hG_norm
  have hcoe : (⇑(∑' i, G i) : α → ℂ) =ᵐ[μ] fun a ↦ ∑' i, F i a := by
    filter_upwards [Lp.coeFn_tsum hG_enorm,
      ae_all_iff.mpr (fun i ↦ (hF_int i).coeFn_toL1)] with a hsum hterm
    exact hsum.trans (tsum_congr fun i ↦ hterm i)
  exact (L1.integrable_coeFn (∑' i, G i)).congr hcoe

theorem integrableOn_fractionalShapeIdealTheta_logMellin
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun y : realSpace K ↦
        Complex.exp ((Module.finrank ℚ K : ℂ) * s *
          (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
          (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J)
            (expMapBasis y) (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1))
      (unitFundamentalParamSet K) := by
  classical
  letI := countable_nonzeroIdealElement K J
  have hi (x : nonzeroIdealElement K J) : IntegrableOn
      (mixedConeRadialKernel K (((x : 𝓞 K) : K)) s) (unitFundamentalParamSet K) :=
    (integrable_mixedConeRadialKernel K (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
      (lt_trans zero_lt_one hs)).integrableOn
  have ht := cone_integrable_tsum hi (cone_summable_integral_norm K J hs)
  have hscaled := ht.const_mul (
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ)⁻¹)
  apply IntegrableOn.congr_fun hscaled _ measurableSet_unitFundamentalParamSet
  intro y _
  dsimp only
  rw [cone_tsum_radialKernel, ← mul_assoc, inv_mul_cancel₀ (coneRadialConstant_ne_zero K), one_mul]

private theorem cone_integral_tsum_radialKernel
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in unitFundamentalParamSet K,
      ∑' x : nonzeroIdealElement K J, mixedConeRadialKernel K (((x : 𝓞 K) : K)) s y) =
      ((1 / 2 : ℂ) ^ nrRealPlaces K * (1 / 4 : ℂ) ^ nrComplexPlaces K *
        Complex.Gammaℝ s ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K) *
          fundamentalConeZeta K J s := by
  classical
  letI := countable_nonzeroIdealElement K J
  letI := countable_idealSet K J
  have hi (x : nonzeroIdealElement K J) : IntegrableOn
      (mixedConeRadialKernel K (((x : 𝓞 K) : K)) s) (unitFundamentalParamSet K) :=
    (integrable_mixedConeRadialKernel K (RingOfIntegers.coe_ne_zero_iff.mpr x.prop.2)
      (lt_trans zero_lt_one hs)).integrableOn
  rw [← integral_tsum_of_summable_integral_norm hi (cone_summable_integral_norm K J hs),
    ← (idealElementMulDecompositionEquiv K J).tsum_eq]
  have hp : Summable (fun p : idealSet K J × unitShiftIndex K ↦
      ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K
          (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y) := by
    apply Summable.of_norm_bounded
      (summable_prod_integral_norm_mixedConeRadialKernel_unitSlab K J hs)
    intro p
    exact norm_integral_le_integral_norm _
  have hrewrite : (fun p : idealSet K J × unitShiftIndex K ↦
    ∫ y in unitFundamentalParamSet K,
      mixedConeRadialKernel K (((idealElementMulDecompositionEquiv K J p : 𝓞 K) : K)) s y) =
    (fun p : idealSet K J × unitShiftIndex K ↦
    ∫ y in unitFundamentalParamSet K,
      mixedConeRadialKernel K
        (((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : K) * idealSetElement K J p.1) s y) := by
    funext p
    apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
    intro y _
    rw [idealElementMulDecompositionEquiv_coe]
  rw [hrewrite, hp.tsum_prod]
  have hin : (fun a : idealSet K J ↦ ∑' z : unitShiftIndex K,
      ∫ y in unitFundamentalParamSet K,
        mixedConeRadialKernel K
          (((fundamentalUnitForShift z : (𝓞 K)ˣ) : K) * idealSetElement K J a) s y) =
      (fun a : idealSet K J ↦ ∫ q : realSpace K,
        mixedMellinGaussian K (idealSetElement K J a) s q
        ∂Measure.pi (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0))) := by
    funext a
    rw [← integral_mixedConeRadialKernel_eq_tsum_unitSlab K
      (idealSetElement_ne_zero K J a) (lt_trans zero_lt_one hs),
      integral_mixedConeRadialKernel]
  rw [hin]
  exact (hasSum_integral_mixedMellinGaussian_idealSet K J hs).tsum_eq

private theorem cone_normalizingCoefficient :
    ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
      Units.regulator K) : ℝ) : ℂ)⁻¹ *
      ((1 / 2 : ℂ) ^ nrRealPlaces K * (1 / 4 : ℂ) ^ nrComplexPlaces K) =
    (2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
      ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) := by
  push_cast
  rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  simp only [zpow_natCast]
  have hfour : (1 / 4 : ℂ) = (2 : ℂ)⁻¹ ^ 2 := by norm_num
  rw [hfour, one_div, inv_pow, ← pow_mul, Nat.mul_comm 2, pow_mul]
  simp only [mul_inv_rev, inv_inv, inv_pow]
  field_simp
  <;> ring

theorem setIntegral_fractionalShapeIdealTheta_logMellin
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : realSpace K in unitFundamentalParamSet K,
      Complex.exp ((Module.finrank ℚ K : ℂ) * s *
        (y Units.dirichletUnitTheorem.w₀ : ℂ)) *
        (fractionalShapeIdealTheta K (FractionalIdeal.mk0 K J)
          (expMapBasis y) (fun w ↦ ne_of_gt (expMapBasis_pos _ w)) - 1)) =
      (2 : ℂ) ^ (-(↑(nrRealPlaces K + nrComplexPlaces K) : ℤ)) /
        ((Module.finrank ℚ K : ℂ) * (Units.regulator K : ℂ)) *
        Complex.Gammaℝ s ^ nrRealPlaces K *
        Complex.Gammaℂ s ^ nrComplexPlaces K *
        fundamentalConeZeta K J s := by
  have hi := cone_integral_tsum_radialKernel K J hs
  simp_rw [cone_tsum_radialKernel] at hi
  rw [integral_const_mul] at hi
  have hi' := congrArg
    (fun z : ℂ ↦
      ((((2 : ℝ)⁻¹ ^ nrComplexPlaces K * (Module.finrank ℚ K : ℝ) *
        Units.regulator K) : ℝ) : ℂ)⁻¹ * z) hi
  rw [← mul_assoc, inv_mul_cancel₀ (coneRadialConstant_ne_zero K), one_mul] at hi'
  calc
    _ = _ := hi'
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
        cone_normalizingCoefficient]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
