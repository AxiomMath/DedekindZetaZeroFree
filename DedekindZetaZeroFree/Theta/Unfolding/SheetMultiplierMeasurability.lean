module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitSheetMajorants
public import DedekindZetaZeroFree.Theta.Periods.RationalPeriodContinuity
public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderLocalRegularity
public import DedekindZetaZeroFree.Adeles.Quotients.PGLContinuity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open ThetaExpansion.SignedExpansion
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

private theorem sixthPowers_measurable (A : SArithmeticData F) :
    MeasurableSet (A.sixthPowers : Set A.G) := by
  have h : IsSigmaCompact (Set.range (fun y : A.G => y ^ 6)) :=
    isSigmaCompact_range (continuous_id.pow 6)
  obtain ⟨K, hK, hU⟩ := h
  change MeasurableSet (Set.range (fun y : A.G => y ^ 6))
  rw [← hU]
  exact MeasurableSet.iUnion (fun i => (hK i).measurableSet)

private theorem class_measurableSingleton (A : SArithmeticData F) :
    MeasurableSingletonClass A.V := by
  constructor
  intro q
  obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective A.sixthPowers) q
  apply measurableSet_quotient.mpr
  have he : (Quotient.mk'' ⁻¹' {QuotientGroup.mk' A.sixthPowers y} : Set A.G) =
      (fun z => z / y) ⁻¹' (A.sixthPowers : Set A.G) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact QuotientGroup.eq_iff_div_mem
  rw [he]
  exact (sixthPowers_measurable A).preimage
    ((continuous_id : Continuous (fun z : A.G => z)).div' continuous_const).measurable

theorem classMask_measurable : Measurable (fun y : R.A.G =>
    if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then (1 : ℂ) else 0) := by
  letI := class_measurableSingleton R.A
  letI := R.A.V_finite
  exact (measurable_of_finite (fun q : R.A.V =>
    if q ∈ R.probe.correction.B then (1 : ℂ) else 0)).comp
      (measurable_quotient_mk'' (s := QuotientGroup.leftRel R.A.sixthPowers))

private theorem correctionLS_continuous :
    Continuous (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
      R.probe.correction.η_id) := by
  unfold SArithmeticData.correctionLS SArithmeticData.ideleSInverseProduct
  have hθ := SArithmeticData.CorrectionAssembly.correctionTheta_continuous R.A
    R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id
    R.probe.correction.Λ_continuous R.probe.correction.G_continuous
    R.probe.correction.eta_continuous
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w hw
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.infinite_embedding_continuous w).comp
      ((continuous_apply w).comp continuous_fst))).inv
  · apply continuous_finset_prod
    intro v hv
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.finite_embedding_continuous v.val).comp
      ((continuous_apply v).comp continuous_snd))).inv

theorem branch_measurable {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) : Measurable (P.branch v) := by
  letI := class_measurableSingleton R.A
  letI := R.A.V_finite
  have hH : Measurable (fun q : R.A.V =>
      R.σ (((R.A.H_S6 (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal
        (R.probe.unitReps.representative v).val)) q : Fˣ) : F))) :=
    measurable_of_finite _
  have hc := hH.comp (measurable_quotient_mk'' (s := QuotientGroup.leftRel R.A.sixthPowers))
  have hLS : Measurable (fun y : R.A.G =>
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
        R.probe.correction.η_id y : ℂ)) :=
    (continuous_subtype_val.comp (correctionLS_continuous R)).measurable
  convert hLS.mul hc using 1
  funext y
  rw [P.branch_global]
  exact congrArg (_ * ·) (congrArg (fun r : rootsOfUnity 6 F => R.σ ((r : Fˣ) : F))
    (R.A.H_S6_on_representatives (R.A.diagonal (R.probe.unitReps.representative v).val) y)).symm

def sheetMultiplier {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹

theorem sheetMultiplier_measurable {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) : Measurable (sheetMultiplier R P v) :=
  (classMask_measurable R).mul (branch_measurable R P v).inv

theorem sheetMultiplier_norm_le {Q : AdmissibleFlatSources R} (P : Packet R Q)
    (v : R.A.UnitQuotient) (y : R.A.G) : ‖sheetMultiplier R P v y‖ ≤ 1 := by
  unfold sheetMultiplier
  split_ifs <;> simp [branch_norm_one R P]

theorem localIdele_continuous : Continuous (localIdele R) := by
  have hi (v : KPHilbert.Place F) : Continuous (KPRationalAdelicSplitting.localIdele F v) := by
    cases v with
    | inl w =>
      apply Continuous.units_map
      change Continuous (fun x : w.Completion =>
        (Pi.mulSingle w x, (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
      exact (continuous_mulSingle w).prodMk continuous_const
    | inr q =>
      apply Continuous.units_map
      let s : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := {q}ᶜ
      have hs : Filter.cofinite ≤ Filter.principal s :=
        Filter.le_principal_iff.mpr (Set.finite_singleton q).compl_mem_cofinite
      let f : q.adicCompletion F → RestrictedProduct (fun w => w.adicCompletion F)
          (fun w => (w.adicCompletionIntegers F : Set _)) (Filter.principal s) := fun x =>
        ⟨Pi.mulSingle q x, by
          intro w hw
          have hwq : w ≠ q := hw
          simpa [Pi.mulSingle_eq_of_ne hwq] using (w.adicCompletionIntegers F).one_mem⟩
      have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
        (continuous_mulSingle q)
      exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hs).comp hf)
  unfold localIdele
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w hw
    exact (hi (Sum.inl w)).comp ((continuous_apply w).comp continuous_fst)
  · apply continuous_finset_prod
    intro p hp
    exact (hi (Sum.inr p.val)).comp ((continuous_apply p).comp continuous_snd)

theorem signedArgument_continuous (m : ThetaReflectionData.Row R.A) (b : Bool)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Continuous (fun y => signedArgument R m b y d) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  unfold signedArgument diagonal
  exact (continuous_const.mul
    ((pglA_continuous R.A).comp
      (localIdele_continuous R))).mul continuous_const

theorem orbitSheet_measurable {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (i : OrbitIndex R) (l : PositiveAxis) : Measurable (orbitSheet R C v m b i l) := by
  have hm : Measurable (fun z : Sheet R.A l => sheetMultiplier R C.packet v z.val) :=
    (sheetMultiplier_measurable R C.packet v).comp measurable_subtype_coe
  have hd : Measurable (fun z : Sheet R.A l =>
      ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
        digitWeight R m d * orbitFrequencyValue R C.sources C.realization v i
          (signedArgument R m b z.val d)) := by
    apply Finset.measurable_sum
    intro d hd
    exact measurable_const.mul (((orbitFrequencyValue_continuous R C.realization v i).comp
      ((signedArgument_continuous R m b d).comp continuous_subtype_val)).measurable)
  convert hm.mul hd using 1
  rfl

end DedekindZetaZeroFree.OrbitExpansion

end
