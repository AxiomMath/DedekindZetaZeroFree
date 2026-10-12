module

public import DedekindZetaZeroFree.Metaplectic.Torus.UniformRadialCoordinates
public import DedekindZetaZeroFree.MeasureTheory.MeasurableParameterDerivatives
public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderLocalRegularity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem branch_measurable {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) :
    Measurable (P.branch v) := by
  let D := R.probe.correction
  have hc : Continuous (R.A.correctionLS D.Λ D.G D.η_id) := by
    unfold SArithmeticData.correctionLS SArithmeticData.ideleSInverseProduct
    have hθ := SArithmeticData.CorrectionAssembly.correctionTheta_continuous R.A
      D.Λ D.G D.η_id D.Λ_continuous D.G_continuous D.eta_continuous
    apply Continuous.mul
    · apply continuous_finset_prod
      intro w hw
      exact (hθ.comp ((SArithmeticData.CorrectionTopology.infinite_embedding_continuous w).comp
        ((continuous_apply w).comp continuous_fst))).inv
    · apply continuous_finset_prod
      intro p hp
      exact (hθ.comp ((SArithmeticData.CorrectionTopology.finite_embedding_continuous p.val).comp
        ((continuous_apply p).comp continuous_snd))).inv
  have hh := finiteClass_measurable R (fun q => R.σ
    ((D.H (QuotientGroup.mk' R.A.sixthPowers
      (R.A.diagonal (R.probe.unitReps.representative v).val)) q : Fˣ) : F))
  have hh' : Measurable (fun y : R.A.G => R.σ
      ((R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y : Fˣ) : F)) := by
    simpa only [D.H_actual] using hh
  have h := (continuous_subtype_val.comp hc).measurable.mul hh'
  have he : P.branch v = (fun y : R.A.G =>
      (R.A.correctionLS D.Λ D.G D.η_id y : ℂ) *
      R.σ ((R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y : Fˣ) : F)) :=
    funext (P.branch_global v)
  rw [he]
  exact h

theorem sheet_radial_contDiff {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (κ : R.A.V) (y : R.A.G1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => T.sheetIntegrand P v κ
      (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t))) := by
  have hs := (fourier_chart_contDiffOn T v (diagonal R y.val)
    (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)).comp
      ((uniformCoordinates_smooth R).contDiffOn (s := Set.univ))
      (fun t _ => uniformCoordinates_mem R t)
  rw [contDiffOn_univ] at hs
  have he : (fun t => T.sheetIntegrand P v κ
      (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t))) =
      (fun t => sheetPhase R κ y.val * P.branch v y.val * fourier R Q.dq (T.theta v)
        (diagonal R y.val * archChart F R.A.zeta12 R.A.primitive_zeta12 (uniformCoordinates R t) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) := by
    funext t
    change sheetPhase R κ _ * P.branch v _ * _ = _
    rw [sheetPhase_uniform_radial, branch_uniform_radial, diagonal_uniform_radial]
  rw [he]
  exact contDiff_const.mul hs

theorem sheet_radial_measurable {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (κ : R.A.V) :
    letI : MeasurableSpace R.A.G1 := borel _
    Measurable (fun p : R.A.G1 × ℝ => T.sheetIntegrand P v κ
      (p.1.val * R.A.radialSection (Real.exp p.2) (Real.exp_pos p.2))) := by
  letI : MeasurableSpace R.A.G1 := borel _
  letI : BorelSpace R.A.G1 := ⟨rfl⟩
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  have hr : Continuous (fun t : ℝ => R.A.radialSection (Real.exp t) (Real.exp_pos t)) :=
    R.A.continuous_radialSection.comp (Real.continuous_exp.subtype_mk Real.exp_pos)
  have hy : Continuous (fun p : R.A.G1 × ℝ =>
      p.1.val * R.A.radialSection (Real.exp p.2) (Real.exp_pos p.2)) :=
    (continuous_subtype_val.comp continuous_fst).mul (hr.comp continuous_snd)
  have hp : Measurable (fun p : R.A.G1 × ℝ => sheetPhase R κ
      (p.1.val * R.A.radialSection (Real.exp p.2) (Real.exp_pos p.2))) :=
    (sheetPhase_measurable R κ).comp hy.measurable
  have hb : Measurable (fun p : R.A.G1 × ℝ => P.branch v
      (p.1.val * R.A.radialSection (Real.exp p.2) (Real.exp_pos p.2))) :=
    (branch_measurable R P v).comp hy.measurable
  have hf : Continuous (fun p : R.A.G1 × ℝ => fourier R Q.dq (T.theta v)
      (diagonal R (p.1.val * R.A.radialSection (Real.exp p.2) (Real.exp_pos p.2)) *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) :=
    (fourier_continuous T v).comp (((diagonal_continuous R).comp hy).mul continuous_const)
  exact (hp.mul hb).mul hf.measurable

theorem sheet_radial_jets_aestronglyMeasurable {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (P : Packet R Q) (v : R.A.UnitQuotient) (κ : R.A.V) (j : ℕ) (hj : j ≤ 2) (u : ℝ) :
    letI : MeasurableSpace R.A.G1 := borel _
    AEStronglyMeasurable (fun y : R.A.G1 => iteratedDeriv j
      (fun t => T.sheetIntegrand P v κ
        (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t))) u) R.probe.domain.measure := by
  letI : MeasurableSpace R.A.G1 := borel _
  have hm := SourceSheet.Differentiation.ParameterDerivatives.iterated_two_measurable_of_measurable
    (fun (y : R.A.G1) t => T.sheetIntegrand P v κ
      (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)))
    (sheet_radial_measurable R T P v κ)
    (fun y => (sheet_radial_contDiff R T P v κ y).of_le (by simp)) j hj
  exact (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
end DedekindZetaZeroFree.SheetRescaling

end
