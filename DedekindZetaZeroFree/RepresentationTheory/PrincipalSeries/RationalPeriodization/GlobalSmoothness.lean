module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarEvaluationContinuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicLieGeneration

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct KPLiteralChamber
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_right → sectionTuple_right
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem archValue_chart_smooth (g : Raw R) (w : InfinitePlace F)
    (f : Plus R N P C (Sum.inl w)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : KPGlobalResidualConstruction.ArchCoordinates F =>
      localValue R N P C (Sum.inl w)
        ((g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (z w))) (Sum.inl w)) f)
      (KPGlobalResidualConstruction.archDomain F) := by
  let M := complexMatrix R w (g (Sum.inl w))
  let A (z : KPGlobalResidualConstruction.ArchCoordinates F) := M * rightMatrix (z w)
  let B (z : KPGlobalResidualConstruction.ArchCoordinates F) : Matrix (Fin 2) (Fin 2) ℂ :=
    M.val * !![z w 1 + z w 0*z w 2, z w 0; z w 2, 1]
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have hBA z (hz : z ∈ KPGlobalResidualConstruction.archDomain F) : B z = (A z).val := by
    dsimp [B, A]
    rw [rightMatrix_val _ (hz w)]
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ f.val).mp f.val.property).2
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => KPCplxPrincipalSeriesCharts.matrixFunction f.val (B z))
      (KPGlobalResidualConstruction.archDomain F) := hf.comp hB.contDiffOn (fun z hz => by
    rw [Set.mem_setOf_eq, hBA z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero (A z))
  apply (contDiffOn_const.mul hs).congr
  intro z hz
  have he : ((g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (z w)))
      (Sum.inl w)).epsilon = (g (Sum.inl w)).epsilon := by
    change (g (Sum.inl w)).epsilon * 1 * KPLocalCover.sigmaTwo F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one, mul_one]
  have hm : complexMatrix R w ((g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12
      (fun w => rightMatrix (z w))) (Sum.inl w)) = A z := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * _) = _
    rw [map_mul]
    change M * EisensteinReferenceSections.LocalCovariance.complexMatrix F R.A.zeta12 R.A.primitive_zeta12 w
      (sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun _ => rightMatrix (z w)) (Sum.inl w)) = A z
    rw [EisensteinReferenceSections.SourceSmooth.complexMatrix_section]
  change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
    ((g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (z w))) (Sum.inl w)).epsilon : ℂ) *
      f.val (complexMatrix R w ((g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12
        (fun w => rightMatrix (z w))) (Sum.inl w))) = _
  rw [he, hm, hBA z hz]
  dsimp only [KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (A z))]
  exact congrArg (fun a : KPCplxCharacterHaar.ComplexGL2 =>
    (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
      (g (Sum.inl w)).epsilon : ℂ) * f.val a) (Units.ext rfl)

theorem scalarSource_chart_smooth (x : PlusCore R N P C) (g : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => scalarSourceEvaluator R N P C x
      (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 z))
      (KPGlobalResidualConstruction.archDomain F) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun a => scalarSourceEvaluator R N P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s z) (g * KPGlobalResidualConstruction.archChart
      F R.A.zeta12 R.A.primitive_zeta12 a)) _
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun a => scalarSourceEvaluator R N P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f))
        (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 a))
        (KPGlobalResidualConstruction.archDomain F) := by
      induction g using QuotientGroup.induction_on with
      | H g =>
        induction g using QuotientGroup.induction_on with
        | H g =>
          have ht : ContDiffOn ℝ (⊤ : ℕ∞) (fun a =>
              pureArchProduct R N P C s f (g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (a w))) *
              scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s
                (PiTensorProduct.tprod ℂ (finitePure R N P C s f)))
                (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 g).val)
              (KPGlobalResidualConstruction.archDomain F) := by
            apply ContDiffOn.mul _ contDiffOn_const
            unfold pureArchProduct
            apply contDiffOn_prod
            intro w _
            exact archValue_chart_smooth R N P C g w _
          apply ht.congr
          intro a _
          change scalarSourceEvaluator R N P C _
            (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g) *
              KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 a) = _
          rw [← sectionTuple_right, ← map_mul, ← map_mul, scalarSource_pure_raw_factor]
          have he : EisensteinReferenceSections.FiniteSourceTopology.finiteProjection F R.A.zeta12 R.A.primitive_zeta12
              (g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (a w))) =
              EisensteinReferenceSections.FiniteSourceTopology.finiteProjection F R.A.zeta12 R.A.primitive_zeta12 g := by
            apply RestrictedProduct.ext
            intro p
            cases p with
            | inl w => rfl
            | inr q => change g (Sum.inr q) * 1 = g (Sum.inr q); exact mul_one _
          have heq : EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12
              (g * sectionTuple F R.A.zeta12 R.A.primitive_zeta12 (fun w => rightMatrix (a w))) =
              EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 g := by
            apply Subtype.ext
            exact congrArg (fun v => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
              (amalgamation F R.A.zeta12 R.A.primitive_zeta12 v)) he
          rw [heq]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact contDiffOn_const.mul hs
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply]
    exact hx.add hy

theorem scalarSource_smooth (x : PlusCore R N P C) :
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (scalarSourceEvaluator R N P C x) :=
  ⟨scalarSource_continuous R N P C x, scalarSource_chart_smooth R N P C x,
    scalarSource_has_level R N P C x⟩

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
