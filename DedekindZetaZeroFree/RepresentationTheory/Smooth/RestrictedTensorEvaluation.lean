module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.UniformFiniteLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages KPLiteralChamber
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_right → sectionTuple_right
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

private theorem matrix_section (w : InfinitePlace F) (M : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    complexMatrix A w (sectionTuple F ζ hζ (fun _ => M) (Sum.inl w)) = M := by
  unfold complexMatrix sectionTuple
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ M) = M
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

theorem localValue_arch_chart_smooth (g : Raw A) (w : InfinitePlace F)
    (f : Plus A P C (Sum.inl w)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F =>
      localValue A P C (Sum.inl w)
        ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)) f)
      (archDomain F) := by
  let M := complexMatrix A w (g (Sum.inl w))
  let B (z : ArchCoordinates F) : Matrix (Fin 2) (Fin 2) ℂ :=
    M.val * !![z w 1 + z w 0*z w 2, z w 0; z w 2, 1]
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have hBA z (hz : z ∈ archDomain F) : B z = (M * rightMatrix (z w)).val := by
    dsimp [B]
    rw [rightMatrix_val _ (hz w)]
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ f.val).mp f.val.property).2
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
      KPCplxPrincipalSeriesCharts.matrixFunction f.val (B z)) (archDomain F) :=
    hf.comp hB.contDiffOn (fun z hz => by
      rw [Set.mem_setOf_eq, hBA z hz]
      exact Matrix.GeneralLinearGroup.det_ne_zero (M * rightMatrix (z w)))
  apply ((contDiffOn_const : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun _ : ArchCoordinates F => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
      (g (Sum.inl w)).epsilon : ℂ)) (archDomain F)).mul hs).congr
  intro z hz
  have he : ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)).epsilon =
      (g (Sum.inl w)).epsilon := by
    change (g (Sum.inl w)).epsilon * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one, mul_one]
  have hm : complexMatrix A w
      ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)) =
      M * rightMatrix (z w) := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * _) = _
    rw [map_mul]
    change M * complexMatrix A w (sectionTuple F ζ hζ (fun _ => rightMatrix (z w)) (Sum.inl w)) = _
    rw [matrix_section]
  rw [localValue, he, hm, hBA z hz]
  dsimp only [KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (M * rightMatrix (z w)))]
  congr 1
  exact congrArg (fun m : KPCplxCharacterHaar.ComplexGL2 => f.val m) (Units.ext rfl)

private theorem archScalar_chart_smooth (g : Raw A) (v : KPHilbert.Place F) (f : Plus A P C v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F => archScalar A P C v
      ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) v) f) (archDomain F) := by
  cases v with
  | inl w => exact localValue_arch_chart_smooth A P C g w f
  | inr q => exact contDiffOn_const

private theorem finiteValue_chart (g : Raw A) (v : KPHilbert.Place F) (f : Plus A P C v)
    (z : ArchCoordinates F) :
    finiteValue A P C v ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) v) f =
      finiteValue A P C v (g v) f := by
  cases v with
  | inl w => rfl
  | inr q => change f.val (KPPGLLocalCover.coverQuotient F ζ hζ _ (g _ * 1)) = _; rw [mul_one]; rfl

private theorem rawStageValue_chart_smooth (s : RestrictedTensorSimple.Level (bad A P C))
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) (g : Raw A) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F =>
      rawStageValue A P C s (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) x)
      (archDomain F) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    have hprod : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F =>
        ∏ j : s.val, archScalar A P C j.val
          ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) j.val) (x j)) (archDomain F) := by
      apply contDiffOn_prod
      intro j _
      exact archScalar_chart_smooth A P C g j.val (x j)
    have hf : (fun z : ArchCoordinates F => fun j : s.val => finiteValue A P C j.val
        ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) j.val) (x j)) =
        fun _ => fun j : s.val => finiteValue A P C j.val (g j.val) (x j) := by
      funext z j
      exact finiteValue_chart A P C g j.val (x j) z
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F =>
        rawStageValue A P C s (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w)))
          (PiTensorProduct.tprod ℂ x)) (archDomain F) := by
      let b : ℂ := rationalEvaluation A (comparison A P C
        (RestrictedTensorSimple.stageInclusion (Fiber A P C) (reference A P C) (bad A P C) s
          (PiTensorProduct.tprod ℂ (fun j => finiteValue A P C j.val (g j.val) (x j)))))
      have hconst : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : ArchCoordinates F => b)
          (archDomain F) := contDiffOn_const
      apply (hprod.mul hconst).congr
      intro z _
      have he := rawStageInsertion_arch_factorization A P C s x
        (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w)))
      change rawStageValue A P C s _ (PiTensorProduct.tprod ℂ x) = _ at he
      rw [he]
      change _ * rationalEvaluation A (comparison A P C
        (RestrictedTensorSimple.stageInclusion (Fiber A P C) (reference A P C) (bad A P C) s
          (PiTensorProduct.tprod ℂ _))) = _ * b
      unfold b
      rw [congrFun hf z]
    have hsc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ArchCoordinates F => c *
        rawStageValue A P C s (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w)))
          (PiTensorProduct.tprod ℂ x)) (archDomain F) := contDiffOn_const.mul hs
    convert hsc using 1
    funext z
    exact map_smul _ c _
  | add x y hx hy => simpa only [map_add] using hx.add hy

theorem quotientCoreEvaluator_chart_smooth
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => quotientCoreEvaluator A P C x (g * archChart F ζ hζ z))
      (archDomain F) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      induction g using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨u, hu⟩ := exists_reference_stage A P C g
        let t : RestrictedTensorSimple.Level (bad A P C) := ⟨s.val ∪ u.val,
          s.property.trans Finset.subset_union_left⟩
        have hst : s ≤ t := Finset.subset_union_left
        have ht : ∀ v, v ∉ t.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v :=
          fun v hv => hu v (fun h => hv (Finset.mem_union_right _ h))
        have ht' (z : ArchCoordinates F) : ∀ v, v ∉ t.val →
            localValue A P C v ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) v)
              (plusReference A P C v) = reference A P C v := by
          intro v hv
          cases v with
          | inl w =>
            have hb : Sum.inl w ∈ bad A P C := by
              simp [bad, ScalarAbsorption.fullBad]
            exact False.elim (hv (t.property hb))
          | inr q =>
            change localValue A P C _ (g _ * 1) _ = _
            rw [mul_one]
            exact ht _ hv
        have he : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) s x =
            RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) t
              (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t hst x) :=
          Module.DirectLimit.of_f.symm
        change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => quotientCoreEvaluator A P C
          (RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C) (bad A P C) s x)
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) * archChart F ζ hζ z)) (archDomain F)
        rw [he]
        apply (rawStageValue_chart_smooth A P C t
          (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t hst x) g).congr
        intro z _
        dsimp only [quotientCoreEvaluator, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← sectionTuple_right, ← map_mul, ← map_mul, quotientCoreValue_raw]
        exact rawCoreInsertion_stage A P C t _ _ (ht' z)
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
