module

public import DedekindZetaZeroFree.Eisenstein.Induction.SectionContinuity
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalCovariance
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology Matrix.Norms.Elementwise
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceSmooth
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages KPLiteralChamber
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_right → sectionTuple_right

 theorem complexMatrix_section (w : InfinitePlace F) (M : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    LocalCovariance.complexMatrix F ζ hζ w (sectionTuple F ζ hζ (fun _ => M) (Sum.inl w)) = M := by
  unfold LocalCovariance.complexMatrix sectionTuple
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ M) = M
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

 theorem arch_chart_smooth (g : RestrictedCover F ζ hζ) (w : InfinitePlace F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : KPGlobalResidualConstruction.ArchCoordinates F =>
      LocalCovariance.arch F ζ hζ w
        ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)))
      (KPGlobalResidualConstruction.archDomain F) := by
  let M := LocalCovariance.complexMatrix F ζ hζ w (g (Sum.inl w))
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
  let f := KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter
  have hf := ((KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ f).mp f.property).2
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => KPCplxPrincipalSeriesCharts.matrixFunction f (B z))
      (KPGlobalResidualConstruction.archDomain F) := hf.comp hB.contDiffOn (fun z hz => by
    rw [Set.mem_setOf_eq, hBA z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero (A z))
  apply (contDiffOn_const.mul hs).congr
  intro z hz
  have he : ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)).epsilon =
      (g (Sum.inl w)).epsilon := by
    change (g (Sum.inl w)).epsilon * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one, mul_one]
  have hm : LocalCovariance.complexMatrix F ζ hζ w
      ((g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) (Sum.inl w)) = A z := by
    unfold LocalCovariance.complexMatrix
    change Matrix.GeneralLinearGroup.map _ (_ * _) = _
    rw [map_mul]
    change M * LocalCovariance.complexMatrix F ζ hζ w
      (sectionTuple F ζ hζ (fun _ => rightMatrix (z w)) (Sum.inl w)) = A z
    rw [complexMatrix_section]
  rw [LocalCovariance.arch, he, hm, hBA z hz]
  dsimp only [KPCplxPrincipalSeriesCharts.matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (A z))]
  congr 2

 theorem scalar_chart_smooth (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => RawSource.scalarValue F ζ hζ P C
      (g * KPGlobalResidualConstruction.archChart F ζ hζ z)) (KPGlobalResidualConstruction.archDomain F) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
          RawSource.archProduct F ζ hζ (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))) *
          RawSource.scalarValue F ζ hζ P C (FiniteSourceTopology.finiteQuotient F ζ hζ g).val)
          (KPGlobalResidualConstruction.archDomain F) := by
        apply ContDiffOn.mul _ contDiffOn_const
        unfold RawSource.archProduct
        apply contDiffOn_prod
        intro w _
        exact arch_chart_smooth F ζ hζ g w
      apply hs.congr
      intro z _
      change RawSource.scalarValue F ζ hζ P C
        (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) * KPGlobalResidualConstruction.archChart F ζ hζ z) = _
      rw [← sectionTuple_right, ← map_mul, ← map_mul, FiniteSourceTopology.scalar_raw_factor]
      congr 2
      change scalarQuotient F ζ hζ (amalgamation F ζ hζ
        (FiniteSourceTopology.finiteProjection F ζ hζ (g * sectionTuple F ζ hζ (fun w => rightMatrix (z w))))) =
          scalarQuotient F ζ hζ (amalgamation F ζ hζ (FiniteSourceTopology.finiteProjection F ζ hζ g))
      congr 2
      apply RestrictedProduct.ext
      intro v
      cases v with
      | inl w => rfl
      | inr q => change g (Sum.inr q) * 1 = g (Sum.inr q); exact mul_one _

 theorem scalar_induced : KPLiteralRaw.Induced F ζ hζ 0 (RawSource.scalarValue F ζ hζ P C) := by
  refine ⟨⟨SourceContinuity.scalar_continuous F ζ hζ P C,
    scalar_chart_smooth F ζ hζ P C, SourceLevels.level F ζ hζ P C,
    SourceLevels.scalar_fixed F ζ hζ P C⟩, RationalCovariance.covariance F ζ hζ P C⟩

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceSmooth

end
