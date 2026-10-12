module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.WeightedWeylKernelsAndGammaCorrections

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPRankOneCenterInducedDiagonalComparison
open KPRankOneShellContinuation KPActualScalarBinding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
private theorem evaluation_analytic (ε : Sign) (s : ℂ) :
    AnalyticAt ℂ (fun z => (evaluationUnit (KPExceptionalRaw.LocalField F q) ε z : ℂ)) s := by
  cases ε
  · change AnalyticAt ℂ (fun z => KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) z) s
    unfold KPRankOneRootParameter.r
    fun_prop
  · change AnalyticAt ℂ (fun z => (KPRankOneRootParameter.r (KPExceptionalRaw.LocalField F q) z)⁻¹) s
    apply AnalyticAt.inv
    · unfold KPRankOneRootParameter.r
      fun_prop
    · exact Complex.exp_ne_zero _

private theorem denominator_analytic (ε : Sign) (s : ℂ) :
    AnalyticAt ℂ (fun z => denominator (KPExceptionalRaw.LocalField F q) ε z) s := by
  cases ε <;> unfold denominator KPRankOneRootParameter.t KPRankOneRootParameter.r <;> dsimp
  · fun_prop
  · apply AnalyticAt.sub analyticAt_const
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.pow
    apply AnalyticAt.inv
    · fun_prop
    · exact Complex.exp_ne_zero _

private theorem scalar_laurent_analytic {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ)
    (u : ℂ → ℂˣ) (s : ℂ)
    (hu : AnalyticAt ℂ (fun z => (u z : ℂ)) s) :
    AnalyticAt ℂ (fun z => l (p.sum (fun n v => (u z : ℂ)^n • v))) s := by
  classical
  simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro n hn
  exact (hu.zpow (Units.ne_zero (u s))).mul analyticAt_const

variable (S : ActualKPBinding F ζ hζ q) (I : IwasawaData S.borel)
variable (E : CenterModule S.heisenberg ≃ₗ[ℂ] CenterModule S.heisenberg)
variable (hE : ∀ (f : CenterModule S.heisenberg) (h : KPExceptionalRaw.actualTorus F ζ hζ q),
  (E f).val h = normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h))
variable (J : CompactOpenLevel (KPRankOneOpenCellKernel.Cover F ζ hζ q))
variable (hJ : J.toOpenSubgroup ≤ I.compact.toOpenSubgroup)

theorem actual_weighted_numerator_all_parameters
    (μ : Measure (KPExceptionalRaw.LocalField F q)) (ε : Sign)
    (p : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J ε)
    (p' : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J (targetSign ε))
    (hp : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ ε p)
    (hp' : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ (targetSign ε) p')
    (s : ℂ)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    denominator (KPExceptionalRaw.LocalField F q) (targetSign ε) (-s - 1/3) *
      normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J ε p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε s) φ).val.val k).val (S.borel.weyl h) =
    denominator (KPExceptionalRaw.LocalField F q) ε s *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J (targetSign ε) p'
        (evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-s - 1/3))
        (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ)).val.val k).val h := by
  let l : (centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel I (targetSign ε) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M φ).val.val k).val (S.borel.weyl h)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let l' : (centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign (targetSign ε)) J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel I (targetSign (targetSign ε)) J) →ₗ[ℂ] ℂ :=
    { toFun := fun M => ((M (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ)).val.val k).val h
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let L : ℂ → ℂ := fun z =>
    denominator (KPExceptionalRaw.LocalField F q) (targetSign ε) (-z - 1/3) *
      normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
      l (centerEvaluate F ζ hζ q S.heisenberg S.borel I J ε p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε z))
  let R : ℂ → ℂ := fun z =>
    denominator (KPExceptionalRaw.LocalField F q) ε z *
      l' (centerEvaluate F ζ hζ q S.heisenberg S.borel I J (targetSign ε) p'
        (evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-z - 1/3)))
  have hflip (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => -w - 1/3) z := by fun_prop
  have hL : AnalyticOnNhd ℂ L Set.univ := by
    intro z _
    have hden := (denominator_analytic F q (targetSign ε) (-z - 1/3)).comp
      (f := fun w : ℂ => -w - 1/3) (hflip z)
    have hev : AnalyticAt ℂ (fun w => l (centerEvaluate F ζ hζ q S.heisenberg S.borel I J ε p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε w))) z := by
      unfold centerEvaluate
      exact scalar_laurent_analytic p l
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε) z (evaluation_analytic F q ε z)
    change AnalyticAt ℂ (fun w => denominator (KPExceptionalRaw.LocalField F q) (targetSign ε) (-w - 1/3) *
      normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
      l (centerEvaluate F ζ hζ q S.heisenberg S.borel I J ε p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε w))) z
    exact (hden.mul analyticAt_const).mul hev
  have hR : AnalyticOnNhd ℂ R Set.univ := by
    intro z _
    have hev : AnalyticAt ℂ (fun w => l' (centerEvaluate F ζ hζ q S.heisenberg S.borel I J (targetSign ε) p'
        (evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-w - 1/3)))) z := by
      unfold centerEvaluate
      exact scalar_laurent_analytic p' l'
        (fun w => evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-w - 1/3)) z
        ((evaluation_analytic F q (targetSign ε) (-z - 1/3)).comp
          (f := fun w : ℂ => -w - 1/3) (hflip z))
    change AnalyticAt ℂ (fun w => denominator (KPExceptionalRaw.LocalField F q) ε w *
      l' (centerEvaluate F ζ hζ q S.heisenberg S.borel I J (targetSign ε) p'
        (evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-w - 1/3)))) z
    exact (denominator_analytic F q ε z).mul hev
  have hch (z : ℂ) (hz : convergenceHalfPlane ε z) : L z = R z :=
    actual_weighted_numerator_chamber F ζ hζ q S I E hE J hJ μ ε p p' hp hp' z hz φ k h
  let z₀ : ℂ := if ε = .plus then 0 else -1
  have hev : L =ᶠ[nhds z₀] R := by
    have hn : ∀ᶠ z : ℂ in nhds z₀, convergenceHalfPlane ε z := by
      cases ε
      · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [z₀])
      · exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num [z₀])
    filter_upwards [hn] with z hz
    exact hch z hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_univ
    (Set.mem_univ z₀) hev (Set.mem_univ s)

end
end DedekindZetaZeroFree.KPActualResidueSources
