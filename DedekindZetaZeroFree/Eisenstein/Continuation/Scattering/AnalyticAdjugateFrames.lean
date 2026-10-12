module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Scattering.LinearFactorization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.LocalProducts.CompactChangeAnalyticity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPLocalStoneVonNeumann renaming inducedCosetEquiv → inducedCosetEquiv
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem scatteringSlotOutput_coordinate_analytic (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (g : Raw R.A) (f : Plus R.A P C (Sum.inr q))
    (h : actualTorus F ζ hζ q) :
    AnalyticOnNhd ℂ (fun z => (scatteringSlotOutput R P C q μ hμ z g f).val h)
      KPContinuation.spectralDomain := by
  exact KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity.CorrectedOutputAnalytic.finite_corrected_full_right_coordinate_analytic
    F ζ hζ q (C.canonical q) (C.polarization q) (finiteIntegralIwasawa R P C q) μ hμ
    ((compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus 0).symm f)
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q))) h

theorem scatteringSlotOutput_frame (q : KPFinitePlace F)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
    (g : Raw R.A) :
    ∃ (ι : Type) (_ : Fintype ι) (e : LocalFiber F ζ hζ P C q ≃ₗ[ℂ] (ι → ℂ))
      (tests : ι → Plus R.A P C (Sum.inr q)) (d : ℂ → ℂ)
      (c : Plus R.A P C (Sum.inr q) → ℂ → ι → ℂ),
      AnalyticOnNhd ℂ d KPContinuation.spectralDomain ∧ d 0 = 1 ∧
      (∀ f i, AnalyticOnNhd ℂ (fun z => c f z i) KPContinuation.spectralDomain) ∧
      (∀ f, c f 0 = e (scatteringSlotOutput R P C q μ hμ 0 g f)) ∧
      (∀ z f, d z • scatteringSlotOutput R P C q μ hμ z g f =
        ∑ i, c f z i • scatteringSlotOutput R P C q μ hμ z g (tests i)) := by
  let H := (C.polarization q).L.comap (C.canonical q).heisenberg.π
  let ι := actualTorus F ζ hζ q ⧸ H
  letI : Fintype ι := Fintype.ofFinite _
  letI : DecidableEq ι := Classical.decEq _
  let e : LocalFiber F ζ hζ P C q ≃ₗ[ℂ] (ι → ℂ) :=
    inducedCosetEquiv H (C.polarization q).ωL.toMonoidHom
  let h (i : ι) := Function.surjInv (QuotientGroup.mk'_surjective H) i
  have he (v : LocalFiber F ζ hζ P C q) (i : ι) : e v i = v.val (h i) := rfl
  have ht : ∀ i : ι, ∃ f : Plus R.A P C (Sum.inr q),
      scatteringSlotOutput R P C q μ hμ 0 g f = e.symm (Pi.single i 1) := by
    intro i
    obtain ⟨f, hf⟩ := actualCanonicalForwardMap_evaluation_surjective F ζ hζ q (C.canonical q)
      (C.polarization q) μ hμ
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (-1) * g (Sum.inr q)))
      (e.symm (Pi.single i 1))
    exact ⟨f, (scatteringSlotOutput_zero R P C q μ hμ g f).trans hf⟩
  choose tests htests using ht
  let A : ℂ → Matrix ι ι ℂ := fun z i j => e (scatteringSlotOutput R P C q μ hμ z g (tests j)) i
  have hA : ∀ i j, AnalyticOnNhd ℂ (fun z => A z i j) KPContinuation.spectralDomain := by
    intro i j
    simp only [A, he]
    exact scatteringSlotOutput_coordinate_analytic R P C q μ hμ g (tests j) (h i)
  have hzero : A 0 = 1 := by
    ext i j
    simp only [A, htests, LinearEquiv.apply_symm_apply, Matrix.one_apply]
    simp [Pi.single_apply, eq_comm]
  have hdet : AnalyticOnNhd ℂ (fun z => (A z).det) KPContinuation.spectralDomain := by
    intro z hz
    simp_rw [Matrix.det_apply]
    apply Finset.analyticAt_fun_sum
    intro σ _
    apply AnalyticAt.const_smul
    apply Finset.analyticAt_fun_prod
    intro i _
    exact hA (σ i) i z hz
  have hadj : ∀ i j, AnalyticOnNhd ℂ (fun z => (A z).adjugate i j) KPContinuation.spectralDomain := by
    intro i j z hz
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply]
    apply Finset.analyticAt_fun_sum
    intro σ _
    apply AnalyticAt.const_smul
    apply Finset.analyticAt_fun_prod
    intro k _
    by_cases hk : σ k = j
    · simp only [Matrix.updateRow_self, hk]
      exact analyticAt_const
    · simp only [Matrix.updateRow_ne hk]
      exact hA (σ k) k z hz
  let c : Plus R.A P C (Sum.inr q) → ℂ → ι → ℂ := fun f z =>
    (A z).adjugate.mulVec (e (scatteringSlotOutput R P C q μ hμ z g f))
  have hc : ∀ f i, AnalyticOnNhd ℂ (fun z => c f z i) KPContinuation.spectralDomain := by
    intro f i z hz
    change AnalyticAt ℂ (fun z => ∑ j, (A z).adjugate i j *
      e (scatteringSlotOutput R P C q μ hμ z g f) j) z
    apply Finset.analyticAt_fun_sum
    intro j _
    apply (hadj i j z hz).mul
    simp only [he]
    exact scatteringSlotOutput_coordinate_analytic R P C q μ hμ g f (h j) z hz
  refine ⟨ι, inferInstance, e, tests, fun z => (A z).det, c, hdet, ?_, hc, ?_, ?_⟩
  · change (A 0).det = 1
    rw [hzero, Matrix.det_one]
  · intro f
    simp [c, hzero, Matrix.adjugate_one]
  · intro z f
    have hm : (A z).mulVec (c f z) = (A z).det •
        e (scatteringSlotOutput R P C q μ hμ z g f) := by
      dsimp only [c]
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    apply e.injective
    rw [map_smul, map_sum]
    ext i
    have hi := congrFun hm i
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ j, e (scatteringSlotOutput R P C q μ hμ z g (tests j)) i * c f z j) =
      (A z).det * e (scatteringSlotOutput R P C q μ hμ z g f) i at hi
    rw [← hi]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
