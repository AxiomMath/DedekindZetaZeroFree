module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.OpenCellIntegration
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedFourierContinuation
public import DedekindZetaZeroFree.Analysis.Complex.AnalyticFunctionImages
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexEvaluation
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteAnalyticSourceImage
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.FiniteEvaluationSeparation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField MeasureTheory KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxJacquetFunctional
open KPLiteralRaw KPLiteralScalarHCCompactOrbit MomentSources
open KPReferenceChange.StandardComplexImage.FamilyCorrect TraceHaarTransport FiniteFunctionSpaces
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

theorem adelic_arch_first_integral (f : KPAdeles F → ℂ)
    (hf : Integrable f (KPAdditiveHaar.adelicMeasure F)) :
    Integrable (fun t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F =>
      ∫ a : InfiniteAdeleRing F, f (a,t) ∂KPAdditiveHaar.archMeasure F)
      (KPAdditiveHaar.finiteMeasure F) ∧
    (∫ x : KPAdeles F, f x ∂KPAdditiveHaar.adelicMeasure F) =
      ∫ t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
        ∫ a : InfiniteAdeleRing F, f (a,t) ∂KPAdditiveHaar.archMeasure F
          ∂KPAdditiveHaar.finiteMeasure F := by
  letI := KPAdditiveHaar.archMeasure_isAddHaarMeasure F
  letI := KPAdditiveHaar.finiteMeasure_isAddHaarMeasure F
  letI : SigmaCompactSpace (InfiniteAdeleRing F) :=
    (PoissonArch.infiniteAdeleToSpace F).toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  letI : BorelSpace (KPAdeles F) := ⟨rfl⟩
  have hm : @Measurable (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
      (KPAdeles F) Prod.instMeasurableSpace (inferInstance : MeasurableSpace (KPAdeles F))
      (fun x => x) := by
    exact (@Continuous.measurable _ _ _ Prod.instMeasurableSpace _ _
      (inferInstance : MeasurableSpace (KPAdeles F)) _
      (fun x : InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F =>
        (x : KPAdeles F)) continuous_id)
  have hf' := hf
  rw [KPAdditiveHaar.adelicMeasure] at hf'
  have hp := (integrable_map_measure hf'.aestronglyMeasurable hm.aemeasurable).mp hf'
  refine ⟨hp.integral_prod_right, ?_⟩
  rw [KPAdditiveHaar.adelicMeasure]
  exact (integral_map hm.aemeasurable hf'.aestronglyMeasurable).trans (integral_prod_symm _ hp)

theorem selected_chamber_jacquet_image
    (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R)
    (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    ∃ T : Submodule ℂ (PrincipalSeries positiveParameter), FiniteDimensional ℂ T ∧
      ∀ s : ℂ, (1 / 3 : ℝ) < s.re →
      (fun g : ComplexGL2 => fourier R Q.dq
        (eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s)
        (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
          (Function.update (fun _ => 1) w g))) ∈
        ((spectralJacquetMap s).comp T.subtype).range := by
  obtain ⟨n,p,b,h,he⟩ := openCell_arch_integral_separation F R.A.zeta12
    R.A.primitive_zeta12 Q.K Q.iwasawa (Q.flat v)
  let T : Submodule ℂ (PrincipalSeries positiveParameter) :=
    Submodule.span ℂ (Set.range (fun i : Fin n => (h i w).val))
  have hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  letI := hT
  refine ⟨T,hT,?_⟩
  intro s hs
  have hsc : s ∈ chamber := by change (-1 / 6 : ℝ) < s.re; linarith
  let G := fun g : ComplexGL2 => archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
    (Function.update (fun _ => 1) w g)
  let f := fun (t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (g : ComplexGL2) =>
    ∫ a : InfiniteAdeleRing F, (Q.flat v).val s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (a,t) * G g) *
      star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ) ∂KPAdditiveHaar.archMeasure F
  have hh (g : ComplexGL2) := adelic_arch_first_integral
    (fun x : KPAdeles F => (Q.flat v).val s
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * G g) *
      star (adelicTraceQuotientCharacter F (QuotientAddGroup.mk x) : ℂ))
    (selected_open_cell_fourier_integrable R Q v s hs (G g))
  have hf : ∀ g, Integrable (fun t => f t g) (KPAdditiveHaar.finiteMeasure F) :=
    fun g => (hh g).1
  have hmem : ∀ t, f t ∈ ((spectralJacquetMap s).comp T.subtype).range := by
    intro t
    let c := fun i => b i * literalArchProduct F R.A.zeta12 R.A.primitive_zeta12
      Q.K (Q.flat v) (openCellFiniteArgument F R.A.zeta12 R.A.primitive_zeta12 t) (p i) *
      literalFiniteDeformation F R.A.zeta12 R.A.primitive_zeta12 Q.K Q.iwasawa s
        (openCellFiniteArgument F R.A.zeta12 R.A.primitive_zeta12 t) *
      star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)
    let d := fun i => c i * ∏ u ∈ Finset.univ.erase w, spectralJacquet (h i u).val s 1
    let u : Fin n → T := fun i => ⟨(h i w).val, Submodule.subset_span ⟨i,rfl⟩⟩
    refine ⟨∑ i, d i • u i, ?_⟩
    funext g
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.comp_apply, Submodule.subtype_apply, spectralJacquetMap_apply s hsc]
    dsimp only [f,G]
    rw [(he s hsc t (Function.update (fun _ => 1) w g)).2]
    apply Finset.sum_congr rfl
    intro i _
    have hprod : (∏ u, spectralJacquet (h i u).val s
        (Function.update (fun _ : InfinitePlace F => (1 : ComplexGL2)) w g u)) =
        spectralJacquet (h i w).val s g *
          ∏ u ∈ Finset.univ.erase w, spectralJacquet (h i u).val s 1 := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      rw [Function.update_of_ne (Finset.mem_erase.mp hu).1]
    rw [hprod]
    dsimp only [d,c,u]
    ring
  let J : T →ₗ[ℂ] (ComplexGL2 → ℂ) := (spectralJacquetMap s).comp T.subtype
  have hr := integral_mem_finite_linear_image (V := T) (KPAdditiveHaar.finiteMeasure F)
    J f (Filter.Eventually.of_forall hmem) hf
  convert hr using 1
  funext g
  rw [selected_chamber_fourier_unfolding R Q v s hs (G g), (hh g).2]
  rfl

theorem selected_residue_jacquet_image
    (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R)
    (T₀ : Realization R Q) (v : R.A.UnitQuotient) (w : InfinitePlace F) :
    ∃ f : PrincipalSeries positiveParameter, ∀ g : ComplexGL2,
      fourier R Q.dq (T₀.theta v)
        (archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
          (Function.update (fun _ => 1) w g)) =
      KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
        (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f) := by
  obtain ⟨T,hT,hch⟩ := selected_chamber_jacquet_image R Q v w
  letI := hT
  let G := fun g : ComplexGL2 => archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12
    (Function.update (fun _ => 1) w g)
  let J : ℂ → T →ₗ[ℂ] (ComplexGL2 → ℂ) := fun s => (spectralJacquetMap s).comp T.subtype
  have hzero : (0 : ℂ) ∈ chamber := by norm_num [chamber]
  have hinj : Function.Injective (J 0) := by
    intro f h he
    apply Subtype.ext
    apply KPCplxJacquetFunctional.jacquetEvaluation_injective
    funext g
    have hg := congrFun he g
    change jacquetEvaluation f.val g = jacquetEvaluation h.val g
    change KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
      (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f.val) =
      KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
        (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) h.val)
    simpa only [J, LinearMap.comp_apply, Submodule.subtype_apply,
      spectralJacquetMap_apply 0 hzero, spectralJacquet_zero,
      DedekindZetaZeroFree.TraceHaarTransport.standardComplexParameter,
      DedekindZetaZeroFree.SheetRescaling.standardComplexParameter] using hg
  have hJa : ∀ f g, AnalyticOnNhd ℂ (fun s => J s f g) chamber := by
    intro f g s hs
    apply (spectralJacquet_analytic f.val g s hs).congr
    have hO : IsOpen chamber := by
      exact isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hO.mem_nhds hs] with t ht
    exact (spectralJacquetMap_apply t ht f.val g).symm
  choose I hm hc hp using fun g => selected_fourier_continuation_exists T₀ v (G g)
  let H := fun s g => fourier R Q.dq (T₀.cleared v s) (G g)
  have hdom : chamber = KPContinuation.spectralDomain := by
    ext s
    simp only [chamber, KPContinuation.spectralDomain, Set.mem_setOf_eq]

  have hmem : H 0 ∈ (J 0).range := by
    apply residue_mem_analytic_function_image (V := T) J hinj hzero
      (hdom.symm ▸ KPContinuation.spectralDomain_isConnected.isPreconnected)
      (isOpen_lt continuous_const Complex.continuous_re)
      (U := {s : ℂ | (1 / 3 : ℝ) < s.re})
      (fun s hs => by change (-1 / 6 : ℝ) < s.re; change (1/3 : ℝ) < s.re at hs; linarith)
      1 (by norm_num) hJa (fun s g => I g s) H
    · intro g
      rw [hdom]
      exact hm g
    · intro g
      exact selected_fourier_cleared_analyticOnNhd T₀ v (G g) 0
        (Metric.mem_ball_self T₀.radius_pos)
    · intro g
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T₀.radius_pos),
        self_mem_nhdsWithin] with s hs hn
      exact hp g s hs hn
    · intro s hs
      convert hch s hs using 1
      funext g
      exact hc g s hs
  obtain ⟨f,hf⟩ := hmem
  refine ⟨f.val, ?_⟩
  intro g
  have hg := congrFun hf g
  simpa only [J, H, Realization.theta, LinearMap.comp_apply, Submodule.subtype_apply,
    spectralJacquetMap_apply 0 hzero, spectralJacquet_zero,
    DedekindZetaZeroFree.TraceHaarTransport.standardComplexParameter,
    DedekindZetaZeroFree.SheetRescaling.standardComplexParameter] using hg.symm

end DedekindZetaZeroFree.SheetRescaling

end

section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField MeasureTheory KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPLiteralRaw KPLiteralScalarHCCompactOrbit MomentSources
open KPReferenceChange.StandardComplexImage.FamilyCorrect
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

end DedekindZetaZeroFree.SheetRescaling

end
end
