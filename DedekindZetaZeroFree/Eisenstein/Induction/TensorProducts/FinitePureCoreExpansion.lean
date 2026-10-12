module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeCore.UniformFiniteLevel
public import DedekindZetaZeroFree.Eisenstein.Induction.FiniteEvaluation.SphericalPGLCoreRealization
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactFiniteEvaluationSeparation

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry
private theorem sourceCore_le_scalarSmooth_port
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    KPMsRationalCompactCrossPairing.sourceCore F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ) ≤
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  unfold KPMsRationalCompactCrossPairing.sourceCore KPGlobalEisensteinData.hcHeckeCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left
private theorem source_common_level_port
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U ∧
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      ∀ s g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        (KPContFlatSourceRecipe.flatR F ζ hζ s t).val (g * u.val) =
          (KPContFlatSourceRecipe.flatR F ζ hζ s t).val g := by
  obtain ⟨V, hV⟩ := KPGlobalResidualKernel.ScatteringResidue.scalarSmooth_exists_right_level
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) t.val
    (sourceCore_le_scalarSmooth_port F ζ hζ t.property)
  obtain ⟨K, hK⟩ := KPCompactFiniteLevel.exists_level F ζ hζ
  let U : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
    ⟨V.toOpenSubgroup ⊓ K.toOpenSubgroup, V.isCompact.inter_right K.toOpenSubgroup.isClosed⟩
  have hUV : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ V := Subgroup.map_mono inf_le_left
  have hUK : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ K := Subgroup.map_mono inf_le_right
  have halpha (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
      KPContFlatSourceRecipe.alpha F ζ hζ (g * u.val) = KPContFlatSourceRecipe.alpha F ζ hζ g :=
    KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g ⟨u.val, hK (hUK u.property)⟩
  refine ⟨U, ?_, hUK.trans hK, ?_⟩
  · intro g u
    refine ⟨hV g ⟨u.val, hUV u.property⟩, ?_⟩
    rw [halpha g u, sub_self, Complex.ofReal_zero, zero_mul]
  · intro s g u
    rw [KPContFlatSourceRecipe.flatR_formula, KPContFlatSourceRecipe.flatR_formula,
      halpha g u, hV g ⟨u.val, hUV u.property⟩]

open ActualRaisingLocal.SphericalReseeding

theorem actual_source_finite_pure_core
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (n : ℕ) (v : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U)
      (f : Fin n → NumberField.InfinitePlace F →
        KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter),
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      (∀ j w, KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter (f j w)) ∧
      ∀ (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          ∑ j, (v j).val.val.val c.val * ∏ w, f j w (a w) := by
  obtain ⟨U₀,htU,hUK,_⟩ := source_common_level_port F ζ hζ t
  obtain ⟨n,m,k,A,f,hf,he⟩ := actual_source_uniform_finite_evaluation_separation F ζ hζ t
  have hb := fun j : Fin n => actual_source_finite_evaluation_spherical_reseeding F ζ hζ t
    U₀ htU hUK m k (A j)
  choose V v hV hVK hv hvfiber using hb
  let H := U₀.toOpenSubgroup ⊓ Finset.univ.inf (fun j : Fin n => (V j).toOpenSubgroup)
  let U : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
    ⟨H, U₀.isCompact.of_isClosed_subset H.isClosed (fun _ hx => hx.1)⟩
  have hUU : U.toOpenSubgroup ≤ U₀.toOpenSubgroup := inf_le_left
  have hUV (j : Fin n) : U.toOpenSubgroup ≤ (V j).toOpenSubgroup :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
  have hglobal (j : Fin n) : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ (V j) := Subgroup.map_mono (hUV j)
  let vv : Fin n → KPContActualSphericalFlatStage.Stage F ζ hζ U := fun j =>
    ⟨(v j).val, (fun g u => (v j).property.1 g ⟨u.val,hglobal j u.property⟩), (v j).property.2⟩
  refine ⟨U,n,vv,f,(Subgroup.map_mono hUU).trans hUK,hf,?_⟩
  intro a c
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := hv j (fun _ => 1) c
  simp only [sphericalProduct_one, one_mul] at hc
  have hInsertion : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (1 : KPCplxCharacterHaar.ComplexGL2)) = 1 := by
    have h := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
    convert h using 1
    congr 1
  rw [hInsertion,one_mul] at hc
  exact congrArg (fun z => z * ∏ w, f j w (a w)) hc.symm
end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry

end
