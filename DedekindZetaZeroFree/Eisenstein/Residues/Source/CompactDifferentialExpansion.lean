module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.CompactWordAdjoint

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts CurrentComplexBoundary
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem compactWord_of_expansion (s : ℝ)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (h : KPLiteralRaw.G F ζ hζ → ℂ)
    {κ : Type} [Fintype κ] (d : κ → ℂ) (f : κ → InfinitePlace F → PrincipalSeries s)
    (he : ∀a, h (finiteSlicePoint F ζ hζ c a)=∑j,d j*∏i,f j i (a i))
    (w : List (Fin (groupDimension F))) (k : KPMsGreenFlux.K F) :
    actualRightWord F ζ hζ w h (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) =
      ∑j,d j*pureCompact s (fun i=>matrixWord s (slotWords i (w.map (matrixLetter F))) (f j i)) k := by
  choose u hu using fun i => compactQuotient_surjective (k i)
  let a : InfinitePlace F → ComplexGL2 := fun i => complexSU2Embedding (u i)
  have hk : ∀i, Matrix.ProjGenLinGroup.mk (a i)=(k i).val := by
    intro i
    exact congrArg Subtype.val (hu i)
  have hp : KPMsGreenFlux.compactInsertion F ζ hζ k*c.val = finiteSlicePoint F ζ hζ c a := by
    unfold finiteSlicePoint KPMsGreenFlux.compactInsertion
    congr 2
    funext i
    exact (hk i).symm
  rw [hp,actualRightWord_finiteSlice]
  have hf : (fun a=>h (finiteSlicePoint F ζ hζ c a))=(fun a=>∑j,d j*∏i,f j i (a i)) := funext he
  rw [hf,tupleWord_sum_pure]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold pureCompact
  apply Finset.prod_congr rfl
  intro i hi
  rw [←hk i,pi_mk]
  simp only [KPCplxPrincipalSeriesCharts.rightTranslate,one_mul]

theorem source_compact_word_expansion
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ∃ n : ℕ, ∃ d : Fin n → ℂ, ∃ f : Fin n → InfinitePlace F → PrincipalSeries positiveParameter,
      ∀w k, actualRightWord F ζ hζ w t.val.val
        (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val) =
      ∑j,d j*pureCompact positiveParameter
        (fun i=>matrixWord positiveParameter (slotWords i (w.map (matrixLetter F))) (f j i)) k := by
  obtain ⟨U,n,v,f,hU,hf,he⟩ := ActualRaisingGeometry.actual_source_finite_pure_core F ζ hζ t
  refine ⟨n,fun j=>(v j).val.val.val c.val,f,?_⟩
  intro w k
  exact compactWord_of_expansion F ζ hζ positiveParameter c t.val.val _ f
    (fun a=>he a c) w k

theorem source_word_compact_continuous
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (w : List (Fin (groupDimension F))) :
    Continuous (fun k : KPMsGreenFlux.K F => actualRightWord F ζ hζ w t.val.val
      (KPMsGreenFlux.compactInsertion F ζ hζ k*c.val)) := by
  obtain ⟨n,d,f,he⟩ := source_compact_word_expansion F ζ hζ t c
  simp_rw [he]
  exact continuous_finset_sum _ (fun j _=>continuous_const.mul (pureCompact_continuous _ _))
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
