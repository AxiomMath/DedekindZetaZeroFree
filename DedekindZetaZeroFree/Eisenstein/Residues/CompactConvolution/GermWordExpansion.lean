module

public import DedekindZetaZeroFree.Eisenstein.Residues.Source.CompactDifferentialExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts CurrentComplexBoundary
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem compactWord_of_germ_expansion (s : ℝ)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (h : KPLiteralRaw.G F ζ hζ → ℂ)
    {κ : Type} [Fintype κ] (d : κ → ℂ) (f : κ → InfinitePlace F → PrincipalSeries s)
    (he : ∀u : InfinitePlace F → ComplexSU2,
      (fun a => h (finiteSlicePoint F ζ hζ c a)) =ᶠ[𝓝 (fun i => complexSU2Embedding (u i))]
        (fun a => ∑j,d j*∏i,f j i (a i)))
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
  have hw := (tupleWord_germ (w.map (matrixLetter F)) (he u)).eq_of_nhds
  rw [hw,tupleWord_sum_pure]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold pureCompact
  apply Finset.prod_congr rfl
  intro i hi
  rw [←hk i,pi_mk]
  simp only [KPCplxPrincipalSeriesCharts.rightTranslate,one_mul]
  rfl

end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
