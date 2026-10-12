module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LogJetTransport
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexWeylBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField KPCplxPrincipalSeriesCharts KPCplxRotatedRapidDecay KPCplxJacquetFunctional
open ThetaRawSheetEnvelope.WeightedWhittakerSheets
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

theorem selected_arch_bounds_of_jacquet_identity
    (v : R.A.UnitQuotient) (w : InfinitePlace F)
    (κ : ℂˣ) (f : PrincipalSeries positiveParameter)
    (he : selectedComplexWeyl R C v w = standardWeylJacquet κ f)
    (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ 2 → ∀ z : w.Completionˣ,
      ‖ThetaExpansion.localWeylArchJet R C v w j z‖ ≤
        D * archPowerMajorant A (‖(z : w.Completion)‖ ^ 2) := by
  obtain ⟨D, hD, hb⟩ := exists_norm_iterate_logarithmicDerivative_standardWeylJacquet_le κ f A hA
  refine ⟨D, hD, ?_⟩
  intro j hj z
  have ht := archJet_norm_le_complex_jet R C v w j z
  rw [he] at ht
  have hn : ‖(Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z : ℂ)‖ =
      ‖(z : w.Completion)‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _
  exact ht.trans (by simpa only [hn] using
    (hb j hj (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z)))

theorem all_selected_arch_bounds_of_jacquet_identity
    (he : ∀ (v : R.A.UnitQuotient) (w : InfinitePlace F),
      ∃ (κ : ℂˣ) (f : PrincipalSeries positiveParameter),
        selectedComplexWeyl R C v w = standardWeylJacquet κ f)
    (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (v : R.A.UnitQuotient) (w : InfinitePlace F)
      (j : ℕ), j ≤ 2 → ∀ z : w.Completionˣ,
      ‖ThetaExpansion.localWeylArchJet R C v w j z‖ ≤
        D * archPowerMajorant A (‖(z : w.Completion)‖ ^ 2) := by
  have hb : ∀ i : R.A.UnitQuotient × InfinitePlace F,
      ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ 2 → ∀ z : i.2.Completionˣ,
        ‖ThetaExpansion.localWeylArchJet R C i.1 i.2 j z‖ ≤
          D * archPowerMajorant A (‖(z : i.2.Completion)‖ ^ 2) := by
    intro i
    obtain ⟨κ, f, hf⟩ := he i.1 i.2
    exact selected_arch_bounds_of_jacquet_identity R C i.1 i.2 κ f hf A hA
  letI : Finite R.A.UnitQuotient := C.sources.finite_companions
  letI : Fintype R.A.UnitQuotient := Fintype.ofFinite _
  choose D hD hbound using hb
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro v w j hj z
  exact (hbound (v, w) j hj z).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ (v, w)))
      (archPowerMajorant_nonneg A _ (sq_nonneg _)))

end DedekindZetaZeroFree.SheetRescaling

end
