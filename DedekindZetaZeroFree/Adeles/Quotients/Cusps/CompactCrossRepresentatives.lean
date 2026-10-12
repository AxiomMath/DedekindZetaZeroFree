module

public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CrossSectionRepresentatives

@[expose] public section

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

open NumberField

theorem compact_cross_representatives
    (F : Type) [Field F] [NumberField F]
    (hF : InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ B : Set (KPCuspCharts.Cross F), IsCompact B ∧
      ∀ p : KPCuspCharts.Cross F, ∃ γ : S, G.crossAction γ p ∈ B := by
  obtain ⟨P, B, hP, _, hB, _, hrep⟩ :=
    KPCuspSiegel.exists_compact_cross_section_representatives F hF S D G
  refine ⟨P ×ˢ B, hP.prod hB, ?_⟩
  intro p
  obtain ⟨γ, x, hx, b, hb, he⟩ := hrep (KPCuspCharts.toArch F (p, 0))
  obtain ⟨A, hA, hc⟩ := D.upper γ γ.property
  rw [G.actual_action γ A hA hc] at he
  have hmean := KPCuspCharts.toArch_meanHeight F G.positive_dimension (p, 0)
  have hp : KPCuspCharts.crossAffine F hF D.E D.integralUnits
      (D.ratio γ) (A 0 1 / A 1 1) p = (x, b) := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (congrFun he i)
    · apply Subtype.ext
      funext i
      have hi := congrArg Prod.snd (congrFun he i)
      simpa only [KPCuspCharts.crossAffine, KPCuspCharts.affine,
        KPCuspCharts.toArch, hmean, zero_add] using hi
  refine ⟨γ, ?_⟩
  rw [G.crossAction_formula γ A hA hc p, hp]
  exact ⟨hx, hb⟩

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth
