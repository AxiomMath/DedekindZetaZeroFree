module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def chamberIndex (c : KPChamberBruhatTwoCells.RationalQuotient F) : KPHeightSeries.P1 F :=
  chamberCosetIndex F c

theorem chamberHeightBound (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    ∃ B : ℝ, ∀ c : KPChamberBruhatTwoCells.RationalQuotient F,
      ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤
        B * KPHeightSeries.term (Projectivization.mulHeight (K := F))
          (2 / 3 + s.re) (chamberIndex F c) :=
  chamberCosetHeightBound F ζ hζ K hK f s hs g

theorem summable_of_chamberHeightBound {u : KPChamberBruhatTwoCells.RationalQuotient F → ℂ}
    {a : ℝ} (ha : 1 < a) {B : ℝ}
    (hB : ∀ c, ‖u c‖ ≤
      B * KPHeightSeries.term (Projectivization.mulHeight (K := F)) a (chamberIndex F c)) :
    Summable u := by
  have hsum := (KPHeightSeries.relativeHeight_summable_tail F a ha).1
  have hmaj : Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      B * KPHeightSeries.term (Projectivization.mulHeight (K := F)) a (chamberCosetIndex F c)) :=
    (hsum.comp_injective (chamberCosetIndex_injective F)).mul_left B
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun c => norm_nonneg _) hB hmaj)

theorem chamberConvergence (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      f.val s (rationalLift F ζ hζ (Quotient.out c) * g)) := by
  have hexp : 1 < (2 : ℝ) / 3 + s.re := by linarith
  obtain ⟨B, hB⟩ := chamberHeightBound F ζ hζ K hK f s hs g
  exact summable_of_chamberHeightBound F hexp hB

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
