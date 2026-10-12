module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.TranslatedBigCellCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_raw_group_chart_contDiffOn_source (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => h (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  apply contDiffOn_of_locally_contDiffOn
  intro z₀ hz₀
  obtain ⟨O, q, hO, hzO, hq, hqO, heq⟩ :=
    literal_group_chart_local_transition F ζ hζ g z₀ hz₀
  refine ⟨O, hO, hzO, ?_⟩
  have H := (hh.2.1
    (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z₀ * g)).comp hq hqO
  apply (H.congr (fun z hz => congrArg h (heq z hz))).mono
  exact Set.inter_subset_right

end DedekindZetaZeroFree.KPLiteralChamber

end
