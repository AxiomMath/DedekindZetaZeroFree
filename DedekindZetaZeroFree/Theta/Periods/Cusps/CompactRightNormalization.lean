module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryFrameAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.CurrentNativeBoundaryFrame
open KPMsActualAngularSource KPMsNativeOffsetMass
open _root_.DedekindZetaZeroFree.KPContFlatLogNormSmooth renaming compact_insertion → compact_insertion
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem compact_mem (k : KPMsGreenFlux.K F) :
    KPMsGreenFlux.compactInsertion F ζ hζ k ∈ (nativeDatum F ζ hζ).K := by
  have hk (w : NumberField.InfinitePlace F) : ∃ q : KPCplxCharacterHaar.ComplexSU2,
      Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding q) = (k w).val :=
    (k w).property
  choose q hq using hk
  have he : (fun w => (k w).val) = fun w =>
      Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (q w)) := by
    funext w
    exact (hq w).symm
  unfold KPMsGreenFlux.compactInsertion
  rw [he]
  exact compact_insertion F ζ hζ q

theorem normalization_right_compact
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ g : G F ζ hζ)
    (k : KPMsGreenFlux.K F) :
    framedNormalization F ζ hζ (nativeDatum F ζ hζ) B σ
      (g * KPMsGreenFlux.compactInsertion F ζ hζ k) =
    framedNormalization F ζ hζ (nativeDatum F ζ hζ) B σ g *
      KPMsGreenFlux.compactInsertion F ζ hζ k := by
  let a : (nativeDatum F ζ hζ).K := ⟨_,compact_mem k⟩
  have hr : framedRadius F ζ hζ (nativeDatum F ζ hζ) σ (g*a.val) =
      framedRadius F ζ hζ (nativeDatum F ζ hζ) σ g := by
    apply Subtype.ext
    dsimp only [framedRadius]
    rw [← mul_assoc,KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact]
  change framedNormalization F ζ hζ (nativeDatum F ζ hζ) B σ (g*a.val) = _
  unfold framedNormalization
  rw [hr]
  group
  rfl
end DedekindZetaZeroFree.CurrentNativeBoundaryFrame

end
