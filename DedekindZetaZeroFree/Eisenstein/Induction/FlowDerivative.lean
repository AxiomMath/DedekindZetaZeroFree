module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CanonicalExtension
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.LieDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPSmoothActualFlowData KPContActualSphericalRightFieldIdentification
open KPMsClearedTruncationL2.NativeWordBridge
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_hasDerivAt_of_chart_smooth → rightWord_hasDerivAt_of_chart_smooth
open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word → word
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem raw_flow_derivative (u : KPLiteralRaw.G F ζ hζ → ℂ)
    (hu : KPLiteralRaw.Smooth F ζ hζ u) (b : Fin (groupDimension F))
    (g : KPLiteralRaw.G F ζ hζ) (t : ℝ) :
    HasDerivAt (fun r=>u (g*archimedeanInsertion F ζ hζ (flow F (wordIndexEquiv F b) r)))
      (actualRight F ζ hζ b u (g*archimedeanInsertion F ζ hζ (flow F (wordIndexEquiv F b) t))) t := by
  let a : ℝ → KPLiteralRaw.G F ζ hζ := fun r=>archimedeanInsertion F ζ hζ (flow F (wordIndexEquiv F b) r)
  have ha (r s : ℝ) : a (r+s)=a r*a s := by
    dsimp [a]
    rw [(flow_properties F _).2.1,(archimedean_insertion_properties F ζ hζ).2.1]
  have hz := rightWord_hasDerivAt_of_chart_smooth F ζ hζ u hu.2.1 [] (wordIndexEquiv F b) (g*a t)
  have hz₁ := hz
  rw [←sub_self t] at hz₁
  have hp := hz₁.comp_sub_const t t
  have he : (fun r : ℝ=>u ((g*a t)*a (r-t))) = fun r=>u (g*a r) := by
    funext r
    rw [mul_assoc,←ha,add_sub_cancel]
  change HasDerivAt (fun r=>u ((g*a t)*a (r-t)))
    (KPMsGreenFlux.rightDerivative F ζ hζ (wordIndexEquiv F b).1 (wordIndexEquiv F b).2 u (g*a t)) t at hp
  rw [he,←ResidualUpperWordInterchange.actualRight_eq] at hp
  exact hp
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
