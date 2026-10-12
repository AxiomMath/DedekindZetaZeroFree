module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.SL2.ArchimedeanInvariance
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightTranslation.CasimirCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualArchSL2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
local notation "ins" => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
open KPMsGreenFlux

theorem casimir_zero_of_arch_invariant (θ : G → ℂ) (hs : RawWordKFinite.NativeSmooth θ)
    (hθ : ∀ k g, θ (ins k * g) = θ g) (g : G) : casimir F ζ hζ θ g = 0 := by
  let f : G → ℂ := fun a => θ (a*g)
  have hd (w : InfinitePlace F) (j : Fin 6) (k : KPSmoothActualFlowData.GInfinity F) :
      rightDerivative F ζ hζ w j f (ins k) = 0 := by
    unfold rightDerivative
    have he : (fun t : ℝ => f (ins k * ins (KPSmoothActualFlowData.flow F (w,j) t))) =
        fun _ : ℝ => θ g := by
      funext t
      change θ ((ins k * ins (KPSmoothActualFlowData.flow F (w,j) t))*g) = θ g
      rw [mul_assoc, hθ, hθ]
    rw [he]
    exact deriv_const _ _
  have hdd (w : InfinitePlace F) (i j : Fin 6) :
      rightDerivative F ζ hζ w i (rightDerivative F ζ hζ w j f) 1 = 0 := by
    unfold rightDerivative
    change deriv (fun t : ℝ => rightDerivative F ζ hζ w j f
      (1 * ins (KPSmoothActualFlowData.flow F (w,i) t))) 0 = 0
    simp only [one_mul, hd]
    exact deriv_const _ _
  have he := ResidualFullGroupTranslation.casimir_right_translate θ hs 1 g
  rw [one_mul] at he
  rw [← he]
  change casimir F ζ hζ f 1 = 0
  simp [casimir, hdd]

end DedekindZetaZeroFree.FourierContinuation.ResidualArchSL2

end
