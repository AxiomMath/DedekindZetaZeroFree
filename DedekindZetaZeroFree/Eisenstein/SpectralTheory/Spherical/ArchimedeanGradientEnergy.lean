module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ProductGradientEnergy

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric
open KPSmoothActualFlowData
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming flow_apply → flow_apply
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets renaming pgl_action_out → pgl_action_out

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

include ζ hζ

private theorem arch_first (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (a : GInfinity F) (i : Fin (KPCuspLogShape.dimension F)) (j : Fin 6) :
    archRight F (KPCusp.complexPlace F i) j (f ∘ KPMsFixedHaarDisintegration.archBasepoint F) a =
    localD j (fun b => f (fun v => KPArch.action
      (Function.update (fun v => (a (KPCusp.complexPlace F v)).out) i b v) (0,0)))
      (a (KPCusp.complexPlace F i)).out := by
  unfold archRight localD
  congr 1
  funext t
  apply congrArg f
  funext v
  change KPArch.action ((a * flow F (KPCusp.complexPlace F i,j) t) (KPCusp.complexPlace F v)).out (0,0) = _
  simp only [Pi.mul_apply, flow_apply]
  by_cases hv : v = i
  · subst v
    simp only [↓reduceIte, Function.update_self]
    have hm : Matrix.ProjGenLinGroup.mk (a (KPCusp.complexPlace F i)).out =
        a (KPCusp.complexPlace F i) := Quotient.out_eq _
    conv_lhs => rw [← hm, ← map_mul]
    exact pgl_action_out _ _
  · have hp : KPCusp.complexPlace F v ≠ KPCusp.complexPlace F i := by
      intro he
      apply hv
      exact (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm.injective he
    simp only [hp, ↓reduceIte, mul_one, Function.update_of_ne hv]

def archEnergy (h : GInfinity F → ℂ) (a : GInfinity F) : ℝ :=
  ∑ w : NumberField.InfinitePlace F,
    ((‖archRight F w 0 h a‖^2 + ‖archRight F w 1 h a‖^2) / 4 +
      (‖archRight F w 2 h a‖^2 + ‖archRight F w 3 h a‖^2 +
        ‖archRight F w 4 h a‖^2 + ‖archRight F w 5 h a‖^2) / 2)

 theorem arch_energy (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : GInfinity F) :
    archEnergy F (f ∘ KPMsFixedHaarDisintegration.archBasepoint F) a =
      KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1 f
        (KPMsFixedHaarDisintegration.archBasepoint F a) ^ 2 := by
  change _ = KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1 f
    (fun i => KPArch.action (a (KPCusp.complexPlace F i)).out (0,0)) ^ 2
  rw [← product_energy _ f hf (fun i => (a (KPCusp.complexPlace F i)).out)]
  unfold archEnergy productEnergy
  rw [← (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm i =
    KPCusp.complexPlace F i from rfl, arch_first F ζ hζ, localEnergy]

 theorem original_slice_energy
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (e : (GInfinity F × KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) ≃ₜ*
      KPGlobalTorusFunctionData.G F ζ hζ)
    (he : ∀ a c, e (a,c) = archimedeanInsertion F ζ hζ a * c.val)
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hslice : ∀ b, h (e (b,c)) = f (KPMsFixedHaarDisintegration.archBasepoint F b))
    (a : GInfinity F) :
    (∑ w : NumberField.InfinitePlace F,
      ((‖KPMsGreenFlux.rightDerivative F ζ hζ w 0 h (e (a,c))‖^2 +
        ‖KPMsGreenFlux.rightDerivative F ζ hζ w 1 h (e (a,c))‖^2) / 4 +
      (‖KPMsGreenFlux.rightDerivative F ζ hζ w 2 h (e (a,c))‖^2 +
        ‖KPMsGreenFlux.rightDerivative F ζ hζ w 3 h (e (a,c))‖^2 +
        ‖KPMsGreenFlux.rightDerivative F ζ hζ w 4 h (e (a,c))‖^2 +
        ‖KPMsGreenFlux.rightDerivative F ζ hζ w 5 h (e (a,c))‖^2) / 2)) =
      KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1 f
        (KPMsFixedHaarDisintegration.archBasepoint F a) ^ 2 := by
  have hright (w : NumberField.InfinitePlace F) (j : Fin 6) (b : GInfinity F) :
      KPMsGreenFlux.rightDerivative F ζ hζ w j h (e (b,c)) =
        archRight F w j (fun x => h (e (x,c))) b := by
    unfold KPMsGreenFlux.rightDerivative archRight
    congr 1
    funext t
    congr 1
    have hi : e (flow F (w,j) t,1) = archimedeanInsertion F ζ hζ (flow F (w,j) t) := by
      rw [he]; simp
    rw [← hi, ← map_mul]
    simp
  simp_rw [hright]
  rw [show (fun b => h (e (b,c))) = f ∘ KPMsFixedHaarDisintegration.archBasepoint F
    from funext hslice]
  exact arch_energy F ζ hζ f hf a

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric

end
