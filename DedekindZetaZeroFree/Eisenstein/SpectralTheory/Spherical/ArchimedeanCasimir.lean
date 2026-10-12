module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ProductCasimir

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

def archRight (w : NumberField.InfinitePlace F) (j : Fin 6)
    (f : GInfinity F → ℂ) (a : GInfinity F) : ℂ :=
  deriv (fun t : ℝ => f (a * flow F (w,j) t)) 0

def archCasimir (f : GInfinity F → ℂ) (a : GInfinity F) : ℂ :=
  ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
    (archRight F w 0 (archRight F w 0 f) a - archRight F w 1 (archRight F w 1 f) a +
      2 * (archRight F w 2 (archRight F w 4 f) a + archRight F w 4 (archRight F w 2 f) a -
        archRight F w 3 (archRight F w 5 f) a - archRight F w 5 (archRight F w 3 f) a))

include ζ hζ

private theorem arch_twice (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (a : GInfinity F) (i : Fin (KPCuspLogShape.dimension F)) (j k : Fin 6) :
    archRight F (KPCusp.complexPlace F i) j
      (archRight F (KPCusp.complexPlace F i) k (f ∘ KPMsFixedHaarDisintegration.archBasepoint F)) a =
    localD j (localD k (fun b => f (fun v => KPArch.action
      (Function.update (fun v => (a (KPCusp.complexPlace F v)).out) i b v) (0,0))))
      (a (KPCusp.complexPlace F i)).out := by
  unfold archRight localD
  congr 1
  funext t
  congr 1
  funext u
  apply congrArg f
  funext v
  change KPArch.action (((a * flow F (KPCusp.complexPlace F i,j) t) *
      flow F (KPCusp.complexPlace F i,k) u) (KPCusp.complexPlace F v)).out (0,0) = _
  simp only [Pi.mul_apply, flow_apply]
  by_cases hv : v = i
  · subst v
    simp only [↓reduceIte, Function.update_self]
    have hm : Matrix.ProjGenLinGroup.mk (a (KPCusp.complexPlace F i)).out =
        a (KPCusp.complexPlace F i) := Quotient.out_eq _
    conv_lhs => rw [← hm, ← map_mul, ← map_mul]
    exact pgl_action_out _ _
  · have hp : KPCusp.complexPlace F v ≠ KPCusp.complexPlace F i := by
      intro he
      apply hv
      exact (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm.injective he
    simp only [hp, ↓reduceIte, mul_one, Function.update_of_ne hv]

 theorem arch_casimir (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : GInfinity F) :
    archCasimir F (f ∘ KPMsFixedHaarDisintegration.archBasepoint F) a =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f
        (KPMsFixedHaarDisintegration.archBasepoint F a) := by
  change _ = KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f
    (fun i => KPArch.action (a (KPCusp.complexPlace F i)).out (0,0))
  rw [← product_casimir _ f hf (fun i => (a (KPCusp.complexPlace F i)).out)]
  unfold archCasimir productCasimir
  rw [← (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  change -((1 : ℂ) / 4) * _ = _
  simp only [show (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).symm i =
    KPCusp.complexPlace F i from rfl, arch_twice F ζ hζ, localCasimir]

 theorem original_slice_casimir
    (h : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (e : (GInfinity F × KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ) ≃ₜ*
      KPGlobalTorusFunctionData.G F ζ hζ)
    (he : ∀ a c, e (a,c) = archimedeanInsertion F ζ hζ a * c.val)
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (f : KPArch.Space (KPCuspLogShape.dimension F) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hslice : ∀ b, h (e (b,c)) = f (KPMsFixedHaarDisintegration.archBasepoint F b))
    (a : GInfinity F) :
    KPMsGreenFlux.casimir F ζ hζ h (e (a,c)) =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) f
        (KPMsFixedHaarDisintegration.archBasepoint F a) := by
  have hright (q : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
      (w : NumberField.InfinitePlace F) (j : Fin 6) (b : GInfinity F) :
      KPMsGreenFlux.rightDerivative F ζ hζ w j q (e (b,c)) =
        archRight F w j (fun x => q (e (x,c))) b := by
    unfold KPMsGreenFlux.rightDerivative archRight
    congr 1
    funext t
    congr 1
    have hi : e (flow F (w,j) t,1) = archimedeanInsertion F ζ hζ (flow F (w,j) t) := by
      rw [he]; simp
    rw [← hi, ← map_mul]
    simp
  have hcas : KPMsGreenFlux.casimir F ζ hζ h (e (a,c)) =
      archCasimir F (fun b => h (e (b,c))) a := by
    unfold KPMsGreenFlux.casimir archCasimir
    simp_rw [hright]
  rw [hcas, show (fun b => h (e (b,c))) = f ∘ KPMsFixedHaarDisintegration.archBasepoint F
    from funext hslice]
  exact arch_casimir F ζ hζ f hf a

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric

end
