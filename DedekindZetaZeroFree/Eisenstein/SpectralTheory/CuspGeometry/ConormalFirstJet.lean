module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.BottomRowRadialContraction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.ConormalFirstJet
open KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming bottomRowJet → bottomRowJet
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming normalRadialJet_eq_bottomRowJet → normalRadialJet_eq_bottomRowJet

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 def lift (u : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : KPSmoothActualFlowData.LieCoordinates F → ℂ :=
  fun a => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.exponential F a))

 theorem rightDerivative_eq_fderiv (u : Cover F ζ hζ → ℂ) (hu : Smooth F ζ hζ u)
  (g : Cover F ζ hζ) (w : NumberField.InfinitePlace F) (j : Fin 6) :
  rightDerivative F ζ hζ w j u g =
  fderiv ℝ (lift u g) 0 (Pi.single (w,j) 1) := by
  have hs : DifferentiableAt ℝ (lift u g) 0 :=
    ((hu.2 g).differentiable (by simp) 0)
  have hd : HasDerivAt (fun t : ℝ => (Pi.single (w,j) t : KPSmoothActualFlowData.LieCoordinates F))
    (Pi.single (w,j) 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro b
    by_cases hb : b = (w,j)
    · subst b; convert hasDerivAt_id (0 : ℝ) using 1 <;> try simp
      rfl
    · simpa [Pi.single_apply, hb] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hs' : HasFDerivAt (lift u g) (fderiv ℝ (lift u g) 0) (Pi.single (w,j) 0) := by
    simpa using hs.hasFDerivAt
  have h := hs'.comp_hasDerivAt 0 hd
  have heq : (fun t : ℝ => lift u g (Pi.single (w,j) t)) =
    (fun t : ℝ => u (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F (w,j) t))) := by
    funext t
    unfold lift KPSmoothActualFlowData.flow
    congr 4
    funext b
    by_cases hb : b = (w,j) <;> simp [hb]
  change HasDerivAt (fun t => lift u g (Pi.single (w,j) t)) _ 0 at h
  rw [heq] at h
  simpa [rightDerivative] using h.deriv

 theorem exponential_direction_hasDerivAt (u : Cover F ζ hζ → ℂ)
  (hu : Smooth F ζ hζ u) (g : Cover F ζ hζ) (a : KPSmoothActualFlowData.LieCoordinates F) :
  HasDerivAt (fun t : ℝ => lift u g (t • a)) (fderiv ℝ (lift u g) 0 a) 0 := by
  have hd := (hasDerivAt_id (0 : ℝ)).smul_const a
  have hdiff : DifferentiableAt ℝ (lift u g) 0 :=
    ((hu.2 g).differentiable (by simp) 0)
  have hs : HasFDerivAt (lift u g) (fderiv ℝ (lift u g) 0) ((0 : ℝ) • a) := by
    simpa using hdiff.hasFDerivAt
  convert hs.comp_hasDerivAt 0 hd using 1 <;> try simp
  rfl

end DedekindZetaZeroFree.KPMsSameContinuationGreen.ConormalFirstJet

end
