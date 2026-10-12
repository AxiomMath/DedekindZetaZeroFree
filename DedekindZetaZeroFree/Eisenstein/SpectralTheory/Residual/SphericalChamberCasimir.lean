module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ChamberCasimir
public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordChamberReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContActualSphericalRightFieldIdentification KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_flat_casimir → native_flat_casimir
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_second_word → native_second_word
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming nativeIndex → nativeIndex
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming spherical_word_chamber → spherical_word_chamber
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
theorem actual_spherical_chamber_casimir
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (s : ℂ) (hs : (1/3 : ℝ) < s.re)
    (g : KPGlobalResidualConstruction.G F ζ hζ) :
    let chamber := fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
      (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
        (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c) * h)
    KPMsGreenFlux.casimir F ζ hζ chamber g =
      KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) s * chamber g := by
  let f := (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
  let a := fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
    KPLiteralRaw.rationalLift F ζ hζ (Quotient.out c)
  let chamber := fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F, f (a c*h)
  change KPMsGreenFlux.casimir F ζ hζ chamber g = _
  have hjet (w : NumberField.InfinitePlace F) (i j : Fin 6) :
      Summable (fun q : KPChamberBruhatTwoCells.RationalQuotient F =>
        KPMsGreenFlux.rightDerivative F ζ hζ w i
          (KPMsGreenFlux.rightDerivative F ζ hζ w j f) (a q*g)) ∧
      KPMsGreenFlux.rightDerivative F ζ hζ w i
        (KPMsGreenFlux.rightDerivative F ζ hζ w j chamber) g =
        ∑' q : KPChamberBruhatTwoCells.RationalQuotient F,
          KPMsGreenFlux.rightDerivative F ζ hζ w i
            (KPMsGreenFlux.rightDerivative F ζ hζ w j f) (a q*g) := by
    have hh := spherical_word_chamber F ζ hζ U v
      [nativeIndex F (w,i),nativeIndex F (w,j)] s hs g
    simpa only [native_second_word] using hh
  have hw (w : NumberField.InfinitePlace F) :
      -((1 : ℂ)/4) *
        (KPMsGreenFlux.rightDerivative F ζ hζ w 0
          (KPMsGreenFlux.rightDerivative F ζ hζ w 0 (chamber)) g -
         KPMsGreenFlux.rightDerivative F ζ hζ w 1
          (KPMsGreenFlux.rightDerivative F ζ hζ w 1 (chamber)) g +
         2 * (KPMsGreenFlux.rightDerivative F ζ hζ w 2
          (KPMsGreenFlux.rightDerivative F ζ hζ w 4 (chamber)) g +
          KPMsGreenFlux.rightDerivative F ζ hζ w 4
          (KPMsGreenFlux.rightDerivative F ζ hζ w 2 (chamber)) g -
          KPMsGreenFlux.rightDerivative F ζ hζ w 3
          (KPMsGreenFlux.rightDerivative F ζ hζ w 5 (chamber)) g -
          KPMsGreenFlux.rightDerivative F ζ hζ w 5
          (KPMsGreenFlux.rightDerivative F ζ hζ w 3 (chamber)) g)) =
      ∑' q : KPChamberBruhatTwoCells.RationalQuotient F,
        -((1 : ℂ)/4) *
          (KPMsGreenFlux.rightDerivative F ζ hζ w 0 (KPMsGreenFlux.rightDerivative F ζ hζ w 0 f) (a q*g) -
           KPMsGreenFlux.rightDerivative F ζ hζ w 1 (KPMsGreenFlux.rightDerivative F ζ hζ w 1 f) (a q*g) +
           2 * (KPMsGreenFlux.rightDerivative F ζ hζ w 2 (KPMsGreenFlux.rightDerivative F ζ hζ w 4 f) (a q*g) +
            KPMsGreenFlux.rightDerivative F ζ hζ w 4 (KPMsGreenFlux.rightDerivative F ζ hζ w 2 f) (a q*g) -
            KPMsGreenFlux.rightDerivative F ζ hζ w 3 (KPMsGreenFlux.rightDerivative F ζ hζ w 5 f) (a q*g) -
            KPMsGreenFlux.rightDerivative F ζ hζ w 5 (KPMsGreenFlux.rightDerivative F ζ hζ w 3 f) (a q*g))) := by
    simp_rw [(hjet w _ _).2]
    rw [tsum_mul_left]
    rw [((hjet w 0 0).1.sub (hjet w 1 1).1).tsum_add
      (((((hjet w 2 4).1.add (hjet w 4 2).1).sub (hjet w 3 5).1).sub (hjet w 5 3).1).mul_left 2)]
    rw [((hjet w 0 0).1).tsum_sub (hjet w 1 1).1,tsum_mul_left,
      (((hjet w 2 4).1.add (hjet w 4 2).1).sub (hjet w 3 5).1).tsum_sub (hjet w 5 3).1,
      ((hjet w 2 4).1.add (hjet w 4 2).1).tsum_sub (hjet w 3 5).1,
      (hjet w 2 4).1.tsum_add (hjet w 4 2).1]
  have hws (w : NumberField.InfinitePlace F) : Summable (fun q =>
      -((1 : ℂ)/4) *
        (KPMsGreenFlux.rightDerivative F ζ hζ w 0 (KPMsGreenFlux.rightDerivative F ζ hζ w 0 f) (a q*g) -
         KPMsGreenFlux.rightDerivative F ζ hζ w 1 (KPMsGreenFlux.rightDerivative F ζ hζ w 1 f) (a q*g) +
         2 * (KPMsGreenFlux.rightDerivative F ζ hζ w 2 (KPMsGreenFlux.rightDerivative F ζ hζ w 4 f) (a q*g) +
          KPMsGreenFlux.rightDerivative F ζ hζ w 4 (KPMsGreenFlux.rightDerivative F ζ hζ w 2 f) (a q*g) -
          KPMsGreenFlux.rightDerivative F ζ hζ w 3 (KPMsGreenFlux.rightDerivative F ζ hζ w 5 f) (a q*g) -
          KPMsGreenFlux.rightDerivative F ζ hζ w 5 (KPMsGreenFlux.rightDerivative F ζ hζ w 3 f) (a q*g)))) :=
    (((hjet w 0 0).1.sub (hjet w 1 1).1).add
      (((((hjet w 2 4).1.add (hjet w 4 2).1).sub (hjet w 3 5).1).sub (hjet w 5 3).1).mul_left 2)).mul_left _
  unfold KPMsGreenFlux.casimir
  simp_rw [hw]
  rw [← Summable.tsum_finsetSum (fun w _ => hws w)]
  change (∑' q, KPMsGreenFlux.casimir F ζ hζ f (a q*g)) = _
  dsimp only [f]
  simp_rw [native_flat_casimir F ζ hζ v.val s]
  rw [tsum_mul_left]
end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
