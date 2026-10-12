module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactDerivatives.SecondDerivativeL2
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.EnergyEstimates.FirstDerivativeL2
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.DominatedFlowDifferentiation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open KPMsClearedTruncationL2
open ResidualCompactSecondL2
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity renaming compactTensor → compactTensor
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactSecondL2 renaming compactAction → compactAction
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev diagonalEnergyWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

def nativeDiagonalWeight (b : KPSmoothActualFlowData.B F) : ℝ :=
  if b.2.val < 2 then 1/4 else 1/2

theorem nativeDiagonalWeight_pos (b : KPSmoothActualFlowData.B F) :
    0 < nativeDiagonalWeight b := by unfold nativeDiagonalWeight; split_ifs <;> norm_num

theorem original_diagonal_identity (u : X F ζ hζ → ℂ) (x : X F ζ hζ) :
    (∑ b : KPSmoothActualFlowData.B F, (nativeDiagonalWeight b : ℂ) * diagonalEnergyWordDerivative [b,b] u x) =
      -(KPMsGreenFlux.casimir F ζ hζ
        (fun g => u (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) x.out +
        compactForcing u x) := by
  have hp (w : NumberField.InfinitePlace F) (i j : Fin 6) :
      KPMsGreenFlux.rightDerivative F ζ hζ w i
        (KPMsGreenFlux.rightDerivative F ζ hζ w j
          (fun a => u (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a))) x.out =
      diagonalEnergyWordDerivative [(w,i),(w,j)] u x := by
    change diagonalEnergyWordDerivative [(w,i),(w,j)] u (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out) = _
    rw [show KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out = x from Quotient.out_eq x]
  rw [Fintype.sum_prod_type, KPMsGreenFlux.casimir]
  simp_rw [hp]
  unfold compactForcing
  rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  simp [nativeDiagonalWeight, compactTensor, Fin.sum_univ_succ]
  ring

theorem eigen_first_derivative_memLp
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y : ℝ) (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    {U₀ : Level F ζ hζ} (f : smoothSpace F ζ hζ U₀)
    (eig : ℂ) (he : ∀ g, KPMsGreenFlux.casimir F ζ hζ
      (fun a => f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a)) g =
      eig * f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))
    (hf : MemLp f.val 2 R.quotientHaar)
    [FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : KPMsGreenFlux.K F => f.val ∘ compactAction k)))]
    (b : KPSmoothActualFlowData.B F) :
    MemLp (KPSmoothActualFlowData.flowDerivative F ζ hζ b f.val) 2 R.quotientHaar := by
  apply original_first_derivative_memLp A R P D Y hY f nativeDiagonalWeight nativeDiagonalWeight_pos hf
  have hc := smooth_compactForcing_memLp_of_finiteOrbit f hf
  have hm : MemLp (fun x => -(eig * f.val x + compactForcing f.val x)) 2 R.quotientHaar :=
    ((hf.const_mul eig).add hc).neg
  refine MemLp.ae_eq ?_ hm
  filter_upwards [] with x
  rw [original_diagonal_identity, he]
  rw [show KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x.out = x from Quotient.out_eq x]

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
