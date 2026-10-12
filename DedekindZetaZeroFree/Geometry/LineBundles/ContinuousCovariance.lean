module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction
open MeasureTheory KPContLocalNorm

theorem continuous_covariance_of_ae {n : ℕ} (A : LocalBall n)
    (τ : Space n → Space n) (hτ : Continuous τ)
    (hτμ : Measure.QuasiMeasurePreserving τ volume volume)
    (q f : Space n → ℂ) (hf : ContinuousOn f A.carrier)
    (hrep : f =ᵐ[volume.restrict A.carrier] q) (χ : ℂ)
    (hcov : ∀ᵐ p ∂volume.restrict (A.carrier ∩ τ ⁻¹' A.carrier),
      q (τ p) = χ * q p) :
    ∀ p ∈ A.carrier ∩ τ ⁻¹' A.carrier, f (τ p) = χ * f p := by
  have hball : IsOpen A.carrier := Metric.isOpen_ball
  have hU : IsOpen (A.carrier ∩ τ ⁻¹' A.carrier) := hball.inter (hball.preimage hτ)
  have hmaps : Set.MapsTo τ (A.carrier ∩ τ ⁻¹' A.carrier) A.carrier := fun _ hx => hx.2

  have h1 : f =ᵐ[volume.restrict (A.carrier ∩ τ ⁻¹' A.carrier)] q :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hrep
  have hqmp : Measure.QuasiMeasurePreserving τ
      (volume.restrict (A.carrier ∩ τ ⁻¹' A.carrier)) (volume.restrict A.carrier) :=
    hτμ.restrict hmaps
  have h3 : f ∘ τ =ᵐ[volume.restrict (A.carrier ∩ τ ⁻¹' A.carrier)] q ∘ τ :=
    hqmp.ae_eq_comp hrep
  have h4 : (fun p => f (τ p)) =ᵐ[volume.restrict (A.carrier ∩ τ ⁻¹' A.carrier)]
      (fun p => χ * f p) :=
    (h3.trans hcov).trans h1.mul_left.symm

  have hcont1 : ContinuousOn (fun p => f (τ p)) (A.carrier ∩ τ ⁻¹' A.carrier) :=
    hf.comp hτ.continuousOn hmaps
  have hcont2 : ContinuousOn (fun p => χ * f p) (A.carrier ∩ τ ⁻¹' A.carrier) :=
    continuousOn_const.mul (hf.mono Set.inter_subset_left)
  exact fun p hp => Measure.eqOn_open_of_ae_eq h4 hU hcont1 hcont2 hp

end DedekindZetaZeroFree.KPContActualLocalSolutionFamily.CoefficientRestriction

end
