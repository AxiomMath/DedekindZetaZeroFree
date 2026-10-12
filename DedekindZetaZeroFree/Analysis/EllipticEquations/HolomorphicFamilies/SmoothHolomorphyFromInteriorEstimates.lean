module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.HolomorphicFamilies.SolutionJetContinuity
public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.HilbertCauchyCoefficientLifting

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

open MeasureTheory KPContLocalNorm

theorem common_disks_imply_smooth_holomorphic {n : ℕ} (B : LocalBall n)
    (O : Set ℂ) (hO : IsOpen O) (f : ℂ → Space n → ℂ)
    (hseries : ∀ z₀ : ℂ, ∀ ρ : ℝ, 0 < ρ → Metric.closedBall z₀ ρ ⊆ O →
      ∃ coeff : ℕ → Space n → ℂ, Raw.SmoothPowerSeriesOn B z₀ ρ coeff f) :
    Raw.SmoothCompactOpenHolomorphicOn B f O := by
  intro z₀ hz₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO z₀ hz₀
  have hhalf : 0 < ε / 2 := by positivity
  have hclosed : Metric.closedBall z₀ (ε / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  exact ⟨ε / 2, hhalf, Metric.ball_subset_closedBall.trans hclosed,
    hseries z₀ (ε / 2) hhalf hclosed⟩

theorem holomorphy_of_jet_continuity {n : ℕ} (B : LocalBall n)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (R : H →L[ℂ] BallL2 B)
    (O : Set ℂ) (hO : IsOpen O) (v : ℂ → H) (hv : DifferentiableOn ℂ v O)
    (f : ℂ → Space n → ℂ)
    (hf : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier ∧
      (f z =ᵐ[volume.restrict B.carrier] (fun x => R (v z) x)))
    (hjets : Raw.JetContinuousOn B f O) :
    Raw.SmoothCompactOpenHolomorphicOn B f O ∧
    (∀ z₀ : ℂ, ∀ ρ : ℝ, 0 < ρ → Metric.closedBall z₀ ρ ⊆ O →
      ∃ coeff : ℕ → Space n → ℂ,
        (∀ j : ℕ,
          (coeff j =ᵐ[volume.restrict B.carrier]
            (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x)) ∧
          (∀ g : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier →
            (g =ᵐ[volume.restrict B.carrier]
              (fun x => R ((cauchyPowerSeries v z₀ ρ j) (fun _ => (1 : ℂ))) x)) →
            Set.EqOn g (coeff j) B.carrier)) ∧
        Raw.SmoothPowerSeriesOn B z₀ ρ coeff f) := by
  have hseries := cauchy_coefficients_of_jet_continuity B R O v hv f hf hjets
  refine ⟨common_disks_imply_smooth_holomorphic B O hO f ?_, hseries⟩
  intro z₀ ρ hρ hclosed
  obtain ⟨coeff, _, hc⟩ := hseries z₀ ρ hρ hclosed
  exact ⟨coeff, hc⟩

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

end
