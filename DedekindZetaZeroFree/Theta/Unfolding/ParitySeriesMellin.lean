module

public import DedekindZetaZeroFree.Theta.Unfolding.ParityThetaMellinIntegral

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.SeriesMellin

variable {K : Type} [Field K] [NumberField K]

theorem completed_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    (RayTheta.Pδ D δ).Λ s = κδ K δ s * RayCoset.Zδ D δ s := by
  have h1 := (ThetaMellinIntegral.hasMellin D δ s hs).2
  have h2 := ((RayTheta.Pδ D δ).hasMellin (s := s)
    (by simpa [RayTheta.Pδ_k] using hs)).2
  rw [RayTheta.Pδ_f, RayTheta.Pδ_f₀] at h2
  rw [h1] at h2
  exact h2.symm

theorem uncompleted_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    hδ K δ s * (RayTheta.Pδ D δ).Λ s = RayCoset.Zδ D δ s := by
  rw [completed_eq D δ s hs, ← mul_assoc,
    mul_comm (hδ K δ s) (κδ K δ s),
    FourierMellin.mellinFactor_mul_reciprocalGamma K δ s hs, one_mul]

end DedekindZetaZeroFree.AbelianQuotient.RayParity.SeriesMellin

end
