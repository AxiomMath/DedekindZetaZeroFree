module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.ParityAffineCovariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SchwartzLattice

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.ShiftedPoisson

variable (K : Type) [Field K] [NumberField K]

private lemma norm_εδ (δ : Finset (RayCoset.RealPlaces K)) : ‖εδ K δ‖ = 1 := by
  rw [εδ, norm_pow, norm_neg, Complex.norm_I, one_pow]

private lemma norm_phase (a : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (a : ℂ) =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma norm_inv_J (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    ‖(J K q : ℂ)⁻¹‖ = |J K q|⁻¹ := by
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv]

private lemma norm_fourier (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v)
    (z ξ : euclidean.mixedSpace K) :
    ‖(FourierTransform.fourier (AffineFourier.shiftedSchwartz K δ q hq z)) ξ‖ =
      |J K q|⁻¹ * ‖gδ K δ (Q K (fun v ↦ (q v)⁻¹) ξ)‖ := by
  rw [AffineFourier.fourier_shiftedSchwartz, norm_mul, norm_mul, norm_mul,
    norm_inv_J K q hq, norm_εδ, norm_phase]
  ring

theorem poisson (L : Submodule ℤ (euclidean.mixedSpace K))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (δ : Finset (RayCoset.RealPlaces K))
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v)
    (z : euclidean.mixedSpace K) :
    Summable (fun ℓ : L => ‖gδ K δ (Q K q (z + (ℓ : euclidean.mixedSpace K)))‖) ∧
      Summable (fun ξ : Theta.dualLattice L =>
        ‖Complex.exp (2 * Real.pi * Complex.I *
            (inner ℝ (ξ : euclidean.mixedSpace K) z : ℂ)) *
          gδ K δ (Q K (fun v ↦ (q v)⁻¹) (ξ : euclidean.mixedSpace K))‖) ∧
      HasSum (fun ℓ : L => gδ K δ (Q K q (z + (ℓ : euclidean.mixedSpace K))))
        (((ZLattice.covolume L * J K q : ℝ) : ℂ)⁻¹ * εδ K δ *
          ∑' ξ : Theta.dualLattice L,
            Complex.exp (2 * Real.pi * Complex.I *
                (inner ℝ (ξ : euclidean.mixedSpace K) z : ℂ)) *
              gδ K δ (Q K (fun v ↦ (q v)⁻¹) (ξ : euclidean.mixedSpace K))) := by
  obtain ⟨hprimal, hdual, hHas⟩ :=
    Theta.schwartzLatticePoisson L (AffineFourier.shiftedSchwartz K δ q hq z)
  refine ⟨?_, ?_, ?_⟩
  · refine hprimal.congr (fun ℓ => ?_)
    rw [AffineFourier.shiftedSchwartz_apply]
  · have hA : Summable (fun ξ : Theta.dualLattice L =>
        |J K q|⁻¹ * ‖gδ K δ (Q K (fun v ↦ (q v)⁻¹)
          (ξ : euclidean.mixedSpace K))‖) :=
      hdual.congr (fun ξ => norm_fourier K δ q hq z (ξ : euclidean.mixedSpace K))
    have hbase : Summable (fun ξ : Theta.dualLattice L =>
        ‖gδ K δ (Q K (fun v ↦ (q v)⁻¹) (ξ : euclidean.mixedSpace K))‖) := by
      have h2 := hA.mul_left (|J K q|)
      refine h2.congr (fun ξ => ?_)
      rw [← mul_assoc, mul_inv_cancel₀
        (ne_of_gt (abs_pos.mpr (ne_of_gt (AffineFourier.J_pos K q hq)))), one_mul]
    refine hbase.congr (fun ξ => ?_)
    rw [norm_mul, norm_phase, one_mul]
  · set S : ℂ := ∑' ξ : Theta.dualLattice L,
        Complex.exp (2 * Real.pi * Complex.I *
            (inner ℝ (ξ : euclidean.mixedSpace K) z : ℂ)) *
          gδ K δ (Q K (fun v ↦ (q v)⁻¹) (ξ : euclidean.mixedSpace K)) with hS
    have htsum : ∑' ξ : Theta.dualLattice L,
        (FourierTransform.fourier (AffineFourier.shiftedSchwartz K δ q hq z))
          (ξ : euclidean.mixedSpace K) = (J K q : ℂ)⁻¹ * εδ K δ * S := by
      rw [hS]
      rw [tsum_congr (fun ξ : Theta.dualLattice L =>
        AffineFourier.fourier_shiftedSchwartz K δ q hq z (ξ : euclidean.mixedSpace K))]
      rw [tsum_congr (fun ξ : Theta.dualLattice L =>
        mul_assoc ((J K q : ℂ)⁻¹ * εδ K δ)
          (Complex.exp (2 * Real.pi * Complex.I *
            (inner ℝ (ξ : euclidean.mixedSpace K) z : ℂ)))
          (gδ K δ (Q K (fun v ↦ (q v)⁻¹) (ξ : euclidean.mixedSpace K))))]
      rw [tsum_mul_left]
    rw [htsum] at hHas
    have hHas' : HasSum (fun ℓ : L =>
        gδ K δ (Q K q (z + (ℓ : euclidean.mixedSpace K))))
        ((ZLattice.covolume L : ℂ)⁻¹ * ((J K q : ℂ)⁻¹ * εδ K δ * S)) := by
      simpa only [AffineFourier.shiftedSchwartz_apply] using hHas
    have hval : (ZLattice.covolume L : ℂ)⁻¹ * ((J K q : ℂ)⁻¹ * εδ K δ * S) =
        ((ZLattice.covolume L * J K q : ℝ) : ℂ)⁻¹ * εδ K δ * S := by
      rw [Complex.ofReal_mul, mul_inv_rev]
      ring
    rw [hval] at hHas'
    exact hHas'

end DedekindZetaZeroFree.AbelianQuotient.RayParity.ShiftedPoisson

end
