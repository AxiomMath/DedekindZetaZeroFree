module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SchwartzPeriodizationCoefficients

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project

The Fourier-series evaluation below adapts the proof of
`latticeGaussian_poissonSummation_of_basis` from
https://github.com/LeanPool/lean-pool, commit
68aa6ee63d20ad76bcc15f595adfc72949991f06,
LeanPool/Odlyzko/Theta/PoissonSummation.lean.
The upstream Apache-2.0 license is included in
DedekindZetaZeroFree/LICENSE.
-/

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem schwartzLatticePoisson (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap E ℂ) :
    Summable (fun ℓ : L => ‖f (ℓ : E)‖) ∧
      Summable (fun ξ : dualLattice L =>
        ‖(FourierTransform.fourier f) (ξ : E)‖) ∧
      HasSum (fun ℓ : L => f (ℓ : E))
        ((ZLattice.covolume L : ℂ)⁻¹ *
          ∑' ξ : dualLattice L, (FourierTransform.fourier f) (ξ : E)) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  letI := Fintype.ofFinite ι
  letI : IsZLattice ℝ (dualLattice L) := by
    constructor
    rw [← span_range_dualRealBasis L b]
    exact ZSpan.span_top (dualRealBasis L b)
  have habs : Summable (fun ℓ : L => ‖f (ℓ : E)‖) := by
    simpa only [zero_add] using schwartzLatticeDecay_pointwise L f 0
  have hdualabs : Summable (fun ξ : dualLattice L =>
      ‖(FourierTransform.fourier f) (ξ : E)‖) := by
    simpa only [zero_add] using
      schwartzLatticeDecay_pointwise (dualLattice L) (FourierTransform.fourier f) 0
  refine ⟨habs, hdualabs, ?_⟩
  have hdual : Summable (fun n : ι → ℤ =>
      (FourierTransform.fourier f) (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr hdualabs.of_norm
    exact hs
  have hcoeff : Summable
      (UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization L b f)) := by
    change Summable (fun n : ι → ℤ =>
      UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization L b f) n)
    simp_rw [mFourierCoeff_schwartzTorusPeriodization]
    exact hdual.mul_left _
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    hcoeff (0 : UnitAddTorus ι)
  have hsum : (∑' n : ι → ℤ,
      UnitAddTorus.mFourierCoeff (schwartzTorusPeriodization L b f) n) =
      schwartzTorusPeriodization L b f 0 := by
    rw [← hseries.tsum_eq]
    apply tsum_congr
    intro n
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one,
      smul_eq_mul, mul_one]
  have hzero : schwartzTorusPeriodization L b f 0 = ∑' ℓ : L, f (ℓ : E) := by
    rw [show (0 : UnitAddTorus ι) = torusQuotientMap (0 : ι → ℝ) by rfl,
      schwartzTorusPeriodization_apply_quotient]
    simp_rw [zero_add, ofZLatticeBasis_equivFun_symm_intCast]
    exact b.equivFun.toEquiv.symm.tsum_eq (fun ℓ : L => f (ℓ : E))
  have heq : (∑' ℓ : L, f (ℓ : E)) =
      (ZLattice.covolume L : ℂ)⁻¹ *
        ∑' ξ : dualLattice L, (FourierTransform.fourier f) (ξ : E) := by
    rw [← hzero, ← hsum]
    simp_rw [mFourierCoeff_schwartzTorusPeriodization]
    rw [tsum_mul_left]
    congr 1
    exact (dualLatticeBasis L b).equivFun.toEquiv.symm.tsum_eq
      (fun ξ : dualLattice L => (FourierTransform.fourier f) (ξ : E))
  rw [← heq]
  exact habs.of_norm.hasSum

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
