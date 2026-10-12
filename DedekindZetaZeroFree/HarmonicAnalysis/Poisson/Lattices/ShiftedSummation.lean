module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Torus.PeriodisationCoefficients

@[expose] public section

set_option maxHeartbeats 800000

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory
open Module

namespace DedekindZetaZeroFree.PoissonArch

theorem poisson_summation_lattice_shift
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a : V) :
    (∑' v : L, f (a + (v : V))) =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : dualLattice L,
          𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) (w : V) := by
  classical
  let ι := Fin (Module.finrank ℤ L)
  let b : Basis ι ℤ L := Module.finBasis ℤ L
  let e : (ι → ℤ) ≃ dualLattice L := (dualVector_b L b : (ι → ℤ) ≃+ dualLattice L)
  set x : ι → UnitAddCircle := fun i => (((b.ofZLatticeBasis ℝ L).repr a) i : UnitAddCircle) with hx
  have hconjgen : ∀ z : ℝ, (starRingEnd ℂ) (((𝐞 z : Circle)) : ℂ) = (((𝐞 (-z) : Circle)) : ℂ) := by
    intro z
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  have hchar : ∀ n : ι → ℤ, UnitAddTorus.mFourier n x =
      ((𝐞 (inner ℝ a (((dualVector_b L b n : dualLattice L) : V))) : Circle) : ℂ) := by
    intro n
    have h2 : UnitAddTorus.mFourier (-n) x =
        ((𝐞 (-inner ℝ a (((dualVector_b L b n : dualLattice L) : V))) : Circle) : ℂ) := by
      rw [hx]; exact (dualVector_b_fourierChar L b a n).symm
    have h3 : (starRingEnd ℂ) (UnitAddTorus.mFourier n x) =
        ((𝐞 (-inner ℝ a (((dualVector_b L b n : dualLattice L) : V))) : Circle) : ℂ) := by
      rw [← UnitAddTorus.mFourier_neg]
      exact h2
    rw [show UnitAddTorus.mFourier n x
          = (starRingEnd ℂ) ((starRingEnd ℂ) (UnitAddTorus.mFourier n x)) from by simp, h3]
    simpa using hconjgen (-inner ℝ a (((dualVector_b L b n : dualLattice L) : V)))
  have hxval : (torusPeriodisation b f) x = ∑' v : L, f (a + (v : V)) := by
    rw [hx]
    rw [torusPeriodisation_coe b f ((b.ofZLatticeBasis ℝ L).repr a)]
    have hsymm : (b.ofZLatticeBasis ℝ L).equivFun.symm ((b.ofZLatticeBasis ℝ L).repr a) = a := by
      rw [← Basis.equivFun_apply]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hsymm]
    rfl
  have hnorm : Summable (fun w : dualLattice L => ‖(𝓕 (f : V → ℂ)) (w : V)‖) := by
    have h := summable_norm_fourier_schwartz_translate L f 0
    simpa using h
  have hcov : Summable (fun w : dualLattice L =>
      (ZLattice.covolume L volume : ℂ)⁻¹ * (𝓕 (f : V → ℂ)) (w : V)) :=
    (Summable.of_norm hnorm).mul_left _
  have hreindex_norm : Summable (fun n : ι → ℤ =>
      ‖(𝓕 (f : V → ℂ)) (((dualVector_b L b n : dualLattice L) : V))‖) := by
    refine (Function.Injective.summable_iff (dualVector_b L b).injective ?_).mpr hnorm
    intro x hx
    exact absurd (Set.mem_range.mpr ((dualVector_b L b).surjective x)) hx
  have hreindex_c : Summable (fun n : ι → ℤ =>
      (𝓕 (f : V → ℂ)) (((dualVector_b L b n : dualLattice L) : V))) :=
    Summable.of_norm hreindex_norm
  have hreindex : Summable (fun n : ι → ℤ =>
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        (𝓕 (f : V → ℂ)) (((dualVector_b L b n : dualLattice L) : V))) :=
    hreindex_c.mul_left _
  have hsumm : Summable (UnitAddTorus.mFourierCoeff (torusPeriodisation b f : UnitAddTorus ι → ℂ)) :=
    hreindex.congr (fun n => (torusPeriodisation_mFourierCoeff L b f n).symm)
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumm x
  have hterm : ∀ n : ι → ℤ,
      UnitAddTorus.mFourierCoeff (torusPeriodisation b f : UnitAddTorus ι → ℂ) n •
          UnitAddTorus.mFourier n x
      = (ZLattice.covolume L volume : ℂ)⁻¹ *
        (𝐞 (inner ℝ a (((dualVector_b L b n : dualLattice L) : V))) •
          (𝓕 (f : V → ℂ)) (((dualVector_b L b n : dualLattice L) : V))) := by
    intro n
    rw [torusPeriodisation_mFourierCoeff L b f n, hchar n, smul_eq_mul, Circle.smul_def]
    ring
  rw [← hxval, ← hs.tsum_eq]
  rw [tsum_congr hterm]
  rw [tsum_mul_left]
  congr 1
  exact Equiv.tsum_eq e
    (fun w : dualLattice L => 𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) (w : V))

end DedekindZetaZeroFree.PoissonArch

end
