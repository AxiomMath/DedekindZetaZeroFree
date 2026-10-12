module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Lattices.DualBasisCoordinates
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Algebra.Module.ZLattice.Summable

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open Filter

namespace DedekindZetaZeroFree.PoissonArch

theorem summable_norm_schwartz_translate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a : V) :
    Summable (fun v : L => ‖f (a + (v : V))‖) := by
  classical
  set s : ℝ := -(Module.finrank ℤ L : ℝ) - 1 with hs_def
  have hs : s < -Module.finrank ℤ L := by
    rw [hs_def]; linarith
  have hclosed : IsClosed (L : Set V) := L.toAddSubgroup.isClosed_of_discreteTopology
  have hdiscrete : IsDiscrete (L : Set V) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  have hincl : Tendsto (fun v : L => (v : V)) cofinite (cocompact V) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete hdiscrete
  have htrans : Tendsto (fun v : L => a + (v : V)) cofinite (cocompact V) := by
    have hE : Tendsto (Homeomorph.addLeft a) (cocompact V) (cocompact V) :=
      (Homeomorph.addLeft a).map_cocompact.le
    have h := hE.comp hincl
    simpa [Function.comp_def, Homeomorph.coe_addLeft] using h
  have hbigO : (fun v : L => f (a + (v : V))) =O[cofinite]
      (fun v : L => ‖a + (v : V)‖ ^ s) :=
    (f.isBigO_cocompact_rpow s).comp_tendsto htrans
  obtain ⟨c, hc⟩ := hbigO.isBigOWith
  have hg : Summable (fun v : L => max c 0 * ‖(v : V) - (-a)‖ ^ s) :=
    (ZLattice.summable_norm_sub_rpow L s hs (-a)).mul_left (max c 0)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [hc.bound] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (f (a + (v : V))))]
  have h1 : ‖f (a + (v : V))‖ ≤ c * ‖a + (v : V)‖ ^ s := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (a + (v : V))) s)] using hv
  have h2 : (0 : ℝ) ≤ ‖a + (v : V)‖ ^ s := Real.rpow_nonneg (norm_nonneg _) s
  calc ‖f (a + (v : V))‖ ≤ c * ‖a + (v : V)‖ ^ s := h1
    _ ≤ max c 0 * ‖a + (v : V)‖ ^ s :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) h2
    _ = max c 0 * ‖(v : V) - (-a)‖ ^ s := by
        have : a + (v : V) = (v : V) - (-a) := by rw [sub_neg_eq_add, add_comm]
        rw [this]

theorem summable_norm_fourier_schwartz_translate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (b : V) :
    Summable (fun w : dualLattice L => ‖(𝓕 (f : V → ℂ)) (b + (w : V))‖) := by
  have h := summable_norm_schwartz_translate (dualLattice L) (𝓕 f) b
  simpa only [SchwartzMap.fourier_coe] using h

end DedekindZetaZeroFree.PoissonArch

end
