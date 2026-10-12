module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.Lattices.TranslationAndModulation

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

theorem summable_norm_poisson_lattice_shift_modulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    Summable (fun v : L =>
      ‖𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))‖) ∧
    Summable (fun w : dualLattice L =>
      ‖𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b)‖) := by
  exact ⟨summable_norm_modulated_schwartz_translate L f a b,
    summable_norm_shifted_fourier_schwartz_dual_lattice L f a b⟩

theorem poisson_summation_lattice_shift_modulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    (∑' v : L, 𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))) =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : dualLattice L,
          𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b) := by
  exact poisson_shift_modulation L f a b

end DedekindZetaZeroFree.PoissonArch

end
