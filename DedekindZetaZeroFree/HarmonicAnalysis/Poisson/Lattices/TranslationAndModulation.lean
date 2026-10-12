module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.Lattices.ShiftedSummation

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

theorem temperateGrowth_fourierChar_inner
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (b : V) :
    (fun x : V => (𝐞 (inner ℝ x b) : ℂ)).HasTemperateGrowth := by
  have h1 : (fun y : ℝ => Complex.exp (y * Complex.I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I
  have h2 : (fun x : V => (2 * Real.pi * inner ℝ x b : ℝ)).HasTemperateGrowth := by fun_prop
  have h3 := h1.comp h2
  convert h3 using 1
  ext x
  rw [Function.comp_apply, Real.fourierChar_apply]

theorem fourier_smul_fourierChar
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : 𝓢(V, ℂ)) (b : V) :
    ∀ w : V, 𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : V => (𝐞 (inner ℝ x b) : ℂ)) f :
        V → ℂ)) w = 𝓕 (f : V → ℂ) (w - b) := by
  have hb := temperateGrowth_fourierChar_inner (V := V) b
  intro w
  rw [Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with v
  have hgv : (SchwartzMap.smulLeftCLM ℂ (fun x : V => (𝐞 (inner ℝ x b) : ℂ)) f : V → ℂ) v
      = (𝐞 (inner ℝ v b) : ℂ) • (f : V → ℂ) v :=
    SchwartzMap.smulLeftCLM_apply_apply hb f v
  rw [hgv]
  rw [Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 1
  rw [inner_sub_right]
  ring_nf

theorem summable_norm_modulated_schwartz_translate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    Summable (fun v : L =>
      ‖𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))‖) := by
  simpa using summable_norm_schwartz_translate L f a

theorem summable_norm_shifted_fourier_schwartz_dual_lattice
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    Summable (fun w : dualLattice L =>
      ‖𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b)‖) := by
  have h := summable_norm_fourier_schwartz_translate L f (-b)
  simpa only [Circle.norm_smul, neg_add_eq_sub] using h

theorem poisson_shift_modulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    (∑' v : L, 𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))) =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : dualLattice L,
          𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b) := by
  have hb := temperateGrowth_fourierChar_inner (V := V) b
  set g := SchwartzMap.smulLeftCLM ℂ (fun x : V => (𝐞 (inner ℝ x b) : ℂ)) f with hg
  trans ∑' v : L, g (a + (v : V))
  · apply tsum_congr
    intro v
    exact (SchwartzMap.smulLeftCLM_apply_apply hb f (a + (v : V))).symm
  · rw [poisson_summation_lattice_shift L g a]
    congr 1
    apply tsum_congr
    intro w
    rw [fourier_smul_fourierChar f b (w : V)]

end DedekindZetaZeroFree.PoissonArch

end
