module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.Lattices.TranslateSummability

@[expose] public section

noncomputable section
open scoped SchwartzMap

namespace DedekindZetaZeroFree.PoissonArch

def periodisation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Submodule ℤ V) (f : 𝓢(V, ℂ)) (x : V) : ℂ :=
  ∑' v : L, f (x + (v : V))

theorem summable_norm_schwartz_translate_restrict
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (K : TopologicalSpace.Compacts V) :
    Summable (fun v : L =>
      ‖(f.toContinuousMap.comp (ContinuousMap.addRight (v : V))).restrict K‖) := by
  classical
  let n := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hdecay⟩ := f.decay n 0
  have hdecay' (y : V) : ‖y‖ ^ n * ‖f y‖ ≤ C := by
    simpa only [iteratedFDeriv_zero_apply, norm_iteratedFDeriv_zero] using hdecay y
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  have hclosed : IsClosed (L : Set V) := L.toAddSubgroup.isClosed_of_discreteTopology
  have hdiscrete : IsDiscrete (L : Set V) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  have hincl : Filter.Tendsto (fun v : L => (v : V)) Filter.cofinite
      (Filter.cocompact V) := hclosed.tendsto_coe_cofinite_of_isDiscrete hdiscrete
  have htail : ∀ᶠ v : L in Filter.cofinite, max (2 * R) 1 ≤ ‖(v : V)‖ :=
    (tendsto_norm_cocompact_atTop.comp hincl).eventually
      (Filter.eventually_ge_atTop _)
  have hg : Summable (fun v : L => (C * 2 ^ n) * ‖(v : V)‖⁻¹ ^ n) := by
    simpa only [Submodule.norm_coe] using
      (ZLattice.summable_norm_pow_inv L n (by dsimp [n]; omega)).mul_left (C * 2 ^ n)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [htail] with v hv
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖f ((x : V) + (v : V))‖ ≤ C * 2 ^ n * ‖(v : V)‖⁻¹ ^ n
  have hvpos : 0 < ‖(v : V)‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_right _ _).trans hv)
  have htriangle : ‖(v : V)‖ ≤ 2 * ‖(x : V) + (v : V)‖ := by
    have ht := norm_add_le ((x : V) + (v : V)) (-(x : V))
    have hx := hR (x : V) x.property
    have hr := (le_max_left _ _).trans hv
    have hid : (x : V) + (v : V) + -(x : V) = (v : V) := by abel
    rw [hid, norm_neg] at ht
    linarith
  have hp : ‖(v : V)‖ ^ n * ‖f ((x : V) + (v : V))‖ ≤ C * 2 ^ n := by
    calc
      _ ≤ (2 * ‖(x : V) + (v : V)‖) ^ n * ‖f ((x : V) + (v : V))‖ := by
        gcongr
      _ = 2 ^ n * (‖(x : V) + (v : V)‖ ^ n * ‖f ((x : V) + (v : V))‖) := by
        rw [mul_pow]; ring
      _ ≤ 2 ^ n * C := mul_le_mul_of_nonneg_left (hdecay' _) (by positivity)
      _ = C * 2 ^ n := mul_comm _ _
  have hh : ‖f ((x : V) + (v : V))‖ ≤ (C * 2 ^ n) / ‖(v : V)‖ ^ n :=
    (le_div_iff₀ (pow_pos hvpos n)).mpr (by simpa only [mul_comm] using hp)
  simpa only [div_eq_mul_inv, inv_pow] using hh

theorem continuous_periodisation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) : Continuous (periodisation L f) := by
  let F : L → C(V, ℂ) := fun v => f.toContinuousMap.comp (ContinuousMap.addRight (v : V))
  have hF : Summable F := ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_schwartz_translate_restrict L f)
  have heq : periodisation L f = ⇑(∑' v, F v) := by
    funext x
    rw [← ContinuousMap.tsum_apply hF]
    rfl
  rw [heq]
  exact (∑' v, F v).continuous

theorem periodisation_add_lattice
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (x : V) (v : L) :
    periodisation L f (x + (v : V)) = periodisation L f x := by
  unfold periodisation
  have he := (Equiv.addLeft v).tsum_eq (fun w : L => f (x + (w : V)))
  simpa only [Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using he

end DedekindZetaZeroFree.PoissonArch

end
