module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Lattices.DualBasisCoordinates
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

theorem periodisation_fourierCoefficient_eq_fourier
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : SchwartzMap V ℂ) (D : Set V) (hDmeas : MeasurableSet D)
    (hD : IsAddFundamentalDomain L D volume) (hDfinite : volume D < ⊤)
    (w : dualLattice L) :
    (∫ x in D, 𝐞 (-inner ℝ x (w : V)) •
      (∑' v : L, f (x + (v : V)))) =
      𝓕 (f : V → ℂ) (w : V) := by
  classical
  letI : VAddInvariantMeasure L V (volume : Measure V) := ⟨fun v s hs => by
    change volume ((fun x : V => (v : V) + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (v : V) s⟩
  have hc : Countable L := inferInstance
  let F : L → V → ℂ := fun v x => 𝐞 (-inner ℝ x (w : V)) • f (x + (v : V))
  have hmeas (v : L) : AEStronglyMeasurable (F v) (volume.restrict D) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hnorm : (∑' v : L, ∫⁻ x in D, ‖F v x‖ₑ) ≠ ⊤ := by
    simp only [F, Circle.enorm_smul]
    have hh := hD.lintegral_eq_tsum'' (fun x : V => ‖f x‖ₑ)
    simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using hh.symm.trans_ne f.integrable.2.ne
  have hchar (v : L) (x : V) :
      𝐞 (-inner ℝ (x + (v : V)) (w : V)) = 𝐞 (-inner ℝ x (w : V)) := by
    have hv := (LinearMap.BilinForm.mem_dualSubmodule (innerₗ V)).mp w.property (v : V) v.property
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp hv
    have hi : inner ℝ (v : V) (w : V) = (n : ℝ) := by
      change (n : ℝ) = inner ℝ (w : V) (v : V) at hn
      rw [real_inner_comm]
      exact hn.symm
    rw [inner_add_left, hi, neg_add, AddChar.map_add_eq_mul]
    have he : 𝐞 (-(n : ℝ)) = 1 := by
      rw [Real.fourierChar_apply']
      rw [show 2 * Real.pi * -(n : ℝ) = (-n : ℤ) * (2 * Real.pi) by push_cast; ring]
      simp
    rw [he, mul_one]
  rw [Real.fourier_eq]
  calc
    _ = ∫ x in D, ∑' v : L, F v x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (tsum_const_smul' (𝐞 (-inner ℝ x (w : V)))).symm
    _ = ∑' v : L, ∫ x in D, F v x := integral_tsum hmeas hnorm
    _ = ∫ x : V, 𝐞 (-inner ℝ x (w : V)) • f x := by
      rw [hD.integral_eq_tsum'' _ ((Real.fourierIntegral_convergent_iff (w : V)).mpr f.integrable)]
      apply tsum_congr
      intro v
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Submodule.vadd_def, vadd_eq_add, add_comm (v : V) x, hchar, F]

end DedekindZetaZeroFree.PoissonArch

end
