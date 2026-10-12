module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open MeasureTheory

def logConvolutionMeasure : Measure ℝ :=
  (volume.withDensity (fun T : ℝ => ENNReal.ofReal T⁻¹)).restrict (Set.Ioi 0)

def logProfile (H : ℝ → ℂ) : ℝ → ℂ := fun u => H (Real.exp u)

def logConvolution (K H : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ T, K T * H (x / T) ∂logConvolutionMeasure

def logConvolutionMoment (K : ℝ → ℂ) (σ : ℝ) : ℝ :=
  ∫ T, ‖K T‖ * T ^ σ ∂logConvolutionMeasure

theorem logConvolution_c2 {I : Type*} [Fintype I]
    (H : I → ℝ → ℂ) (K : ℝ → ℂ) (C : ℝ → ℕ → ℝ)
    (hH : ∀ i, ContDiff ℝ 2 (logProfile (H i)))
    (hC : ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 → 0 ≤ C σ j)
    (henvelope : ∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ j : ℕ, j ≤ 2 →
      ∀ i u, ‖iteratedDeriv j (logProfile (H i)) u‖ ≤
        C σ j * Real.exp (-σ * u))
    (hK : Measurable (fun T : Set.Ioi (0 : ℝ) => K T))
    (hmoments : ∀ σ : ℝ,
      Integrable (fun T : ℝ => ‖K T‖ * T ^ σ) logConvolutionMeasure) :
    (∀ i x, 0 < x →
      Integrable (fun T => K T * H i (x / T)) logConvolutionMeasure) ∧
    (∀ i, ContDiff ℝ 2 (logProfile (logConvolution K (H i)))) ∧
    (∀ i (j : ℕ), j ≤ 2 → ∀ u : ℝ,
      Integrable (fun T => K T * iteratedDeriv j (logProfile (H i))
        (u - Real.log T)) logConvolutionMeasure ∧
      iteratedDeriv j (logProfile (logConvolution K (H i))) u =
        ∫ T, K T * iteratedDeriv j (logProfile (H i))
          (u - Real.log T) ∂logConvolutionMeasure) ∧
    (∀ σ : ℝ, -(1 / 4 : ℝ) < σ → ∀ i (j : ℕ), j ≤ 2 → ∀ u : ℝ,
      ‖iteratedDeriv j (logProfile (logConvolution K (H i))) u‖ ≤
        C σ j * logConvolutionMoment K σ * Real.exp (-σ * u)) := by
  classical
  have hpos : ∀ᵐ T ∂logConvolutionMeasure, 0 < T :=
    ae_restrict_mem measurableSet_Ioi
  have hKmeas : AEStronglyMeasurable K logConvolutionMeasure :=
    (aemeasurable_restrict_of_measurable_subtype measurableSet_Ioi hK).aestronglyMeasurable
  have hzero : -(1 / 4 : ℝ) < 0 := by norm_num
  have hKint : Integrable (fun T => ‖K T‖) logConvolutionMeasure := by
    simpa using hmoments 0
  let F : I → ℕ → ℝ → ℝ → ℂ := fun i j u T =>
    K T * iteratedDeriv j (logProfile (H i)) (u - Real.log T)
  let A : I → ℕ → ℝ → ℂ := fun i j u => ∫ T, F i j u T ∂logConvolutionMeasure
  have hc : ∀ i j, j ≤ 2 → Continuous (iteratedDeriv j (logProfile (H i))) := by
    intro i j hj
    exact (hH i).continuous_iteratedDeriv j (by exact_mod_cast hj)
  have hm : ∀ i j, j ≤ 2 → ∀ u, AEStronglyMeasurable (F i j u) logConvolutionMeasure := by
    intro i j hj u
    exact hKmeas.mul (((hc i j hj).measurable.comp
      (measurable_const.sub Real.measurable_log)).aestronglyMeasurable)
  have hb : ∀ i j, j ≤ 2 → ∀ u T, ‖F i j u T‖ ≤ C 0 j * ‖K T‖ := by
    intro i j hj u T
    dsimp [F]
    rw [norm_mul, mul_comm (C 0 j)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa using henvelope 0 hzero j hj i (u - Real.log T)
  have hi : ∀ i j, j ≤ 2 → ∀ u, Integrable (F i j u) logConvolutionMeasure := by
    intro i j hj u
    exact (hKint.const_mul (C 0 j)).mono' (hm i j hj u)
      (Filter.Eventually.of_forall (hb i j hj u))
  have haCont : ∀ i j, j ≤ 2 → Continuous (A i j) := by
    intro i j hj
    apply continuous_of_dominated (hm i j hj)
      (fun u => Filter.Eventually.of_forall (hb i j hj u)) (hKint.const_mul (C 0 j))
    apply Filter.Eventually.of_forall
    intro T
    exact continuous_const.mul ((hc i j hj).comp (continuous_id.sub continuous_const))
  have haDeriv : ∀ i j, j < 2 → ∀ u, HasDerivAt (A i j) (A i (j + 1) u) u := by
    intro i j hj u
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Set.univ) (bound := fun T => C 0 (j + 1) * ‖K T‖)
      (F' := F i (j + 1)) (by simp)
      (Filter.Eventually.of_forall (hm i j (by omega))) (hi i j (by omega) u)
      (hm i (j + 1) (by omega) u) ?_ (hKint.const_mul (C 0 (j + 1))) ?_).2
    · exact Filter.Eventually.of_forall (fun T v _ => hb i (j + 1) (by omega) v T)
    · apply Filter.Eventually.of_forall
      intro T v _
      have hd := ((hH i).differentiable_iteratedDeriv j
        (by exact_mod_cast hj) (v - Real.log T)).hasDerivAt
      have hs := hd.scomp v ((hasDerivAt_id v).sub_const (Real.log T))
      simpa [F, Function.comp_def, iteratedDeriv_succ] using hs.const_mul (K T)
  have hbase : ∀ i, logProfile (logConvolution K (H i)) = A i 0 := by
    intro i
    funext u
    apply integral_congr_ae
    filter_upwards [hpos] with T hT
    simp [logProfile, logConvolution, A, F, Real.exp_sub, Real.exp_log hT]
  have heq : ∀ i j, j ≤ 2 → iteratedDeriv j (logProfile (logConvolution K (H i))) = A i j := by
    intro i j hj
    induction j with
    | zero => simpa using hbase i
    | succ j ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      funext u
      exact (haDeriv i j (by omega) u).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i x hx
    have he : (fun T => K T * H i (x / T)) =ᵐ[logConvolutionMeasure] F i 0 (Real.log x) := by
      filter_upwards [hpos] with T hT
      simp [F, logProfile, Real.exp_sub, Real.exp_log hT, Real.exp_log hx]
    exact (hi i 0 (by omega) (Real.log x)).congr he.symm
  · intro i
    apply (contDiff_nat_iff_iteratedDeriv (n := 2)).mpr
    constructor
    · intro j hj
      rw [heq i j hj]
      exact haCont i j hj
    · intro j hj
      rw [heq i j (by omega)]
      exact fun u => (haDeriv i j hj u).differentiableAt
  · intro i j hj u
    exact ⟨hi i j hj u, congrFun (heq i j hj) u⟩
  · intro σ hσ i j hj u
    rw [heq i j hj]
    have hweight : ∀ᵐ T ∂logConvolutionMeasure,
        ‖F i j u T‖ ≤ (C σ j * Real.exp (-σ * u)) * (‖K T‖ * T ^ σ) := by
      filter_upwards [hpos] with T hT
      have hh := mul_le_mul_of_nonneg_left
        (henvelope σ hσ j hj i (u - Real.log T)) (norm_nonneg (K T))
      have hex : Real.exp (-σ * (u - Real.log T)) =
          Real.exp (-σ * u) * T ^ σ := by
        rw [Real.rpow_def_of_pos hT, ← Real.exp_add]
        congr 1
        ring
      simpa only [F, norm_mul, hex, mul_assoc, mul_comm, mul_left_comm] using hh
    have hh := norm_integral_le_of_norm_le
      ((hmoments σ).const_mul (C σ j * Real.exp (-σ * u))) hweight
    rw [integral_const_mul] at hh
    change ‖A i j u‖ ≤ _ at hh
    change ‖A i j u‖ ≤ C σ j * (∫ T, ‖K T‖ * T ^ σ ∂logConvolutionMeasure) * Real.exp (-σ * u)
    convert hh using 1 <;> ring

end
end DedekindZetaZeroFree
