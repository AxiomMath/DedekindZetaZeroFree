module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.PositiveIntertwinerConvergence
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness
open scoped ContDiff

theorem compact_family_spatial_jets_bounded
    (G : ℂ × ℂ → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (n : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : ℂ) 1,
      ∀ w ∈ Metric.closedBall z 1,
        ‖iteratedFDeriv ℝ n (fun v : ℂ => G (x, v)) w‖ ≤ C := by
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      iteratedFDeriv ℝ n (fun v : ℂ => G (p.1, v)) p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    induction n generalizing p with
    | zero =>
      simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
        (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hG.contDiffAt
    | succ n ih =>
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => fderiv ℝ
          (iteratedFDeriv ℝ n (fun v : ℂ => G (p.1, v))) p.2) p := by
        exact ((ih (p.1,p.2)).comp (p,p.2)
          (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
          (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) 1).prod
    (isCompact_closedBall z 1)).exists_bound_of_continuousOn hj.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx w hw
  exact (hC (x,w) ⟨hx,hw⟩).trans (le_max_left _ _)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness
open scoped ContDiff

theorem weighted_inverse_translate_spatial_jets_bounded
    (u : ℂ → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (a : ℝ) (n : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Metric.closedBall (0 : ℂ) 1)ᶜ,
      ∀ w ∈ Metric.closedBall z 1,
        ‖iteratedFDeriv ℝ n (fun v : ℂ =>
          ((‖x‖ ^ a : ℝ) : ℂ) * u (v + x⁻¹)) w‖ ≤ C * ‖x‖ ^ a := by
  have hj : Continuous (iteratedFDeriv ℝ n u) :=
    hu.continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall z 2).exists_bound_of_continuousOn
    hj.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx w hw
  have hxnorm : 1 ≤ ‖x‖ := by
    exact le_of_lt (show 1 < ‖x‖ by simpa using hx)
  have hxinv : ‖x⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hxnorm
  have hw' : w + x⁻¹ ∈ Metric.closedBall z 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hwbound : ‖w - z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    calc
      ‖w + x⁻¹ - z‖ = ‖(w - z) + x⁻¹‖ := by congr 1; abel
      _ ≤ ‖w - z‖ + ‖x⁻¹‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hs : ContDiffAt ℝ n (fun v : ℂ => u (v + x⁻¹)) w :=
    (hu.comp (contDiff_id.add contDiff_const)).contDiffAt.of_le (by simp)
  have he := iteratedFDeriv_const_smul_apply' (a := (‖x‖ ^ a : ℝ)) hs
  simp only [Complex.real_smul] at he
  rw [he, norm_smul, iteratedFDeriv_comp_add_right]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) a)]
  exact (mul_le_mul_of_nonneg_left ((hC _ hw').trans (le_max_left C 0))
    (Real.rpow_nonneg (norm_nonneg x) a)).trans_eq (mul_comm _ _)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness
open MeasureTheory Filter
open scoped Topology

theorem local_majorant_of_finite_piece_and_integrable_tail
    {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedAddCommGroup F] (μ : Measure X) (K : Set X)
    (hK : MeasurableSet K) (hfinite : μ K < ⊤)
    (J : E → X → F) (b : X → ℝ) (hb : IntegrableOn b Kᶜ μ)
    (z : E) (C₀ C₁ : ℝ)
    (hcompact : ∀ x ∈ K, ∀ w ∈ Metric.closedBall z 1, ‖J w x‖ ≤ C₀)
    (htail : ∀ x ∈ Kᶜ, ∀ w ∈ Metric.closedBall z 1, ‖J w x‖ ≤ C₁ * b x) :
    ∃ (s : Set E) (B : X → ℝ), s ∈ nhds z ∧ Integrable B μ ∧
      ∀ᵐ x ∂μ, ∀ w ∈ s, ‖J w x‖ ≤ B x := by
  classical
  let B : X → ℝ := K.indicator (fun _ => C₀) + Kᶜ.indicator (fun x => C₁ * b x)
  have hi₀ : Integrable (K.indicator (fun _ : X => C₀)) μ := by
    exact (integrableOn_const (ne_of_lt hfinite)).integrable_indicator hK
  have hi₁ : Integrable (Kᶜ.indicator (fun x => C₁ * b x)) μ := by
    exact (integrable_indicator_iff hK.compl).mpr (hb.const_mul C₁)
  refine ⟨Metric.closedBall z 1, B, Metric.closedBall_mem_nhds z (by norm_num),
    hi₀.add hi₁, Filter.Eventually.of_forall ?_⟩
  intro x w hw
  by_cases hx : x ∈ K
  · simpa [B, Set.indicator_of_mem hx, Set.indicator_of_notMem (show x ∉ Kᶜ by simpa)] using
      hcompact x hx w hw
  · simpa [B, Set.indicator_of_notMem hx, Set.indicator_of_mem (show x ∈ Kᶜ by simpa)] using
      htail x hx w hw

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.OpenSmoothness

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open MeasureTheory Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false in

theorem integral_contDiff_of_locally_dominated_jets
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (F : E → X → ℂ)
    (hsmooth : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun u => F u x))
    (hmeas : ∀ n : ℕ, ∀ u : E,
      AEStronglyMeasurable (fun x => iteratedFDeriv ℝ n (fun v => F v x) u) μ)
    (hbound : ∀ n : ℕ, ∀ u : E, ∃ (s : Set E) (b : X → ℝ),
      s ∈ nhds u ∧ Integrable b μ ∧
        ∀ᵐ x ∂μ, ∀ v ∈ s, ‖iteratedFDeriv ℝ n (fun w => F w x) v‖ ≤ b x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => ∫ x, F u x ∂μ) ∧
      ∀ n : ℕ, ∀ u : E,
        iteratedFDeriv ℝ n (fun v => ∫ x, F v x ∂μ) u =
          ∫ x, iteratedFDeriv ℝ n (fun v => F v x) u ∂μ := by
  have hint (n : ℕ) (u : E) :
      Integrable (fun x => iteratedFDeriv ℝ n (fun v => F v x) u) μ := by
    obtain ⟨s, b, hs, hb, h⟩ := hbound n u
    exact hb.mono' (hmeas n u) (h.mono fun x hx => hx u (mem_of_mem_nhds hs))
  let A (n : ℕ) (u : E) := ∫ x, iteratedFDeriv ℝ n (fun v => F v x) u ∂μ
  have hd (n : ℕ) (u : E) : HasFDerivAt (A n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ) (A (n + 1) u)) u := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    obtain ⟨s, b, hs, hb, h⟩ := hbound (n + 1) u
    have hf'm : AEStronglyMeasurable (fun x =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun v => F v x)) u) μ := by
      exact L.continuous.comp_aestronglyMeasurable (hmeas (n + 1) u)
    have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F := fun v x => iteratedFDeriv ℝ n (fun w => F w x) v)
      (F' := fun v x => fderiv ℝ (iteratedFDeriv ℝ n (fun w => F w x)) v)
      hs (Eventually.of_forall (hmeas n)) (hint n u) hf'm
      (h.mono fun x hx v hv => by
        change ‖L (iteratedFDeriv ℝ (n + 1) (fun w => F w x) v)‖ ≤ b x
        rw [L.norm_map]
        exact hx v hv) hb
      (Eventually.of_forall fun x v _ =>
        ((hsmooth x).differentiable_iteratedFDeriv (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) v).hasFDerivAt)
    have heq : (∫ x, fderiv ℝ (iteratedFDeriv ℝ n (fun v => F v x)) u ∂μ) =
        L (A (n + 1) u) := by
      letI : TopologicalSpace (E [×(n + 1)]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E [×(n + 1)]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      let Lc : (E [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        { toLinearMap := L.toLinearEquiv.toLinearMap
          cont := by convert L.continuous using 1 }
      exact @ContinuousLinearMap.integral_comp_comm X (E [×(n + 1)]→L[ℝ] ℂ)
        (E →L[ℝ] E [×n]→L[ℝ] ℂ) _ μ ℝ _ _ _ _ _ _ _ _ _ Lc _ (hint (n + 1) u)
    rw [heq] at hh
    exact hh
  have heq (n : ℕ) : iteratedFDeriv ℝ n (fun u => ∫ x, F u x ∂μ) = A n := by
    induction n with
    | zero =>
      funext u
      simpa [A, iteratedFDeriv_zero_eq_comp, Function.comp_apply] using
        ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (μ := μ) (F u)).symm
    | succ n ih =>
      funext u
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd n u).fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ).symm_apply_apply _
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun n _ => ?_), fun n u => congrFun (heq n) u⟩
  rw [heq n]
  exact fun u => (hd n u).differentiableAt
end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped Matrix.Norms.Elementwise ContDiff
lemma positive_open_integrand_joint_contDiff (f : PrincipalSeries positiveParameter) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2))) := by
  have hf := ((principalSeries_mem_iff positiveParameter f).mp f.property).2
  let g : ℂ × ℂ → ComplexGL2 := fun p => weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      (g p : Matrix (Fin 2) (Fin 2) ℂ)) := by
    dsimp [g]
    unfold upperUnipotent
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ =>
      (weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, p.1; 0, 1] *
        ((weyl : Matrix (Fin 2) (Fin 2) ℂ) * !![1, p.2; 0, 1]))
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have h := hf.comp (s := Set.univ) hg.contDiffOn (fun p _ => Matrix.GeneralLinearGroup.det_ne_zero (g p))
  rw [contDiffOn_univ] at h
  convert h using 1
  funext p
  dsimp [matrixFunction]
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (g p))]
  apply congrArg (f : ComplexGL2 → ℂ)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl
end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Filter
open scoped ContDiff Topology
lemma positive_open_integrand_jets_contDiff (f : PrincipalSeries positiveParameter) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => iteratedFDeriv ℝ n
      (fun z => f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent z))) p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  induction n generalizing p with
  | zero =>
    simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p
        (positive_open_integrand_joint_contDiff f).contDiffAt
  | succ n ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => fderiv ℝ
        (iteratedFDeriv ℝ n (fun z => f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent z)))) p.2) p := by
      exact ((ih (p.1,p.2)).comp (p,p.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)).fderiv
        (m := (⊤ : ℕ∞)) contDiffAt_snd (by simp)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => ℂ) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp p hd

lemma positive_open_integrand_jets_measurable (β : ℂˣ) (f : PrincipalSeries positiveParameter)
    (n : ℕ) (z : ℂ) : AEStronglyMeasurable (fun x : ℂ => iteratedFDeriv ℝ n
      (fun z => f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) z) (characterHaar β) := by
  exact ((positive_open_integrand_jets_contDiff f n).continuous.comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable

set_option backward.isDefEq.respectTransparency false in
lemma positive_open_contDiff_of_jet_bounds (β : ℂˣ) (f : PrincipalSeries positiveParameter)
    (hbound : ∀ n : ℕ, ∀ z : ℂ, ∃ (s : Set ℂ) (b : ℂ → ℝ),
      s ∈ nhds z ∧ Integrable b (characterHaar β) ∧
        ∀ᵐ x ∂characterHaar β, ∀ w ∈ s,
          ‖iteratedFDeriv ℝ n (fun v =>
            f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w‖ ≤ b x) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  have hs (x : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) := by
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (x, z)) :=
      contDiff_const.prodMk contDiff_id
    have hh := (positive_open_integrand_joint_contDiff f).comp he
    exact hh
  exact (integral_contDiff_of_locally_dominated_jets (characterHaar β)
    (fun z x => f (weyl * upperUnipotent x * (weyl * upperUnipotent z))) hs
    (positive_open_integrand_jets_measurable β f) hbound).1

open scoped Matrix.Norms.Elementwise

private lemma intertwiner_open_matrix_identity (x z : ℂ) (hx : x ≠ 0) :
  weyl * upperUnipotent x * (weyl * upperUnipotent z) =
    upperTriangular (Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx))) (Units.mk0 x hx) 1 *
      (weyl * upperUnipotent (z+x⁻¹)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangular, weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
      hx, mul_add, mul_assoc, add_comm]

lemma intertwiner_open_integrand_eq (s : ℝ) (f : PrincipalSeries s) (x z : ℂ) (hx : x ≠ 0) :
    f (weyl * upperUnipotent x * (weyl * upperUnipotent z)) =
      ((‖x‖ ^ (-2 * (1 + 2*s)) : ℝ) : ℂ) * openCoordinate f (z+x⁻¹) := by
  rw [intertwiner_open_matrix_identity x z hx, f.property.1]
  congr 1
  simp only [inductionWeight, complexAbs, Units.val_mk0, norm_div, norm_neg, norm_inv]
  have hi : ‖x‖⁻¹ / ‖x‖ = (‖x‖ ^ 2)⁻¹ := by
    simp [div_eq_mul_inv, pow_two, mul_inv]
  simp only [Real.rpow_eq_pow]
  rw [hi, inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    ← Real.rpow_natCast_mul (by positivity), ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  ring

lemma intertwiner_tail_weight_integrable (β : ℂˣ) :
    IntegrableOn (fun x : ℂ => ‖x‖ ^ (-(8/3 : ℝ)))
      (Metric.closedBall (0 : ℂ) 1)ᶜ (characterHaar β) := by
  letI := characterHaar_isAddHaarMeasure β
  have hi : Integrable (fun x : ℂ => (1+‖x‖) ^ (-(8/3 : ℝ))) (characterHaar β) :=
    integrable_one_add_norm (by norm_num [Complex.finrank_real_complex])
  apply (hi.mul_const ((2 : ℝ) ^ (8/3 : ℝ))).integrableOn.mono'
  · exact (by fun_prop : Measurable (fun x : ℂ => ‖x‖ ^ (-(8/3 : ℝ)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (Metric.isClosed_closedBall.measurableSet.compl)] with x hx
    have hx : 1 ≤ ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using (le_of_lt (show 1 < ‖x‖ by simpa using hx))
    have ht : (1+‖x‖)/2 ≤ ‖x‖ := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1+‖x‖)/2) ht
      (by norm_num : -(8/3 : ℝ) ≤ 0)
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] using h

theorem positive_intertwiner_openCoordinate_contDiff (β : ℂˣ)
    (f : PrincipalSeries positiveParameter) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (fun g : ComplexGL2 =>
      ∫ x : ℂ, f (weyl * upperUnipotent x * g) ∂characterHaar β)) := by
  apply positive_open_contDiff_of_jet_bounds β f
  intro n z
  let G : ℂ × ℂ → ℂ := fun p =>
    f (weyl * upperUnipotent p.1 * (weyl * upperUnipotent p.2))
  obtain ⟨C₀, hC₀, hcompact⟩ :=
    OpenSmoothness.compact_family_spatial_jets_bounded G
      (positive_open_integrand_joint_contDiff f) n z
  obtain ⟨C₁, hC₁, htranslate⟩ :=
    OpenSmoothness.weighted_inverse_translate_spatial_jets_bounded
      (openCoordinate f) f.property.2.1 (-(8 / 3 : ℝ)) n z
  have htail : ∀ x ∈ (Metric.closedBall (0 : ℂ) 1)ᶜ,
      ∀ w ∈ Metric.closedBall z 1,
        ‖iteratedFDeriv ℝ n (fun v =>
          f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w‖ ≤
            C₁ * ‖x‖ ^ (-(8 / 3 : ℝ)) := by
    intro x hx w hw
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      simp at hx
    have he : (fun v => f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) =
        (fun v => ((‖x‖ ^ (-(8 / 3 : ℝ)) : ℝ) : ℂ) *
          openCoordinate f (v + x⁻¹)) := by
      funext v
      have ha : -2 * (1 + 2 * positiveParameter) = -(8 / 3 : ℝ) := by
        norm_num [positiveParameter]
      simpa only [ha] using
        intertwiner_open_integrand_eq positiveParameter f x v hx0
    rw [he]
    exact htranslate x hx w hw
  letI := characterHaar_isAddHaarMeasure β

  exact OpenSmoothness.local_majorant_of_finite_piece_and_integrable_tail
    (characterHaar β) (Metric.closedBall (0 : ℂ) 1)
    Metric.isClosed_closedBall.measurableSet
    ((isCompact_closedBall (0 : ℂ) 1).measure_lt_top)
    (fun w x => iteratedFDeriv ℝ n (fun v =>
      f (weyl * upperUnipotent x * (weyl * upperUnipotent v))) w)
    (fun x => ‖x‖ ^ (-(8 / 3 : ℝ))) (intertwiner_tail_weight_integrable β)
    z C₀ C₁ hcompact htail

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end
