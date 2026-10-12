module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw

theorem coordinateDerivativeList_contDiffOn_open {n : ℕ} {U : Set (Space n)}
    (hU : IsOpen U) {u : Space n → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (l : List (Fin n)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) U := by
  induction l with
  | nil => exact hu
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem coordinateDerivative_memLp_of_closedBall {n k : ℕ} (B : LocalBall n)
    {U : Set (Space n)} (hU : IsOpen U)
    (hclosed : Metric.closedBall B.center B.radius ⊆ U)
    {u : Space n → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (α : MultiIndex n k) :
    MemLp (coordinateDerivative α u) 2 (volume.restrict B.carrier) := by
  have hsub : B.carrier ⊆ Metric.closedBall B.center B.radius :=
    Metric.ball_subset_closedBall
  have hcompact : IsCompact (Metric.closedBall B.center B.radius) :=
    isCompact_closedBall _ _
  have hc := (coordinateDerivativeList_contDiffOn_open hU hu α.directions).continuousOn
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hc.mono hclosed)
  have hfinite : volume B.carrier < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hcompact.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict B.carrier) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  apply MemLp.of_enorm_bound ((hc.mono (hsub.trans hclosed)).aestronglyMeasurable
    Metric.isOpen_ball.measurableSet) ENNReal.ofReal_ne_top
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact (ofReal_norm_eq_enorm _).symm.le.trans (ENNReal.ofReal_le_ofReal (hC x (hsub hx)))

theorem l2_norm_eq_functionL2Norm_of_ae {n : ℕ} (B : LocalBall n)
    (v : BallL2 B) (u : Space n → ℂ)
    (hvu : ∀ᵐ x ∂volume.restrict B.carrier, v x = u x) :
    ‖v‖ = functionL2Norm B u := by
  have hnorm : ‖v‖ ^ 2 = ∫ x in B.carrier, ‖u x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hvu] with x hx
    rw [hx]
  rw [functionL2Norm, ← hnorm, Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem coordinateDerivative_zeroIndex {n k : ℕ} (u : Space n → ℂ) :
    coordinateDerivative (zeroIndex n k) u = u := by
  have hnil : (List.finRange n).flatMap (fun _ => ([] : List (Fin n))) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  simp [coordinateDerivative, zeroIndex, MultiIndex.directions, coordinateDerivativeList, hnil]

@[simp] theorem firstIndex_directions {n : ℕ} (i : Fin n) :
    (firstIndex i).directions = [i] := by
  classical
  have h : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      l.flatMap (fun j => if j = i then [j] else []) = [i] := by
    intro l hn hi
    induction l with
    | nil => simp at hi
    | cons j l ih =>
      simp only [List.nodup_cons] at hn
      simp only [List.mem_cons] at hi
      simp only [List.flatMap_cons]
      by_cases hj : j = i
      · subst j
        rw [if_pos rfl]
        have hz : l.flatMap (fun j => if j = i then [j] else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro j hj
          rw [if_neg (by intro he; subst j; exact hn.1 hj)]
        simp [hz]
      · rw [if_neg hj]
        simpa using ih hn.2 (hi.resolve_left (Ne.symm hj))
  rw [MultiIndex.directions]
  convert h (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i) using 1
  apply List.flatMap_congr
  intro j _
  by_cases hj : j = i <;> simp [firstIndex, hj]

def derivativeTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ

@[simp] theorem derivativeTest_apply {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    derivativeTest φ i x = coordinateDerivativeList [i] (fun y => φ y) x := by
  rw [derivativeTest, TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv

theorem integral_mul_coordinateDerivative_test {n : ℕ} (B : LocalBall n)
    {f : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) :
    (∫ x in B.carrier, f x * coordinateDerivativeList [i] (fun y => φ y) x) =
      -(∫ x in B.carrier, coordinateDerivativeList [i] f x * φ x) := by
  have hc := (coordinateDerivativeList_contDiffOn_open Metric.isOpen_ball hf [i]).continuousOn
  have hi (g : Space n → ℂ) (hg : ContinuousOn g B.carrier)
      (ψ : TestFunction B.toOpens ℂ ⊤) : Integrable (fun x => g x * ψ x) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ)
        (hg.locallyIntegrableOn Metric.isOpen_ball.measurableSet)
  have h1 := hi _ hc φ
  have h2 := hi _ hf.continuousOn (derivativeTest φ i)
  simp only [derivativeTest_apply] at h2
  have h3 := hi _ hf.continuousOn φ
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x hx => (hf.differentiableOn (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (φ.tsupport_subset hx)))
    (fun x _ => φ.contDiff.differentiable (by simp) x)
  have hs (g : Space n → ℂ) (ψ : TestFunction B.toOpens ℂ ⊤) :
      (∫ x in B.carrier, g x * ψ x) = ∫ x, g x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [ψ.zero_on_compl hx, Pi.zero_apply, mul_zero]
  have hleft := hs f (derivativeTest φ i)
  simp only [derivativeTest_apply] at hleft
  rw [hleft, hs (coordinateDerivativeList [i] f) φ]
  exact he

theorem integrable_mul_test {n : ℕ} (B : LocalBall n) {g : Space n → ℂ}
    (hg : ContinuousOn g B.carrier) (ψ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => g x * ψ x) volume := by
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
    ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ)
      (hg.locallyIntegrableOn Metric.isOpen_ball.measurableSet)

def conjugateTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap φ

@[simp] theorem conjugateTest_apply {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (x : Space n) :
    conjugateTest φ x = star (φ x) := rfl

@[simp] theorem coordinateDerivative_conjugateTest {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    coordinateDerivativeList [i] (fun y => conjugateTest φ y) x =
      star (coordinateDerivativeList [i] (fun y => φ y) x) := by
  simp only [coordinateDerivativeList, conjugateTest_apply, fderiv_star]
  rfl

def classicalFlux {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (u : Space n → ℂ) (i : Fin n) : Space n → ℂ :=
  fun x => (D.density x : ℂ) * ∑ j, (D.matrix x i j : ℂ) *
    coordinateDerivativeList [j] u x

 theorem classicalFlux_smooth {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) {u : Space n → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (i : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (classicalFlux D u i) B.carrier := by
  apply (Complex.ofRealCLM.contDiff.comp_contDiffOn D.density_smooth).mul
  apply ContDiffOn.sum
  intro j _
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (D.matrix_smooth i j)).mul
    (coordinateDerivativeList_contDiffOn_open Metric.isOpen_ball hu [j])

theorem classical_weighted_weak {n : ℕ} (B : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (hcρ : 0 < cρ) (D : Coefficients B cρ Cρ κ Λ)
    (z : ℂ) {u : Space n → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (h : BallL2 B)
    (heq : ∀ᵐ x ∂volume.restrict B.carrier, divergenceOperator D u x - z * u x = h x)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * coordinateDerivativeList [j] u x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * u x * star (φ x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * h x * star (φ x) := by
  classical
  let ψ := conjugateTest φ
  have hf (i) := classicalFlux_smooth D hu i
  have hd (i) := coordinateDerivativeList_contDiffOn_open Metric.isOpen_ball (hf i) [i]
  have hdi (i) : IntegrableOn (fun x => coordinateDerivativeList [i] (classicalFlux D u i) x * ψ x)
      B.carrier volume := (integrable_mul_test B (hd i).continuousOn ψ).integrableOn
  have hfi (i) : IntegrableOn (fun x => classicalFlux D u i x *
      coordinateDerivativeList [i] (fun y => ψ y) x) B.carrier volume := by
    simpa only [derivativeTest_apply] using
      (integrable_mul_test B (hf i).continuousOn (derivativeTest ψ i)).integrableOn
  have hmass : IntegrableOn (fun x => (D.density x : ℂ) * u x * ψ x) B.carrier volume :=
    (integrable_mul_test B ((Complex.ofRealCLM.continuous.comp_continuousOn
      D.density_smooth.continuousOn).mul hu.continuousOn) ψ).integrableOn
  have hpoint : ∀ᵐ x ∂volume.restrict B.carrier,
      (D.density x : ℂ) * h x * ψ x =
      -(∑ i, coordinateDerivativeList [i] (classicalFlux D u i) x * ψ x) -
        z * ((D.density x : ℂ) * u x * ψ x) := by
    filter_upwards [heq, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
    have hr : (D.density x : ℂ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le hcρ (D.density_bounds x hxb).1).ne'
    rw [← hx, divergenceOperator]
    change (D.density x : ℂ) *
      (-(D.density x : ℂ)⁻¹ * ∑ i, coordinateDerivativeList [i] (classicalFlux D u i) x - z * u x) * ψ x = _
    rw [← Finset.sum_mul]
    field_simp
    <;> ring
  have hh := integral_congr_ae hpoint
  have hsum : IntegrableOn (fun x => ∑ i, coordinateDerivativeList [i] (classicalFlux D u i) x * ψ x)
      B.carrier volume := integrable_finsetSum Finset.univ (fun i _ => hdi i)
  have hneg : IntegrableOn (fun x => -(∑ i, coordinateDerivativeList [i] (classicalFlux D u i) x * ψ x))
      B.carrier volume := hsum.neg
  rw [integral_sub hneg (hmass.const_mul z), integral_neg,
    integral_finset_sum _ (fun i _ => hdi i), integral_const_mul] at hh
  have hflux : (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * coordinateDerivativeList [j] u x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      -(∑ i, ∫ x in B.carrier, coordinateDerivativeList [i] (classicalFlux D u i) x * ψ x) := by
    have hp : (fun x => (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * coordinateDerivativeList [j] u x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) =
        (fun x => ∑ i, classicalFlux D u i x * coordinateDerivativeList [i] (fun y => ψ y) x) := by
      funext x
      simp only [ψ, coordinateDerivative_conjugateTest, classicalFlux,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [hp, integral_finset_sum _ (fun i _ => hfi i)]
    simp_rw [integral_mul_coordinateDerivative_test B (hf _) ψ]
    rw [Finset.sum_neg_distrib]
  rw [hflux]
  exact hh.symm

theorem smooth_solution_to_weak {n : ℕ} (outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (hcρ : 0 < cρ) (D : Coefficients outer cρ Cρ κ Λ)
    (z : ℂ) (u : Space n → ℂ) (h : BallL2 outer)
    (U : Set (Space n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall outer.center outer.radius ⊆ U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (heq : ∀ᵐ x ∂volume.restrict outer.carrier,
      divergenceOperator D u x - z * u x = h x) :
    ∃ w : IntegerSobolev outer 1,
      RepresentsClassicalDerivatives w u ∧ WeakEquation D z w h ∧
      ‖value w‖ = functionL2Norm outer u := by
  have hsub : outer.carrier ⊆ U := Metric.ball_subset_closedBall.trans hclosed
  have hL2 (α : MultiIndex n 1) :=
    coordinateDerivative_memLp_of_closedBall outer hU hclosed hu α
  obtain ⟨w, hw⟩ := smooth_has_integerSobolev_data outer u (hu.mono hsub) hL2
  have hrep : RepresentsClassicalDerivatives w u := by
    intro α
    rw [hw α]
    exact (hL2 α).coeFn_toLp
  refine ⟨w, hrep, ?_, ?_⟩
  · intro φ
    have hv : ∀ᵐ x ∂volume.restrict outer.carrier, value w x = u x := by
      simpa only [value, coordinateDerivative_zeroIndex] using hrep (zeroIndex n 1)
    have hg : ∀ᵐ x ∂volume.restrict outer.carrier,
        ∀ j, gradient w j x = coordinateDerivativeList [j] u x := by
      apply ae_all_iff.mpr
      intro j
      simpa only [Raw.gradient, coordinateDerivative, firstIndex_directions] using hrep (firstIndex j)
    have henergy : (∫ x in outer.carrier, (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient w j x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) =
        (∫ x in outer.carrier, (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * coordinateDerivativeList [j] u x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      simp_rw [hx]
    have hmass : (∫ x in outer.carrier, (D.density x : ℂ) * value w x * star (φ x)) =
        (∫ x in outer.carrier, (D.density x : ℂ) * u x * star (φ x)) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    change _ - z * _ = _
    rw [henergy, hmass]
    exact classical_weighted_weak outer hcρ D z (hu.mono hsub) h heq φ
  · apply l2_norm_eq_functionL2Norm_of_ae
    simpa only [value, coordinateDerivative_zeroIndex] using hrep (zeroIndex n 1)

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
