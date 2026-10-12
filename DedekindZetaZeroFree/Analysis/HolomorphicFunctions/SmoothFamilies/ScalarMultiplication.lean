module

public import DedekindZetaZeroFree.Analysis.HolomorphicFunctions.SmoothFamilies.CompactJetTopology

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

open KPContLocalNorm
open scoped NNReal

theorem finite_coordinate_derivative_smooth {n : ℕ} (B : LocalBall n)
    {f : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (l : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) B.carrier := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const

theorem finite_coordinate_derivative_const_mul {n : ℕ} (l : List (Fin n))
    (c : ℂ) (f : Space n → ℂ) :
    coordinateDerivativeList l (fun y => c * f y) =
      fun y => c * coordinateDerivativeList l f y := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [coordinateDerivativeList, ih]
    funext x
    simpa only [Pi.smul_def, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply] using
      congrArg (fun L : Space n →L[ℝ] ℂ => L (EuclideanSpace.single i 1))
        (congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := coordinateDerivativeList l f) c) x)

theorem finite_coordinate_derivative_sum {n : ℕ} (B : LocalBall n)
    {ι : Type*} (s : Finset ι) (f : ι → Space n → ℂ)
    (hf : ∀ j ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (f j) B.carrier)
    (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (fun y => ∑ j ∈ s, f j y))
      (fun y => ∑ j ∈ s, coordinateDerivativeList l (f j) y) B.carrier := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have he : coordinateDerivativeList l (fun y => ∑ j ∈ s, f j y) =ᶠ[nhds x]
        (fun y => ∑ j ∈ s, coordinateDerivativeList l (f j) y) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨B.carrier,
        Metric.isOpen_ball.mem_nhds hx, ih⟩
    simp only [coordinateDerivativeList]
    rw [he.fderiv_eq]
    rw [fderiv_fun_sum]
    · simp only [ContinuousLinearMap.sum_apply]
    · intro j hj
      exact ((finite_coordinate_derivative_smooth B (hf j hj) l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)

theorem finite_coordinate_derivative_sub {n : ℕ} (B : LocalBall n)
    {f g : Space n → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g B.carrier) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList l (fun y => f y - g y))
      (fun y => coordinateDerivativeList l f y - coordinateDerivativeList l g y)
      B.carrier := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have he : coordinateDerivativeList l (fun y => f y - g y) =ᶠ[nhds x]
        (fun y => coordinateDerivativeList l f y - coordinateDerivativeList l g y) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨B.carrier,
        Metric.isOpen_ball.mem_nhds hx, ih⟩
    simp only [coordinateDerivativeList]
    rw [he.fderiv_eq, fderiv_fun_sub]
    · simp only [ContinuousLinearMap.sub_apply]
    · exact ((finite_coordinate_derivative_smooth B hf l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    · exact ((finite_coordinate_derivative_smooth B hg l).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)

theorem cauchy_product_coefficients_smooth {n : ℕ} (B : LocalBall n)
    (a : ℕ → ℂ) (b : ℕ → Space n → ℂ)
    (hb : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (b j) B.carrier) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2 y) B.carrier := by
  exact ContDiffOn.sum fun p _ => contDiffOn_const.mul (hb p.2)

theorem coordinate_derivative_cauchy_product {n m : ℕ} (B : LocalBall n)
    (a : ℕ → ℂ) (b : ℕ → Space n → ℂ)
    (hb : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (b j) B.carrier)
    (k : ℕ) (α : MultiIndex n m) :
    Set.EqOn
      (coordinateDerivative α
        (fun y => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2 y))
      (fun y => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        a p.1 * coordinateDerivative α (b p.2) y) B.carrier := by
  intro x hx
  change coordinateDerivativeList α.directions
      (fun y => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2 y) x = _
  rw [finite_coordinate_derivative_sum B (Finset.HasAntidiagonal.antidiagonal k)
    (fun p y => a p.1 * b p.2 y)
    (fun p _ => contDiffOn_const.mul (hb p.2)) α.directions hx]
  simp only [finite_coordinate_derivative_const_mul, coordinateDerivative]

theorem coordinate_derivative_taylor_remainder {n m : ℕ} (B : LocalBall n)
    (b : ℕ → Space n → ℂ) (hb : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (b j) B.carrier)
    (f : Space n → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier)
    (w : ℂ) (M : ℕ) (α : MultiIndex n m) :
    Set.EqOn
      (coordinateDerivative α (fun y => (∑ j ∈ Finset.range M, w ^ j * b j y) - f y))
      (fun y => (∑ j ∈ Finset.range M, w ^ j * coordinateDerivative α (b j) y) -
        coordinateDerivative α f y) B.carrier := by
  intro x hx
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => ∑ j ∈ Finset.range M, w ^ j * b j y) B.carrier :=
    ContDiffOn.sum fun j _ => contDiffOn_const.mul (hb j)
  change coordinateDerivativeList α.directions _ x = _
  rw [finite_coordinate_derivative_sub B hsum hf α.directions hx]
  dsimp only
  rw [finite_coordinate_derivative_sum B (Finset.range M) (fun j y => w ^ j * b j y)
      (fun j _ => contDiffOn_const.mul (hb j)) α.directions hx]
  simp only [finite_coordinate_derivative_const_mul, coordinateDerivative]

theorem smooth_power_series_tail_coefficient_bound {n : ℕ} (B : LocalBall n)
    (z₀ : ℂ) (ρ : ℝ) (b : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)
    (hb : Raw.SmoothPowerSeriesOn B z₀ ρ b f)
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (htρ : t < ρ) :
    ∃ N : ℕ, ∀ j ≥ N, ∀ α : MultiIndex n m, ∀ x : K,
      t ^ j * ‖coordinateDerivative α (b j) x‖ < 2 := by
  obtain ⟨N, hN⟩ := hb.2.2 K hK hKB m t ht htρ 1 (by norm_num)
  refine ⟨N, ?_⟩
  intro j hj α x
  let z : ℂ := z₀ + (t : ℂ)
  have hzt : z - z₀ = (t : ℂ) := by dsimp [z]; ring
  have hz : z ∈ Metric.closedBall z₀ t := by
    rw [Metric.mem_closedBall, dist_eq_norm, hzt, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht]
  have hzball : z ∈ Metric.ball z₀ ρ := Metric.mem_ball.mpr
    ((Metric.mem_closedBall.mp hz).trans_lt htρ)
  have hbound (M : ℕ) (hM : N ≤ M) :
      ‖(∑ k ∈ Finset.range M, (z - z₀) ^ k * coordinateDerivative α (b k) x) -
          coordinateDerivative α (f z) x‖ < 1 := by
    have he := coordinate_derivative_taylor_remainder B b hb.1 (f z)
      (hb.2.1 z hzball) (z - z₀) M α (hKB x.property)
    have hbound := hN M hM z hz α x
    rw [he] at hbound
    exact hbound
  have hsucc := hbound (j + 1) (hj.trans (Nat.le_succ j))
  have hprev := hbound j hj
  have he : (z - z₀) ^ j * coordinateDerivative α (b j) x =
      ((∑ k ∈ Finset.range (j + 1), (z - z₀) ^ k * coordinateDerivative α (b k) x) -
        coordinateDerivative α (f z) x) -
      ((∑ k ∈ Finset.range j, (z - z₀) ^ k * coordinateDerivative α (b k) x) -
        coordinateDerivative α (f z) x) := by
    rw [Finset.sum_range_succ]
    ring
  have hnorm : ‖(z - z₀) ^ j * coordinateDerivative α (b j) x‖ < 2 := by
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  simpa only [norm_mul, norm_pow, hzt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht] using hnorm

theorem smooth_power_series_coefficient_bound {n : ℕ} (B : LocalBall n)
    (z₀ : ℂ) (ρ : ℝ) (b : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)
    (hb : Raw.SmoothPowerSeriesOn B z₀ ρ b f)
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (htρ : t < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ α : MultiIndex n m, ∀ x : K,
      t ^ j * ‖coordinateDerivative α (b j) x‖ ≤ C := by
  obtain ⟨N, hN⟩ := smooth_power_series_tail_coefficient_bound B z₀ ρ b f hb
    K hK hKB m t ht htρ
  let F : Space n → ℝ := fun x => ∑ j ∈ Finset.range N,
    ∑ α : MultiIndex n m, t ^ j * ‖coordinateDerivative α (b j) x‖
  have hF : ContinuousOn F K := by
    apply continuousOn_finsetSum
    intro j hj
    apply continuousOn_finsetSum
    intro α hα
    exact continuousOn_const.mul
      (((finite_coordinate_derivative_smooth B (hb.1 j) α.directions).continuousOn.mono hKB).norm)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨|D| + 3, by positivity, ?_⟩
  intro j α x
  by_cases hj : N ≤ j
  · exact (hN j hj α x).le.trans (by have := abs_nonneg D; linarith)
  · have hterm : t ^ j * ‖coordinateDerivative α (b j) x‖ ≤ F x := by
      calc
        t ^ j * ‖coordinateDerivative α (b j) x‖ ≤
            ∑ β : MultiIndex n m, t ^ j * ‖coordinateDerivative β (b j) x‖ :=
          Finset.single_le_sum
            (fun β _ => mul_nonneg (pow_nonneg ht j)
              (norm_nonneg (coordinateDerivative β (b j) x))) (Finset.mem_univ α)
        _ ≤ F x := by
          dsimp only [F]
          exact Finset.single_le_sum
            (fun k _ => Finset.sum_nonneg fun β _ =>
              mul_nonneg (pow_nonneg ht k) (norm_nonneg (coordinateDerivative β (b k) x)))
            (Finset.mem_range.mpr (Nat.lt_of_not_ge hj))
    exact hterm.trans ((le_abs_self (F x)).trans
      ((hD x x.property).trans ((le_abs_self D).trans (by linarith))))

theorem uniform_cauchy_product_of_majorants {X : Type*}
    (a b : ℕ → X → ℂ) (u v : ℕ → ℝ)
    (hu : Summable u) (hv : Summable v)
    (hu0 : ∀ j, 0 ≤ u j) (hv0 : ∀ j, 0 ≤ v j)
    (ha : ∀ j x, ‖a j x‖ ≤ u j) (hb : ∀ j x, ‖b j x‖ ≤ v j) :
    TendstoUniformly
      (fun N x => ∑ j ∈ Finset.range N,
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, a p.1 x * b p.2 x)
      (fun x => (∑' j, a j x) * ∑' j, b j x) Filter.atTop := by
  have hmajor : Summable (fun j =>
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, u p.1 * v p.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (hu.mul_of_nonneg hv hu0 hv0)
  have hbound : ∀ j x,
      ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, a p.1 x * b p.2 x‖ ≤
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, u p.1 * v p.2 := by
    intro j x
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [norm_mul]
    exact mul_le_mul (ha p.1 x) (hb p.2 x) (norm_nonneg _) (hu0 p.1)
  have hconv := tendstoUniformly_tsum_nat hmajor hbound
  have heq : (fun x => ∑' j,
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, a p.1 x * b p.2 x) =
      (fun x => (∑' j, a j x) * ∑' j, b j x) := by
    funext x
    exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (hu.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ha j x))
      (hv.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hb j x))).symm
  rw [heq] at hconv
  exact hconv

theorem smooth_series_jet_majorant {n : ℕ} (B : LocalBall n)
    (z₀ : ℂ) (ρ : ℝ) (b : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)
    (hb : Raw.SmoothPowerSeriesOn B z₀ ρ b f)
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) :
    ∃ v : ℕ → ℝ, Summable v ∧ (∀ j, 0 ≤ v j) ∧
      ∀ j z, z ∈ Metric.closedBall z₀ r → ∀ α : MultiIndex n m, ∀ x : K,
        ‖(z - z₀) ^ j * coordinateDerivative α (b j) x‖ ≤ v j := by
  obtain ⟨t, hrt, htρ⟩ := exists_between hrρ
  have ht : 0 < t := hr.trans_lt hrt
  obtain ⟨C, hC, hbound⟩ := smooth_power_series_coefficient_bound B z₀ ρ b f hb
    K hK hKB m t ht.le htρ
  refine ⟨fun j => C * (r / t) ^ j,
    (summable_geometric_of_lt_one (div_nonneg hr ht.le)
      ((div_lt_one ht).mpr hrt)).mul_left C,
    fun j => mul_nonneg hC.le (pow_nonneg (div_nonneg hr ht.le) j), ?_⟩
  intro j z hz α x
  have hz' : ‖z - z₀‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
  rw [norm_mul, norm_pow]
  calc
    ‖z - z₀‖ ^ j * ‖coordinateDerivative α (b j) x‖ ≤
        r ^ j * ‖coordinateDerivative α (b j) x‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz' j) (norm_nonneg _)
    _ = (r / t) ^ j * (t ^ j * ‖coordinateDerivative α (b j) x‖) := by
      rw [div_pow]; field_simp
    _ ≤ (r / t) ^ j * C := mul_le_mul_of_nonneg_left (hbound j α x)
      (pow_nonneg (div_nonneg hr ht.le) j)
    _ = C * (r / t) ^ j := mul_comm _ _

theorem smooth_series_jet_tsum {n m : ℕ} (B : LocalBall n)
    (z₀ : ℂ) (ρ : ℝ) (b : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)
    (hb : Raw.SmoothPowerSeriesOn B z₀ ρ b f)
    (K : Set (Space n)) (hK : IsCompact K) (hKB : K ⊆ B.carrier)
    (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) (z : ℂ) (hz : z ∈ Metric.closedBall z₀ r)
    (α : MultiIndex n m) (x : K)
    (hs : Summable (fun j => (z - z₀) ^ j * coordinateDerivative α (b j) x)) :
    (∑' j, (z - z₀) ^ j * coordinateDerivative α (b j) x) =
      coordinateDerivative α (f z) x := by
  have hzball := Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hrρ)
  have hc : Filter.Tendsto
      (fun M => ∑ j ∈ Finset.range M, (z - z₀) ^ j * coordinateDerivative α (b j) x)
      Filter.atTop (nhds (coordinateDerivative α (f z) x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hb.2.2 K hK hKB m r hr hrρ ε hε
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun M hM => ?_⟩
    rw [dist_eq_norm]
    have he := coordinate_derivative_taylor_remainder B b hb.1 (f z)
      (hb.2.1 z hzball) (z - z₀) M α (hKB x.property)
    have hh := hN M hM z hz α x
    rw [he] at hh
    exact hh
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hc

set_option maxHeartbeats 800000 in

theorem scalar_series_majorant (q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ≥0)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesOnBall q p z₀ R)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ j, 0 ≤ u j) ∧
      ∀ j z, z ∈ Metric.closedBall z₀ r → ‖(z - z₀) ^ j * p.coeff j‖ ≤ u j := by
  let r' : ℝ≥0 := ⟨r, hr⟩
  have hradius : (r' : ENNReal) < p.radius :=
    (ENNReal.coe_lt_coe.mpr (show r' < R from hrR)).trans_le hp.r_le
  refine ⟨fun j => ‖p j‖ * r ^ j, p.summable_norm_mul_pow hradius,
    fun j => mul_nonneg (norm_nonneg _) (pow_nonneg hr j), ?_⟩
  intro j z hz
  have hcoeff : ‖p.coeff j‖ ≤ ‖p j‖ := by
    simpa only [FormalMultilinearSeries.coeff, Pi.one_def, norm_one, Finset.prod_const_one,
      mul_one] using (p j).le_opNorm (fun _ => (1 : ℂ))
  have hz' : ‖z - z₀‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
  rw [norm_mul, norm_pow]
  exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz' j) hcoeff (norm_nonneg _)
    (pow_nonneg hr j)).trans_eq (mul_comm _ _)

theorem scalar_series_tsum (q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ≥0)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesOnBall q p z₀ R) (z : ℂ) (hz : z ∈ Metric.ball z₀ R) :
    (∑' j, (z - z₀) ^ j * p.coeff j) = q z := by
  have hz' : z - z₀ ∈ Metric.eball 0 (R : ENNReal) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
    simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
  have hh := (hp.hasSum hz').tsum_eq
  simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
    add_sub_cancel] using hh

set_option maxHeartbeats 800000 in

theorem smooth_series_scalar_product {n : ℕ} (B : LocalBall n)
    (z₀ : ℂ) (ρ : ℝ) (R : ℝ≥0) (hρR : ρ ≤ R)
    (q : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesOnBall q p z₀ R)
    (b : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ)
    (hb : Raw.SmoothPowerSeriesOn B z₀ ρ b f) :
    Raw.SmoothPowerSeriesOn B z₀ ρ
      (fun j y => ∑ a ∈ Finset.HasAntidiagonal.antidiagonal j, p.coeff a.1 * b a.2 y)
      (fun z y => q z * f z y) := by
  let c : ℕ → Space n → ℂ := fun j y =>
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal j, p.coeff a.1 * b a.2 y
  have hc : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (c j) B.carrier :=
    cauchy_product_coefficients_smooth B p.coeff b hb.1
  refine ⟨hc, fun z hz => contDiffOn_const.mul (hb.2.1 z hz), ?_⟩
  intro K hK hKB m r hr hrρ ε hε
  obtain ⟨u, hu, hu0, ha⟩ := scalar_series_majorant q z₀ R p hp r hr (hrρ.trans_le hρR)
  obtain ⟨v, hv, hv0, hbnd⟩ := smooth_series_jet_majorant B z₀ ρ b f hb K hK hKB m r hr hrρ
  let X := Metric.closedBall z₀ r × MultiIndex n m × K
  let A : ℕ → X → ℂ := fun j x => (x.1.val - z₀) ^ j * p.coeff j
  let D : ℕ → X → ℂ := fun j x => (x.1.val - z₀) ^ j * coordinateDerivative x.2.1 (b j) x.2.2
  have hA : ∀ j x, ‖A j x‖ ≤ u j := fun j x => ha j x.1 x.1.property
  have hD : ∀ j x, ‖D j x‖ ≤ v j := fun j x => hbnd j x.1 x.1.property x.2.1 x.2.2
  have hconv := uniform_cauchy_product_of_majorants A D u v hu hv hu0 hv0 hA hD
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hconv ε hε)
  refine ⟨N, ?_⟩
  intro M hM z hz α x
  let t : X := (⟨z, hz⟩, α, x)
  have hest := hN M hM t
  have hzball : z ∈ Metric.ball z₀ ρ := Metric.mem_ball.mpr
    ((Metric.mem_closedBall.mp hz).trans_lt hrρ)
  have hsA : (∑' j, A j t) = q z := scalar_series_tsum q z₀ R p hp z
    (Metric.ball_subset_ball hρR hzball)
  have hsD : (∑' j, D j t) = coordinateDerivative α (f z) x :=
    smooth_series_jet_tsum B z₀ ρ b f hb K hK hKB r hr hrρ z hz α x
      (hv.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hD j t)).of_norm
  have hprod (j : ℕ) :
      (∑ a ∈ Finset.HasAntidiagonal.antidiagonal j, A a.1 t * D a.2 t) =
        (z - z₀) ^ j * coordinateDerivative α (c j) x := by
    rw [coordinate_derivative_cauchy_product B p.coeff b hb.1 j α (hKB x.property)]
    dsimp only [A, D, t]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    rw [← he, pow_add]
    ring
  rw [hsA, hsD] at hest
  have he := coordinate_derivative_taylor_remainder B c hc (fun y => q z * f z y)
    (contDiffOn_const.mul (hb.2.1 z hzball)) (z - z₀) M α (hKB x.property)
  rw [he, coordinateDerivative, finite_coordinate_derivative_const_mul]
  have hsum : (∑ j ∈ Finset.range M, ∑ a ∈ Finset.HasAntidiagonal.antidiagonal j,
      A a.1 t * D a.2 t) = ∑ j ∈ Finset.range M,
        (z - z₀) ^ j * coordinateDerivative α (c j) x :=
    Finset.sum_congr rfl (fun j _ => hprod j)
  rw [hsum, dist_eq_norm, norm_sub_rev] at hest
  exact hest

end DedekindZetaZeroFree.KPContLocalHolomorphyUpgrade.CauchyAssembly

end
