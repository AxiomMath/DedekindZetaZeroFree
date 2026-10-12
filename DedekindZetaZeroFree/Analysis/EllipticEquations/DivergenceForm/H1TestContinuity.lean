module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

open MeasureTheory KPContLocalNorm Raw Filter Topology

private theorem norm_sq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (v : Lp ℂ 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
private theorem lp_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℂ) (hf : ∀ m, MemLp (f m) 2 μ) (w : Lp ℂ 2 μ)
    (ht : Tendsto (fun m => ∫ x, ‖f m x - w x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 w) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (m : ℕ) : ‖(hf m).toLp (f m) - w‖ ^ 2 =
      ∫ x, ‖f m x - w x‖ ^ 2 ∂μ := by
    rw [norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf m).toLp (f m)) w, (hf m).coeFn_toLp] with x hs hf'
    simp only [Pi.sub_apply] at hs
    rw [hs, hf']
  have ht' : Tendsto (fun m => ‖(hf m).toLp (f m) - w‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using ht
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp ht'
private theorem integral_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℂ) (hf : ∀ m, MemLp (f m) 2 μ) (w : Lp ℂ 2 μ)
    (ht : Tendsto (fun m => ∫ x, ‖f m x - w x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (g : α → ℂ) (hg : MemLp g 2 μ) :
    Tendsto (fun m => ∫ x, g x * star (f m x) ∂μ) atTop
      (𝓝 (∫ x, g x * star (w x) ∂μ)) := by
  have he (m : ℕ) : (∫ x, g x * star (f m x) ∂μ) =
      inner ℂ ((hf m).toLp (f m)) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hf m).coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp [RCLike.inner_apply, hx, hy]
  have hw : (∫ x, g x * star (w x) ∂μ) = inner ℂ w (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [RCLike.inner_apply, hx]
  simp only [he, hw]
  exact (lp_tendsto f hf w ht).inner tendsto_const_nhds
private theorem test_derivative_memLp {n : ℕ} (B : LocalBall n)
    (φ : TestFunction B.toOpens ℂ ⊤) (l : List (Fin n)) :
    MemLp (coordinateDerivativeList l (fun y => φ y)) 2 (volume.restrict B.carrier) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l (fun y => φ y)) ∧
      HasCompactSupport (coordinateDerivativeList l (fun y => φ y)) := by
    induction l with
    | nil => exact ⟨φ.contDiff, φ.hasCompactSupport⟩
    | cons i l ih =>
      refine ⟨(ih.1.fderiv_right (by simp)).clm_apply contDiff_const, ?_⟩
      exact (ih.2.fderiv ℝ).comp_left (g := fun f => f (EuclideanSpace.single i 1)) (by simp)
  exact (hs.1.continuous.memLp_of_hasCompactSupport hs.2).mono_measure Measure.restrict_le_self

private theorem first_directions {n : ℕ} (i : Fin n) : (firstIndex i).directions = [i] := by
  classical
  have aux : ∀ (l : List (Fin n)), l.Nodup → i ∈ l →
      l.flatMap (fun j => if j = i then [j] else []) = [i] := by
    intro l hn hi
    induction l with
    | nil => simp at hi
    | cons a l ih =>
      simp only [List.nodup_cons] at hn
      simp only [List.mem_cons] at hi
      by_cases h : a = i
      · subst a
        rw [List.flatMap_cons, if_pos rfl]
        have hz : l.flatMap (fun j => if j = i then [j] else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro j hj
          rw [if_neg]
          exact fun e => hn.1 (e ▸ hj)
        simp [hz]
      · rw [List.flatMap_cons, if_neg h]
        simpa using ih hn.2 (hi.resolve_left (Ne.symm h))
  unfold MultiIndex.directions firstIndex
  simp only [apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  have he : (fun j : Fin n => List.replicate (if j = i then 1 else 0) j) =
      (fun j => if j = i then [j] else []) := by
    funext j
    split_ifs <;> simp
  rw [he]
  exact aux (List.finRange n) (List.nodup_finRange _) (List.mem_finRange i)

private theorem matrix_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ} (D : Coefficients B cρ Cρ κ Λ)
    (hκ : 0 < κ) (x : Space n) (hx : x ∈ B.carrier) (i j : Fin n) :
    |D.matrix x i j| ≤ |Λ| := by
  classical
  have hd (k : Fin n) : 0 ≤ D.matrix x k k := by
    have h := D.ellipticity x hx (EuclideanSpace.single k 1)
    simp [EuclideanSpace.norm_single, EuclideanSpace.single_apply] at h
    linarith
  have hu (k : Fin n) : D.matrix x k k ≤ Λ := by
    have h := D.upper_bound x hx (EuclideanSpace.single k 1)
    simpa [EuclideanSpace.norm_single, EuclideanSpace.single_apply] using h
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hd i)]
    exact (hu i).trans (le_abs_self Λ)
  have hnorm (t : ℝ) :
      ‖(EuclideanSpace.single i 1 + EuclideanSpace.single j t : Space n)‖ ^ 2 = 1 + t ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, PiLp.add_apply, EuclideanSpace.single_apply,
      add_sq, Finset.sum_add_distrib, hij, Ne.symm hij]
  have hquad (t : ℝ) := D.upper_bound x hx
    (EuclideanSpace.single i 1 + EuclideanSpace.single j t)
  simp only [hnorm] at hquad
  have hq (t : ℝ) :
      D.matrix x i i + 2 * D.matrix x i j * t + D.matrix x j j * t ^ 2 ≤ Λ * (1 + t ^ 2) := by
    have h := hquad t
    simp [PiLp.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
      EuclideanSpace.single_apply, D.symmetric x hx j i] at h
    nlinarith [h]
  apply abs_le.mpr
  constructor <;> nlinarith [hq 1, hq (-1), hd i, hd j, le_abs_self Λ]

private theorem density_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hcρ : 0 < cρ) :
    MemLp (fun x => (D.density x : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn D.density_smooth.continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) Cρ
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_trans hcρ.le (D.density_bounds x hx).1)]
  exact (D.density_bounds x hx).2

private theorem matrix_memLp {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hκ : 0 < κ) (i j : Fin n) :
    MemLp (fun x => (D.matrix x i j : ℂ)) ⊤ (volume.restrict B.carrier) := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp_continuousOn (D.matrix_smooth i j).continuousOn).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) |Λ|
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  simpa using matrix_bound D hκ x hx i j

private theorem zero_directions (n k : ℕ) : (zeroIndex n k).directions = [] := by
  simp [MultiIndex.directions, zeroIndex]

theorem weakEquation_of_test_limit {n : ℕ} (B : LocalBall n)
    (cρ Cρ κ Λ : ℝ) (hcρ : 0 < cρ) (hκ : 0 < κ)
    (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) (heq : WeakEquation D z u h)
    (w : IntegerSobolev B 1) (φ : ℕ → TestFunction B.toOpens ℂ ⊤)
    (hφ : ∀ α : MultiIndex n 1,
      Tendsto (fun m => ∫ x in B.carrier,
        ‖coordinateDerivative α (fun y => φ m y) x - w.derivatives α x‖ ^ 2)
        atTop (𝓝 0)) :
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * value u x * star (value w x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * h x * star (value w x) := by
  classical
  let μ := volume.restrict B.carrier
  have hρ := density_memLp D hcρ
  have hA := matrix_memLp D hκ
  have hzero : Tendsto (fun m => ∫ x in B.carrier, ‖φ m x - value w x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [coordinateDerivative, zero_directions, coordinateDerivativeList, value] using
      hφ (zeroIndex n 1)
  have hfirst (i : Fin n) : Tendsto (fun m => ∫ x in B.carrier,
      ‖coordinateDerivativeList [i] (fun y => φ m y) x - gradient w i x‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [coordinateDerivative, first_directions, Raw.gradient] using hφ (firstIndex i)
  have htests (m : ℕ) : MemLp (fun x => φ m x) 2 μ :=
    test_derivative_memLp B (φ m) []
  have hder (i : Fin n) (m : ℕ) :
      MemLp (coordinateDerivativeList [i] (fun y => φ m y)) 2 μ :=
    test_derivative_memLp B (φ m) [i]
  let g := fun (i j : Fin n) (x : Space n) =>
    (D.density x : ℂ) * (D.matrix x i j : ℂ) * gradient u j x
  have hg (i j : Fin n) : MemLp (g i j) 2 μ := by
    have ht : MemLp (fun x => (D.density x : ℂ) *
        ((D.matrix x i j : ℂ) * gradient u j x)) 2 μ :=
      hρ.mul (show MemLp (fun x => (D.matrix x i j : ℂ) * gradient u j x) 2 μ from
        (hA i j).mul (Lp.memLp (gradient u j)))
    simpa only [mul_assoc, g] using ht
  have hv : MemLp (fun x => (D.density x : ℂ) * value u x) 2 μ :=
    hρ.mul (Lp.memLp (value u))
  have hh : MemLp (fun x => (D.density x : ℂ) * h x) 2 μ := hρ.mul (Lp.memLp h)
  have hV := integral_tendsto (fun m x => φ m x) htests (value w) hzero
    (fun x => (D.density x : ℂ) * value u x) hv
  have hH := integral_tendsto (fun m x => φ m x) htests (value w) hzero
    (fun x => (D.density x : ℂ) * h x) hh
  have hG (i j : Fin n) := integral_tendsto
    (fun m => coordinateDerivativeList [i] (fun y => φ m y)) (hder i)
    (gradient w i) (hfirst i) (g i j) (hg i j)
  have hsum (v : Fin n → Space n → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) :
      (∫ x in B.carrier, (D.density x : ℂ) * ∑ i, ∑ j,
        (D.matrix x i j : ℂ) * gradient u j x * star (v i x)) =
      ∑ i, ∑ j, ∫ x in B.carrier, g i j x * star (v i x) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum]
      intro j hj
      exact (hg i j).integrable_mul (hv i).star
    · intro i hi
      exact integrable_finset_sum _ (fun j hj => (hg i j).integrable_mul (hv i).star)
  have hE : Tendsto (fun m => ∫ x in B.carrier, (D.density x : ℂ) * ∑ i, ∑ j,
      (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ m y) x)) atTop
      (𝓝 (∫ x in B.carrier, (D.density x : ℂ) * ∑ i, ∑ j,
        (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x))) := by
    simp only [hsum _ (fun i => Lp.memLp (gradient w i)),
      hsum _ (fun i => hder i _)]
    exact tendsto_finset_sum _ (fun i hi => tendsto_finset_sum _ (fun j hj => hG i j))
  exact tendsto_nhds_unique (hE.sub (tendsto_const_nhds.mul hV))
    (hH.congr (fun m => (heq (φ m)).symm))

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
