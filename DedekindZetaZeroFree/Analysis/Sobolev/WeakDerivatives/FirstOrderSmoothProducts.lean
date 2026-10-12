module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates
open MeasureTheory KPContLocalNorm Raw
open scoped Topology
private theorem zero_dirs (n k : ℕ) : (zeroIndex n k).directions = [] := by
  simp [MultiIndex.directions, zeroIndex]
private theorem first_dirs {n : ℕ} (i : Fin n) : (firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, firstIndex, apply_ite Fin.val, Fin.val_one,
    Fin.val_zero, List.replicate_one, List.replicate_zero]
  have h : ∀ l : List (Fin n), l.flatMap (fun j => if j = i then [j] else []) = l.filter (· = i) := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
  have hrep : ∀ j : Fin n, List.replicate (if j = i then 1 else 0) j =
      if j = i then [j] else [] := by intro j; split_ifs <;> simp
  simp_rw [hrep]
  rw [h, List.filter_eq]
  simp
private theorem cases_idx {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n 1 ∨ ∃ i : Fin n, α = firstIndex i := by
  classical
  by_cases hz : ∀ i, (α.val i).val = 0
  · left; apply Subtype.ext; funext i; apply Fin.ext; exact hz i
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right; refine ⟨i, ?_⟩
    have hs := Finset.sum_le_one_iff.mp α.property
    have hone := (hs i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    apply Subtype.ext; funext j; apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        by_contra hj
        exact hji (hs j i (Finset.mem_univ _) (Finset.mem_univ _) hj hi).1
      simpa [firstIndex, hji] using hj
private theorem first_degree {n : ℕ} (i : Fin n) : (firstIndex i).degree = 1 := by
  simp only [firstIndex, MultiIndex.degree, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  simp
private theorem first_ne_zero {n : ℕ} (i : Fin n) : firstIndex i ≠ zeroIndex n 1 := by
  intro h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  simpa [firstIndex, zeroIndex] using he
private theorem first_inj {n : ℕ} : Function.Injective (@firstIndex n) := by
  intro i j h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  by_contra hij
  simpa [firstIndex, hij] using he

 def productTest {n : ℕ} {B : LocalBall n}
    (a φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  ⟨fun x => a x * φ x, a.contDiff.mul φ.contDiff,
    a.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans a.tsupport_subset⟩
 def partialTest {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (i : Fin n) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) a
private theorem partialTest_eq {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    partialTest a i x = coordinateDerivativeList [i] (fun y => a y) x := by
  rw [partialTest, TestFunction.lineDerivCLM_eq_fderivCLM]
  rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
  rfl
private theorem product_deriv {n : ℕ} {B : LocalBall n}
    (a φ : TestFunction B.toOpens ℂ ⊤) (i : Fin n) (x : Space n) :
    coordinateDerivativeList [i] (fun y => productTest a φ y) x =
      partialTest a i x * φ x + a x * partialTest φ i x := by
  change (fderiv ℝ (fun y => a y * φ y) x) (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_mul (a.contDiff.differentiable (by simp)).differentiableAt
    (φ.contDiff.differentiable (by simp)).differentiableAt]
  simp only [partialTest_eq, coordinateDerivativeList, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
private theorem test_mul_mem {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (u : BallL2 B) :
    MemLp (fun x => a x * u x) 2 (volume.restrict B.carrier) := by
  exact a.memLp_top.fun_mul (Lp.memLp u)
private theorem test_mul_integrable {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (u : BallL2 B) :
    Integrable (fun x => u x * a x) (volume.restrict B.carrier) := by
  exact (Lp.memLp u).integrable_mul
    (a.continuous.memLp_of_hasCompactSupport (p := 2) a.hasCompactSupport)

private theorem weak_product {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (u : IntegerSobolev B 1)
    (v : BallL2 B) (g : Fin n → BallL2 B)
    (hv : ∀ᵐ x ∂volume.restrict B.carrier, v x = a x * value u x)
    (hg : ∀ i, ∀ᵐ x ∂volume.restrict B.carrier,
      g i x = a x * gradient u i x + partialTest a i x * value u x) (i : Fin n) :
    IsWeakDerivative B (firstIndex i) v (g i) := by
  intro φ
  have hw := u.weak_derivatives (firstIndex i) (productTest a φ)
  change (∫ x in B.carrier, value u x * coordinateDerivative (firstIndex i)
      (fun y => productTest a φ y) x) =
    (-1 : ℂ) ^ (firstIndex i).degree *
      (∫ x in B.carrier, gradient u i x * productTest a φ x) at hw
  simp only [coordinateDerivative, first_dirs, first_degree, pow_one] at hw ⊢
  have hleft : (∫ x in B.carrier, v x * coordinateDerivativeList [i] (fun y => φ y) x) =
      ∫ x in B.carrier, value u x * (a x * partialTest φ i x) := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx, ← partialTest_eq]
    ring
  have hright : (∫ x in B.carrier, g i x * φ x) =
      (∫ x in B.carrier, gradient u i x * (a x * φ x)) +
      (∫ x in B.carrier, value u x * (partialTest a i x * φ x)) := by
    have h1 := test_mul_integrable (productTest a φ) (gradient u i)
    have h2 := test_mul_integrable (productTest (partialTest a i) φ) (value u)
    change Integrable (fun x => gradient u i x * (a x * φ x)) _ at h1
    change Integrable (fun x => value u x * (partialTest a i x * φ x)) _ at h2
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [hg i] with x hx
    rw [hx]
    ring
  have hexpand : (∫ x in B.carrier, value u x *
      coordinateDerivativeList [i] (fun y => productTest a φ y) x) =
      (∫ x in B.carrier, value u x * (partialTest a i x * φ x)) +
      (∫ x in B.carrier, value u x * (a x * partialTest φ i x)) := by
    have h1 := test_mul_integrable (productTest (partialTest a i) φ) (value u)
    have h2 := test_mul_integrable (productTest a (partialTest φ i)) (value u)
    change Integrable (fun x => value u x * (partialTest a i x * φ x)) _ at h1
    change Integrable (fun x => value u x * (a x * partialTest φ i x)) _ at h2
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [product_deriv]
    ring
  rw [hexpand] at hw
  change _ = -1 * (∫ x in B.carrier, gradient u i x * (a x * φ x)) at hw
  rw [hleft, hright]
  linear_combination hw

private theorem multiply_test {n : ℕ} {B : LocalBall n}
    (a : TestFunction B.toOpens ℂ ⊤) (u : IntegerSobolev B 1) :
    ∃ w : IntegerSobolev B 1,
      (∀ᵐ x ∂volume.restrict B.carrier, value w x = a x * value u x) ∧
      ∀ i : Fin n, ∀ᵐ x ∂volume.restrict B.carrier,
        gradient w i x = a x * gradient u i x + partialTest a i x * value u x := by
  classical
  let v : BallL2 B := (test_mul_mem a (value u)).toLp _
  let g : Fin n → BallL2 B := fun i =>
    ((test_mul_mem a (gradient u i)).add (test_mul_mem (partialTest a i) (value u))).toLp _
  have hv : ∀ᵐ x ∂volume.restrict B.carrier, v x = a x * value u x :=
    MemLp.coeFn_toLp _
  have hg : ∀ i, ∀ᵐ x ∂volume.restrict B.carrier,
      g i x = a x * gradient u i x + partialTest a i x * value u x :=
    fun i => MemLp.coeFn_toLp _
  let d : MultiIndex n 1 → BallL2 B := fun α =>
    if h : ∃ i, α = firstIndex i then g h.choose else v
  have dz : d (zeroIndex n 1) = v := by
    simp only [d]
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      exact (first_ne_zero i hi.symm).elim
    · rfl
  have di : ∀ i, d (firstIndex i) = g i := by
    intro i
    have h : ∃ j, firstIndex i = firstIndex j := ⟨i, rfl⟩
    simp only [d, dif_pos h]
    rw [← first_inj h.choose_spec]
  let w : IntegerSobolev B 1 := ⟨d, by
    intro α
    change IsWeakDerivative B α (d (zeroIndex n 1)) (d α)
    rw [dz]
    rcases cases_idx α with hz | ⟨i, hi⟩
    · rw [hz, dz]
      intro φ
      change (∫ x in B.carrier, v x *
        coordinateDerivative (zeroIndex n 1) (fun y => φ y) x) =
        (-1 : ℂ) ^ (zeroIndex n 1).degree *
        (∫ x in B.carrier, v x * φ x)
      rw [coordinateDerivative, zero_dirs]
      simp [coordinateDerivativeList, MultiIndex.degree, zeroIndex]
    · rw [hi, di]
      exact weak_product a u v g hv hg i⟩
  refine ⟨w, ?_, ?_⟩
  · change ∀ᵐ x ∂volume.restrict B.carrier, d (zeroIndex n 1) x = _
    rwa [dz]
  · intro i
    change ∀ᵐ x ∂volume.restrict B.carrier, d (firstIndex i) x = _
    rw [di]
    exact hg i

theorem multiply_smooth_compact {n : ℕ} (B : LocalBall n)
    (η : TestFunction B.toOpens ℝ ⊤) (u : IntegerSobolev B 1) :
    ∃ w : IntegerSobolev B 1,
      (∀ᵐ x ∂volume.restrict B.carrier,
        value w x = (η x : ℂ) ^ 2 * value u x) ∧
      ∀ i : Fin n, ∀ᵐ x ∂volume.restrict B.carrier,
        gradient w i x = (η x : ℂ) ^ 2 * gradient u i x +
          (2 * (η x : ℂ) *
            coordinateDerivativeList [i] (fun y => (η y : ℂ)) x) * value u x := by
  let a : TestFunction B.toOpens ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM η
  obtain ⟨w, hv, hg⟩ := multiply_test (productTest a a) u
  refine ⟨w, ?_, ?_⟩
  · simpa only [productTest, TestFunction.coe_mk, a,
      TestFunction.postcompCLM_apply, Function.comp_apply, Complex.ofRealCLM_apply,
      pow_two] using hv
  · intro i
    filter_upwards [hg i] with x hx
    rw [partialTest_eq, product_deriv] at hx
    simp only [productTest, TestFunction.coe_mk, a,
      TestFunction.postcompCLM_apply, Function.comp_apply, Complex.ofRealCLM_apply,
      partialTest_eq, pow_two] at hx
    rw [hx]
    ring
end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates

end
