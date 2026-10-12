module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.DivergenceForm.WeakSolutions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.WeakJets.Raw
open MeasureTheory KPContLocalNorm
open scoped Topology

abbrev Counts (n : ℕ) := Fin n → ℕ
def counts {n k : ℕ} (α : MultiIndex n k) : Counts n := fun i => (α.val i).val
def indexOfCounts {n k : ℕ} (γ : Counts n) (hγ : (∑ i, γ i) ≤ k) : MultiIndex n k :=
  ⟨fun i => ⟨γ i, by
      have hi : γ i ≤ ∑ j, γ j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (γ j)) (Finset.mem_univ i)
      omega⟩, hγ⟩
def jet {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k)
    (γ : Counts n) : BallL2 B :=
  if hγ : (∑ i, γ i) ≤ k then u.derivatives (indexOfCounts γ hγ) else 0
def coefficientJet {n : ℕ} (γ : Counts n) (f : Space n → ℂ) : Space n → ℂ :=
  coordinateDerivativeList ((List.finRange n).flatMap (fun i => List.replicate (γ i) i)) f
def unitCount {n : ℕ} (i : Fin n) : Counts n := fun j => if j = i then 1 else 0
def multiChoose {n k : ℕ} (α β : MultiIndex n k) : ℕ :=
  ∏ i, Nat.choose (counts α i) (counts β i)

 theorem list_tsupport_subset {n : ℕ} (l : List (Fin n))
    (f : Space n → ℂ) : tsupport (coordinateDerivativeList l f) ⊆ tsupport f := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih =>
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

 theorem list_smooth {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem list_perm {n : ℕ} {l k : List (Fin n)} (hp : l.Perm k)
    {f : Space n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivativeList l f = coordinateDerivativeList k f := by
  induction hp with
  | nil => rfl
  | cons i hp ih => simp only [coordinateDerivativeList, ih]
  | swap i j l =>
    have hs := list_smooth l hf
    funext x
    simp only [coordinateDerivativeList]
    have hd : Differentiable ℝ (fderiv ℝ (coordinateDerivativeList l f)) :=
      (hs.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by norm_num)
    simpa [fderiv_clm_apply (hd x) (differentiableAt_const _)] using
      (hs.contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)).eq
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  | trans hp hq ih ij => exact ih.trans ij

private theorem list_append {n : ℕ} (l k : List (Fin n)) (f : Space n → ℂ) :
    coordinateDerivativeList (l ++ k) f =
      coordinateDerivativeList l (coordinateDerivativeList k f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, coordinateDerivativeList, ih]

private theorem directions_count {n k : ℕ} (α : MultiIndex n k) (i : Fin n) :
    α.directions.count i = counts α i := by
  rw [MultiIndex.directions, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [Function.comp_def, List.count_replicate, counts]

private theorem counts_index {n k : ℕ} (γ : Counts n) (hγ : (∑ i, γ i) ≤ k) :
    counts (indexOfCounts γ hγ) = γ := rfl

private theorem degree_index {n k : ℕ} (γ : Counts n) (hγ : (∑ i, γ i) ≤ k) :
    (indexOfCounts γ hγ).degree = ∑ i, γ i := rfl

private theorem coordinate_add {n a b k : ℕ} (α : MultiIndex n a) (β : MultiIndex n b)
    (hab : (∑ i, (counts α + counts β) i) ≤ k) {f : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivative α (coordinateDerivative β f) =
      coordinateDerivative (indexOfCounts (counts α + counts β) hab) f := by
  rw [coordinateDerivative, coordinateDerivative, ← list_append]
  apply list_perm _ hf
  apply List.perm_iff_count.mpr
  intro i
  simp only [List.count_append, directions_count, counts_index, Pi.add_apply]

 def derivativeTest {n k : ℕ} {B : LocalBall n} (α : MultiIndex n k)
    (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  ⟨coordinateDerivative α (fun y => φ y), list_smooth _ φ.contDiff,
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      (list_tsupport_subset _ _),
    (list_tsupport_subset _ _).trans φ.tsupport_subset⟩

 theorem jet_weak_derivative {n k a b : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n a) (β : MultiIndex n b)
    (ha : (∑ i, counts α i) ≤ k)
    (hab : (∑ i, (counts α + counts β) i) ≤ k) :
    IsWeakDerivative B β (jet u (counts α)) (jet u (counts α + counts β)) := by
  intro φ
  let A := indexOfCounts (counts α) ha
  let AB := indexOfCounts (counts α + counts β) hab
  have h₁ := u.weak_derivatives A (derivativeTest β φ)
  have h₂ := u.weak_derivatives AB φ
  have hcomp : coordinateDerivative A (coordinateDerivative β (fun y => φ y)) =
      coordinateDerivative AB (fun y => φ y) := by
    exact coordinate_add A β hab φ.contDiff
  change (∫ x in B.carrier, u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n k) x *
    coordinateDerivative A (coordinateDerivative β (fun y => φ y)) x) =
    (-1 : ℂ) ^ A.degree *
      (∫ x in B.carrier, u.derivatives A x * coordinateDerivative β (fun y => φ y) x) at h₁
  rw [hcomp] at h₁
  change (∫ x in B.carrier, u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n k) x *
    coordinateDerivative AB (fun y => φ y) x) =
    (-1 : ℂ) ^ AB.degree * (∫ x in B.carrier, u.derivatives AB x * φ x) at h₂
  rw [h₂] at h₁
  have hdeg : AB.degree = A.degree + β.degree := by
    change (∑ i, (counts α + counts β) i) = (∑ i, counts α i) + (∑ i, counts β i)
    exact Finset.sum_add_distrib
  rw [hdeg, pow_add] at h₁
  have hne : (-1 : ℂ) ^ A.degree ≠ 0 := pow_ne_zero _ (by norm_num)
  change (∫ x in B.carrier, jet u (counts α) x * coordinateDerivative β (fun y => φ y) x) =
    (-1 : ℂ) ^ β.degree * (∫ x in B.carrier, jet u (counts α + counts β) x * φ x)
  simp only [jet, dif_pos ha, dif_pos hab]
  apply (mul_left_cancel₀ hne)
  simpa only [mul_assoc] using h₁.symm

theorem counts_zero {n k : ℕ} :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n k) = 0 := rfl

theorem counts_injective {n k : ℕ} :
    Function.Injective (counts (n := n) (k := k)) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

theorem below_zero {n r : ℕ} :
    Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ 0) =
      {KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r} := by
  classical
  ext β
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    apply counts_injective
    funext i
    exact Nat.eq_zero_of_le_zero (h i)
  · rintro rfl
    simp [counts_zero]

theorem coefficientJet_zero {n : ℕ} (f : Space n → ℂ) :
    coefficientJet (0 : Counts n) f = f := by
  have hl : (List.finRange n).flatMap (fun _ => ([] : List (Fin n))) = [] := by
    simp
  simp [coefficientJet, hl, coordinateDerivativeList]

theorem jet_index {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n k) :
    jet u (counts α) = u.derivatives α := by
  have hi : indexOfCounts (counts α) α.property = α := by
    apply counts_injective
    rfl
  have ha : (∑ i, counts α i) ≤ k := α.property
  rw [jet, dif_pos ha, hi]

theorem jet_zero {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) :
    jet u (0 : Counts n) = KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u := by
  rw [← counts_zero]
  exact jet_index u _

theorem zero_degree {n r : ℕ} :
    (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r).degree = 0 := by
  simp [MultiIndex.degree, KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex]

 theorem local_mul_smooth {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => a x * φ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (fun y => φ y)
  · exact ((ha x (φ.tsupport_subset hx)).contDiffAt (Metric.isOpen_ball.mem_nhds (φ.tsupport_subset hx))).mul φ.contDiff.contDiffAt
  · have he : (fun y => a y * φ y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport (f := fun y => φ y)).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he
 def localProductTest {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  ⟨fun x => a x * φ x, local_mul_smooth ha φ,
    φ.hasCompactSupport.mul_left, (tsupport_mul_subset_right (f := a) (g := fun x => φ x)).trans φ.tsupport_subset⟩

private theorem local_partial_smooth {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) (i : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList [i] a) B.carrier := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen Metric.isOpen_ball).mp ha).2.clm_apply contDiffOn_const

private theorem localTest_integrable {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) (v : BallL2 B) :
    Integrable (fun x => v x * (a x * φ x)) (volume.restrict B.carrier) := by
  exact (Lp.memLp v).integrable_mul ((localProductTest ha φ).continuous.memLp_of_hasCompactSupport
    (p := 2) (localProductTest ha φ).hasCompactSupport |>.restrict _)

private theorem counts_first {n : ℕ} (i : Fin n) :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i) = unitCount i := by
  classical
  funext j
  by_cases hji : j = i <;> simp [counts, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, unitCount, hji]

private theorem first_dirs {n : ℕ} (i : Fin n) : (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, apply_ite Fin.val, Fin.val_one,
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

 def firstDerivativeTest {n : ℕ} {B : LocalBall n}
    (i : Fin n) (φ : TestFunction B.toOpens ℂ ⊤) : TestFunction B.toOpens ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ
private theorem firstDerivativeTest_eq {n : ℕ} {B : LocalBall n}
    (i : Fin n) (φ : TestFunction B.toOpens ℂ ⊤) :
    (fun x => firstDerivativeTest i φ x) = coordinateDerivativeList [i] (fun x => φ x) := by
  funext x
  rw [firstDerivativeTest, TestFunction.lineDerivCLM_eq_fderivCLM]
  rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
  rfl

theorem weak_product_rule_first {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) (i : Fin n)
    (hγ : (∑ j, (γ + unitCount i) j) ≤ k)
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, a x * jet u γ x * coordinateDerivativeList [i] (fun y => φ y) x) =
      -(∫ x in B.carrier,
        (coordinateDerivativeList [i] a x * jet u γ x +
          a x * jet u (γ + unitCount i) x) * φ x) := by
  have hbase : (∑ j, γ j) ≤ k := (Finset.sum_le_sum (fun j _ => Nat.le_add_right _ _)).trans hγ
  let A := indexOfCounts γ hbase
  have hA : counts A = γ := rfl
  have hw := jet_weak_derivative u A (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i)
    hbase (by simpa only [counts_first, hA] using hγ) (localProductTest ha φ)
  have hdeg : (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i).degree = 1 := by
    simp only [MultiIndex.degree, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp
  simp only [hA, counts_first, coordinateDerivative, first_dirs, hdeg, pow_one] at hw
  have hd (x : Space n) (hx : x ∈ B.carrier) :
      coordinateDerivativeList [i] (fun y => localProductTest ha φ y) x =
        coordinateDerivativeList [i] a x * φ x +
          a x * coordinateDerivativeList [i] (fun y => φ y) x := by
    change (fderiv ℝ (fun y => a y * φ y) x) (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul (((ha x hx).contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (φ.contDiff.differentiable (by simp)).differentiableAt]
    simp only [coordinateDerivativeList, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hexpand : (∫ x in B.carrier, jet u γ x *
      coordinateDerivativeList [i] (fun y => localProductTest ha φ y) x) =
      (∫ x in B.carrier, jet u γ x * (coordinateDerivativeList [i] a x * φ x)) +
        (∫ x in B.carrier, jet u γ x * (a x * coordinateDerivativeList [i] (fun y => φ y) x)) := by
    have h2 := localTest_integrable ha (firstDerivativeTest i φ) (jet u γ)
    simp only [firstDerivativeTest_eq] at h2
    rw [← integral_add (localTest_integrable (local_partial_smooth ha i) φ _) h2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [hd x hx]
    ring
  rw [hexpand] at hw
  have hleft : (∫ x in B.carrier, a x * jet u γ x * coordinateDerivativeList [i] (fun y => φ y) x) =
      ∫ x in B.carrier, jet u γ x * (a x * coordinateDerivativeList [i] (fun y => φ y) x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hright : (∫ x in B.carrier,
      (coordinateDerivativeList [i] a x * jet u γ x + a x * jet u (γ + unitCount i) x) * φ x) =
      (∫ x in B.carrier, jet u γ x * (coordinateDerivativeList [i] a x * φ x)) +
        (∫ x in B.carrier, jet u (γ + unitCount i) x * (a x * φ x)) := by
    rw [← integral_add (localTest_integrable (local_partial_smooth ha i) φ _)
      (localTest_integrable ha φ _)]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  change _ = -1 * (∫ x in B.carrier, jet u (γ + unitCount i) x * (a x * φ x)) at hw
  rw [hleft, hright]
  linear_combination hw

private theorem l2_test_unique {n : ℕ} {B : LocalBall n} (v w : BallL2 B)
    (heq : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      (∫ x in B.carrier, v x * φ x) = ∫ x in B.carrier, w x * φ x) : v = w := by
  have hl := ((Lp.memLp v).sub (Lp.memLp w)).locallyIntegrable (by norm_num)
  have h := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict B.carrier) (f := fun x => v x - w x)
    (hl.locallyIntegrableOn B.carrier)
  have ht : ∀ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ B.carrier → (∫ x in B.carrier, g x • (v x - w x)) = 0 := by
    intro g hg hgc hgs
    have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have hsupp : tsupport (fun x => (g x : ℂ)) = tsupport g := by
      unfold tsupport
      congr 1
      ext x
      simp
    let φ : TestFunction B.toOpens ℂ ⊤ :=
      ⟨fun x => (g x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hgc,
        fun x hx => hgs (hsupp ▸ hx)⟩
    have hv : Integrable (fun x => v x * φ x) (volume.restrict B.carrier) :=
      (Lp.memLp v).integrable_mul (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport |>.restrict _)
    have hw : Integrable (fun x => w x * φ x) (volume.restrict B.carrier) :=
      (Lp.memLp w).integrable_mul (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport |>.restrict _)
    change (∫ x in B.carrier, g x • (v x - w x)) = 0
    simp only [Complex.real_smul]
    have he : (fun x => (g x : ℂ) * (v x - w x)) =
        (fun x => v x * φ x - w x * φ x) := by
      funext x
      change (g x : ℂ) * (v x - w x) = v x * (g x : ℂ) - w x * (g x : ℂ)
      ring
    rw [he, integral_sub hv hw, sub_eq_zero]
    exact heq φ
  apply Lp.ext
  filter_upwards [h ht, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  exact sub_eq_zero.mp (hx hxB)

theorem jet_unique_of_represents {n k l a : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (v : IntegerSobolev B l)
    (huv : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value v x)) (α : MultiIndex n a)
    (hk : (∑ i, counts α i) ≤ k) (hl : (∑ i, counts α i) ≤ l) :
    jet u (counts α) = jet v (counts α) := by
  apply l2_test_unique
  intro φ
  have h₁ := u.weak_derivatives (indexOfCounts (counts α) hk) φ
  have h₂ := v.weak_derivatives (indexOfCounts (counts α) hl) φ
  have hd : coordinateDerivative (indexOfCounts (counts α) hk) (fun y => φ y) =
      coordinateDerivative (indexOfCounts (counts α) hl) (fun y => φ y) := rfl
  change (∫ x in B.carrier, KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u x * coordinateDerivative _ (fun y => φ y) x) =
    (-1 : ℂ) ^ _ * (∫ x in B.carrier, u.derivatives _ x * φ x) at h₁
  change (∫ x in B.carrier, KPContLocalEnergy.SobolevEnergyEstimates.Raw.value v x * coordinateDerivative _ (fun y => φ y) x) =
    (-1 : ℂ) ^ _ * (∫ x in B.carrier, v.derivatives _ x * φ x) at h₂
  have hi : (∫ x in B.carrier, KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u x * coordinateDerivative (indexOfCounts (counts α) hk) (fun y => φ y) x) =
      ∫ x in B.carrier, KPContLocalEnergy.SobolevEnergyEstimates.Raw.value v x * coordinateDerivative (indexOfCounts (counts α) hl) (fun y => φ y) x := by
    rw [hd]
    apply integral_congr_ae
    filter_upwards [huv] with x hx
    rw [hx]
  rw [h₁, h₂, degree_index, degree_index] at hi
  simp only [jet, dif_pos hk, dif_pos hl]
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hi

def WeakProductRule {n : ℕ} (B : LocalBall n) (k : ℕ) : Prop :=
  ∀ (u : IntegerSobolev B k) (γ : Counts n) (r : ℕ) (α : MultiIndex n r),
    (∑ i, (γ + counts α) i) ≤ k →
    ∀ (a : Space n → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier →
    ∀ (φ : TestFunction B.toOpens ℂ ⊤),
    (∫ x in B.carrier, a x * jet u γ x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree *
        (∫ x in B.carrier,
          (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r =>
              ∀ i, counts β i ≤ counts α i),
            (multiChoose α β : ℂ) * coefficientJet (counts β) a x *
              jet u (γ + counts α - counts β) x) * φ x)

theorem weak_product_rule_zero_degree {n k r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) (α : MultiIndex n r)
    (hα : α.degree = 0) (a : Space n → ℂ)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, a x * jet u γ x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree *
        (∫ x in B.carrier,
          (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r =>
              ∀ i, counts β i ≤ counts α i),
            (multiChoose α β : ℂ) * coefficientJet (counts β) a x *
              jet u (γ + counts α - counts β) x) * φ x) := by
  have hz : counts α = 0 := by
    funext i
    have hi : counts α i ≤ ∑ j, counts α j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (counts α j)) (Finset.mem_univ i)
    change counts α i = 0
    change (∑ j, counts α j) = 0 at hα
    omega
  have hidx : α = KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r :=
    counts_injective (hz.trans counts_zero.symm)
  subst α
  classical
  have hb : Finset.univ.filter (fun β : MultiIndex n r =>
      ∀ i, counts β i ≤ counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) i) =
      {KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r} := below_zero
  rw [hb]
  simp only [Finset.sum_singleton, zero_degree, pow_zero, one_mul,
    multiChoose, counts_zero, Pi.zero_apply, Nat.choose_zero_right, Finset.prod_const_one,
    Nat.cast_one, coefficientJet_zero, add_zero, sub_zero]
  have hd : coordinateDerivative (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r)
      (fun y => φ y) = fun y => φ y := by
    change coefficientJet (0 : Counts n) (fun y => φ y) = fun y => φ y
    exact coefficientJet_zero _
  have hs : γ - 0 = γ := by funext i; exact Nat.sub_zero _
  rw [hd, hs]

theorem coordinateDerivativeList_smooth_on {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l a) B.carrier := by
  induction l with
  | nil => exact ha
  | cons i l ih => exact local_partial_smooth ih i

theorem coordinateDerivativeList_congr_on {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) {a b : Space n → ℂ} (hab : Set.EqOn a b B.carrier) :
    Set.EqOn (coordinateDerivativeList l a) (coordinateDerivativeList l b) B.carrier := by
  induction l with
  | nil => exact hab
  | cons i l ih =>
      intro x hx
      change fderiv ℝ (coordinateDerivativeList l a) x (EuclideanSpace.single i 1) =
        fderiv ℝ (coordinateDerivativeList l b) x (EuclideanSpace.single i 1)
      have he : coordinateDerivativeList l a =ᶠ[𝓝 x] coordinateDerivativeList l b :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) ih
      rw [he.fderiv_eq]

theorem coordinateDerivativeList_perm_on {n : ℕ} {B : LocalBall n}
    {l k : List (Fin n)} (hp : l.Perm k) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    Set.EqOn (coordinateDerivativeList l a) (coordinateDerivativeList k a) B.carrier := by
  induction hp with
  | nil => intro x hx; rfl
  | cons i hp ih => exact coordinateDerivativeList_congr_on [i] ih
  | swap i j l =>
      have hs := coordinateDerivativeList_smooth_on l ha
      intro x hx
      simp only [coordinateDerivativeList]
      have ht := (hs x hx).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
      have hd : DifferentiableAt ℝ (fderiv ℝ (coordinateDerivativeList l a)) x :=
        (ht.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by norm_num)
      simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
        (ht.isSymmSndFDerivAt (by simp)).eq
          (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  | trans hp hq ih ij => exact ih.trans ij

theorem coefficientJet_smooth_on {n : ℕ} {B : LocalBall n}
    (γ : Counts n) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coefficientJet γ a) B.carrier :=
  coordinateDerivativeList_smooth_on _ ha

theorem jet_localTest_integrable {n : ℕ} {B : LocalBall n}
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) (v : BallL2 B) :
    Integrable (fun x => a x * v x * φ x) (volume.restrict B.carrier) := by
  simpa only [mul_assoc, mul_comm (a _) (v _)] using localTest_integrable ha φ v

theorem smooth_jet_test_integrable {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => a x * jet u γ x * φ x) (volume.restrict B.carrier) := by
  simpa only [mul_assoc, mul_comm (a _) (jet u γ _)] using
    localTest_integrable ha φ (jet u γ)

def coordinateDerivativeTest {n r : ℕ} {B : LocalBall n}
    (α : MultiIndex n r) (φ : TestFunction B.toOpens ℂ ⊤) :
    TestFunction B.toOpens ℂ ⊤ := derivativeTest α φ

@[simp] theorem coordinateDerivativeTest_apply {n r : ℕ} {B : LocalBall n}
    (α : MultiIndex n r) (φ : TestFunction B.toOpens ℂ ⊤) (x : Space n) :
    coordinateDerivativeTest α φ x = coordinateDerivative α (fun y => φ y) x := rfl

def conjugateTest {n : ℕ} {B : LocalBall n} (φ : TestFunction B.toOpens ℂ ⊤) :
    TestFunction B.toOpens ℂ ⊤ := by
  have hs : tsupport (fun x => star (φ x)) = tsupport (fun x => φ x) := by
    unfold tsupport
    congr 1
    ext x
    simp
  exact ⟨fun x => star (φ x), (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp φ.contDiff,
    by change IsCompact _; rw [hs]; exact φ.hasCompactSupport,
    hs ▸ φ.tsupport_subset⟩

@[simp] theorem conjugateTest_apply {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (x : Space n) : conjugateTest φ x = star (φ x) := rfl

theorem coordinateDerivative_comm_first {n r : ℕ} (α : MultiIndex n r)
    (i : Fin n) {f : Space n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivative α (coordinateDerivativeList [i] f) =
      coordinateDerivativeList [i] (coordinateDerivative α f) := by
  simp only [coordinateDerivative, ← list_append]
  exact list_perm List.perm_append_comm hf

def directionCounts {n : ℕ} (l : List (Fin n)) : Counts n := fun i => l.count i

@[simp] theorem directionCounts_nil {n : ℕ} : directionCounts ([] : List (Fin n)) = 0 := rfl

theorem directionCounts_cons {n : ℕ} (i : Fin n) (l : List (Fin n)) :
    directionCounts (i :: l) = unitCount i + directionCounts l := by
  classical
  funext j
  simp only [directionCounts, List.count_cons, Pi.add_apply, unitCount]
  by_cases h : j = i
  · subst j; simp only [beq_self_eq_true, ite_true]; omega
  · simp only [h, if_false, beq_iff_eq, Ne.symm h, ite_false, add_zero, zero_add]

theorem directionCounts_directions {n r : ℕ} (α : MultiIndex n r) :
    directionCounts α.directions = counts α := by
  funext i
  exact directions_count α i

private theorem coefficientDirections_counts {n : ℕ} (γ : Counts n) (i : Fin n) :
    ((List.finRange n).flatMap (fun j => List.replicate (γ j) j)).count i = γ i := by
  rw [List.count_flatMap, ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [Function.comp_def, List.count_replicate]

theorem coefficientJet_eq_list_on {n : ℕ} {B : LocalBall n}
    (l : List (Fin n)) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    Set.EqOn (coefficientJet (directionCounts l) a) (coordinateDerivativeList l a) B.carrier := by
  apply coordinateDerivativeList_perm_on _ ha
  apply List.perm_iff_count.mpr
  intro i
  rw [coefficientDirections_counts]
  rfl

theorem coefficientJet_add_unit_on {n : ℕ} {B : LocalBall n}
    (γ : Counts n) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    Set.EqOn (coefficientJet (γ + unitCount i) a)
      (coordinateDerivativeList [i] (coefficientJet γ a)) B.carrier := by
  simp only [coefficientJet, ← list_append, List.singleton_append]
  apply coordinateDerivativeList_perm_on _ ha
  apply List.perm_iff_count.mpr
  intro j
  rw [coefficientDirections_counts, List.count_cons, coefficientDirections_counts]
  simp only [Pi.add_apply, unitCount, beq_iff_eq]
  by_cases h : j = i
  · subst j; simp
  · simp [h, Ne.symm h]

theorem coefficientJet_partial_on {n : ℕ} {B : LocalBall n}
    (γ : Counts n) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) :
    Set.EqOn (coefficientJet γ (coordinateDerivativeList [i] a))
      (coefficientJet (γ + unitCount i) a) B.carrier := by
  rw [coefficientJet, ← list_append]
  apply coordinateDerivativeList_perm_on _ ha
  apply List.perm_iff_count.mpr
  intro j
  rw [List.count_append, coefficientDirections_counts, coefficientDirections_counts]
  simp only [List.count_cons, List.count_nil, zero_add, Pi.add_apply, unitCount, beq_iff_eq]
  by_cases h : j = i
  · subst j; simp
  · simp [h, Ne.symm h]

def productExpansion {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) :
    List (Fin n) → (Space n → ℂ) → Counts n → Space n → ℂ
  | [], a, γ => fun x => a x * jet u γ x
  | i :: l, a, γ => fun x =>
      productExpansion u l (coordinateDerivativeList [i] a) γ x +
        productExpansion u l a (γ + unitCount i) x

theorem productExpansion_integrable {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (l : List (Fin n)) (γ : Counts n)
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => productExpansion u l a γ x * φ x) (volume.restrict B.carrier) := by
  induction l generalizing a γ with
  | nil =>
      simpa only [productExpansion, mul_assoc, mul_comm (a _) (jet u γ _)] using
        localTest_integrable ha φ (jet u γ)
  | cons i l ih =>
      simp only [productExpansion, add_mul]
      exact (ih γ (local_partial_smooth ha i)).add (ih (γ + unitCount i) ha)

theorem weak_product_rule_list {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (l : List (Fin n)) (γ : Counts n)
    (hγ : (∑ j, (γ + directionCounts l) j) ≤ k)
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, a x * jet u γ x * coordinateDerivativeList l (fun y => φ y) x) =
      (-1 : ℂ) ^ l.length * (∫ x in B.carrier, productExpansion u l a γ x * φ x) := by
  induction l generalizing a γ φ with
  | nil => simp only [coordinateDerivativeList, productExpansion, List.length_nil, pow_zero, one_mul]
  | cons i l ih =>
      have hbase : (∑ j, (γ + unitCount i) j) ≤ k := by
        apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hγ
        rw [directionCounts_cons]
        change γ j + unitCount i j ≤ γ j + (unitCount i j + directionCounts l j)
        omega
      have hleft : (∑ j, (γ + directionCounts l) j) ≤ k := by
        apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hγ
        rw [directionCounts_cons]
        change γ j + directionCounts l j ≤ γ j + (unitCount i j + directionCounts l j)
        omega
      have hright : (∑ j, (γ + unitCount i + directionCounts l) j) ≤ k := by
        simpa only [directionCounts_cons, add_assoc] using hγ
      let ψ : TestFunction B.toOpens ℂ ⊤ :=
        ⟨coordinateDerivativeList l (fun y => φ y), list_smooth l φ.contDiff,
          φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (list_tsupport_subset l _),
          (list_tsupport_subset l _).trans φ.tsupport_subset⟩
      have hfirst := weak_product_rule_first u γ i hbase ha ψ
      have hl := ih γ hleft (local_partial_smooth ha i) φ
      have hr := ih (γ + unitCount i) hright ha φ
      have he : (∫ x in B.carrier,
          (coordinateDerivativeList [i] a x * jet u γ x + a x * jet u (γ + unitCount i) x) * ψ x) =
          (∫ x in B.carrier, coordinateDerivativeList [i] a x * jet u γ x *
            coordinateDerivativeList l (fun y => φ y) x) +
          (∫ x in B.carrier, a x * jet u (γ + unitCount i) x *
            coordinateDerivativeList l (fun y => φ y) x) := by
        rw [show (fun x => (coordinateDerivativeList [i] a x * jet u γ x +
          a x * jet u (γ + unitCount i) x) * ψ x) =
            (fun x => coordinateDerivativeList [i] a x * jet u γ x * ψ x +
              a x * jet u (γ + unitCount i) x * ψ x) by funext x; ring]
        apply integral_add
        · simpa only [mul_assoc, mul_comm (coordinateDerivativeList [i] a _) (jet u γ _)] using
            localTest_integrable (local_partial_smooth ha i) ψ (jet u γ)
        · simpa only [mul_assoc, mul_comm (a _) (jet u (γ + unitCount i) _)] using
            localTest_integrable ha ψ (jet u (γ + unitCount i))
      have hout : (∫ x in B.carrier, productExpansion u (i :: l) a γ x * φ x) =
          (∫ x in B.carrier, productExpansion u l (coordinateDerivativeList [i] a) γ x * φ x) +
          (∫ x in B.carrier, productExpansion u l a (γ + unitCount i) x * φ x) := by
        simp only [productExpansion, add_mul]
        exact integral_add (productExpansion_integrable u l γ (local_partial_smooth ha i) φ)
          (productExpansion_integrable u l (γ + unitCount i) ha φ)
      change (∫ x in B.carrier, a x * jet u γ x * coordinateDerivativeList (i :: l) (fun y => φ y) x) = _ at hfirst
      rw [he, hl, hr] at hfirst
      rw [hout, List.length_cons, pow_succ]
      linear_combination hfirst

theorem weak_product_rule_uncollected {n k r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) (α : MultiIndex n r)
    (hγ : (∑ j, (γ + counts α) j) ≤ k)
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, a x * jet u γ x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree *
        (∫ x in B.carrier, productExpansion u α.directions a γ x * φ x) := by
  have hlen : α.directions.length = α.degree := by
    simp only [MultiIndex.directions, MultiIndex.degree, List.length_flatMap, List.map_map,
      List.length_replicate, Function.comp_def]
    simp [List.finRange, List.map_ofFn, List.sum_ofFn]
  simpa only [directionCounts_directions, hlen, coordinateDerivative] using
    weak_product_rule_list u α.directions γ (directionCounts_directions α ▸ hγ) ha φ

def countsChoose {n : ℕ} (δ β : Counts n) : ℕ := ∏ i, Nat.choose (δ i) (β i)

theorem countsChoose_eq_multiChoose {n r : ℕ} (α β : MultiIndex n r) :
    countsChoose (counts α) (counts β) = multiChoose α β := rfl

theorem countsChoose_zero_right {n : ℕ} (δ : Counts n) : countsChoose δ 0 = 1 := by
  simp [countsChoose]

theorem countsChoose_eq_zero {n : ℕ} {δ β : Counts n} (h : ¬ ∀ i, β i ≤ δ i) :
    countsChoose δ β = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Nat.choose_eq_zero_of_lt (by omega)

theorem countsChoose_add_unit {n : ℕ} (δ β : Counts n) (i : Fin n) (hi : 0 < β i) :
    countsChoose (δ + unitCount i) β =
      countsChoose δ (β - unitCount i) + countsChoose δ β := by
  classical
  unfold countsChoose
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => Nat.choose (δ j) ((β - unitCount i) j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => Nat.choose (δ j) (β j)) (Finset.mem_univ i)]
  have h₁ : (∏ j ∈ Finset.univ.erase i, Nat.choose ((δ + unitCount i) j) (β j)) =
      ∏ j ∈ Finset.univ.erase i, Nat.choose (δ j) (β j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [unitCount, hji]
  have h₂ : (∏ j ∈ Finset.univ.erase i, Nat.choose (δ j) ((β - unitCount i) j)) =
      ∏ j ∈ Finset.univ.erase i, Nat.choose (δ j) (β j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [unitCount, hji]
  rw [h₁, h₂]
  simp only [Pi.add_apply, Pi.sub_apply, unitCount, if_pos rfl, ite_true]
  rw [Nat.choose_succ_left _ _ hi, add_mul]

theorem countsChoose_add_unit_zero {n : ℕ} (δ β : Counts n) (i : Fin n) (hi : β i = 0) :
    countsChoose (δ + unitCount i) β = countsChoose δ β := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [hi, unitCount]
  · simp [unitCount, hji]

def countsBox {n : ℕ} (δ : Counts n) : Finset (Counts n) :=
  Fintype.piFinset (fun i => Finset.range (δ i + 1))

@[simp] theorem mem_countsBox {n : ℕ} (δ β : Counts n) :
    β ∈ countsBox δ ↔ ∀ i, β i ≤ δ i := by
  simp [countsBox, Nat.lt_succ_iff]

theorem sum_below_countsBox {n r : ℕ} (α : MultiIndex n r) (f : Counts n → ℂ) :
    (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i),
      f (counts β)) = ∑ β ∈ countsBox (counts α), f β := by
  classical
  apply Finset.sum_bij (fun β _ => counts β)
  · intro β hβ
    exact (mem_countsBox _ _).mpr (Finset.mem_filter.mp hβ).2
  · intro β hβ β' hβ' he
    exact counts_injective he
  · intro β hβ
    have hb := (mem_countsBox _ _).mp hβ
    have hd : (∑ i, β i) ≤ r :=
      (Finset.sum_le_sum (fun i _ => hb i)).trans α.property
    exact ⟨indexOfCounts β hd, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
  · intro β hβ
    rfl

theorem countsBox_shift {n : ℕ} (δ : Counts n) (i : Fin n) (f : Counts n → ℂ) :
    (∑ β ∈ countsBox δ, f (β + unitCount i)) =
      ∑ β ∈ (countsBox (δ + unitCount i)).filter (fun β => 0 < β i), f β := by
  classical
  apply Finset.sum_bij (fun β _ => β + unitCount i)
  · intro β hβ
    have hb := (mem_countsBox _ _).mp hβ
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_countsBox _ _).mpr
      intro j
      exact Nat.add_le_add_right (hb j) _
    · simp [unitCount]
  · intro β hβ β' hβ' he
    funext j
    have hj := congrFun he j
    exact Nat.add_right_cancel hj
  · intro β hβ
    have hb := (mem_countsBox _ _).mp (Finset.mem_filter.mp hβ).1
    have hi := (Finset.mem_filter.mp hβ).2
    have hd : β - unitCount i ∈ countsBox δ := by
      apply (mem_countsBox _ _).mpr
      intro j
      have hj := hb j
      by_cases hji : j = i
      · subst j
        simp only [Pi.sub_apply, Pi.add_apply, unitCount, ite_true] at hj ⊢
        omega
      · simpa [unitCount, hji] using hj
    refine ⟨β - unitCount i, hd, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.sub_apply, Pi.add_apply, unitCount, ite_true]
      omega
    · simp [unitCount, hji]

  · intro β hβ
    rfl

theorem countsBox_pascal {n : ℕ} (δ : Counts n) (i : Fin n) (f : Counts n → ℂ) :
    (∑ β ∈ countsBox (δ + unitCount i), (countsChoose (δ + unitCount i) β : ℂ) * f β) =
      (∑ β ∈ countsBox δ, (countsChoose δ β : ℂ) * f β) +
      (∑ β ∈ countsBox δ, (countsChoose δ β : ℂ) * f (β + unitCount i)) := by
  classical
  have hs : countsBox δ ⊆ countsBox (δ + unitCount i) := by
    intro β hβ
    exact (mem_countsBox _ _).mpr (fun j => le_trans ((mem_countsBox _ _).mp hβ j) (Nat.le_add_right _ _))
  have hmain : (∑ β ∈ countsBox δ, (countsChoose δ β : ℂ) * f β) =
      ∑ β ∈ countsBox (δ + unitCount i), (countsChoose δ β : ℂ) * f β := by
    apply Finset.sum_subset hs
    intro β hβ hnot
    have hz : countsChoose δ β = 0 := countsChoose_eq_zero (by simpa only [mem_countsBox] using hnot)
    simp [hz]
  have hshift : (∑ β ∈ countsBox δ, (countsChoose δ β : ℂ) * f (β + unitCount i)) =
      ∑ β ∈ (countsBox (δ + unitCount i)).filter (fun β => 0 < β i),
        (countsChoose δ (β - unitCount i) : ℂ) * f β := by
    have he (β : Counts n) : β + unitCount i - unitCount i = β := by
      funext j
      exact Nat.add_sub_cancel _ _
    simpa only [he] using countsBox_shift δ i (fun β => (countsChoose δ (β - unitCount i) : ℂ) * f β)
  rw [hmain, hshift, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro β hβ
  by_cases hi : 0 < β i
  · rw [if_pos hi, countsChoose_add_unit δ β i hi, Nat.cast_add]
    ring
  · rw [if_neg hi, countsChoose_add_unit_zero δ β i (by omega), add_zero]

theorem productExpansion_countsBox {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (l : List (Fin n)) (γ : Counts n) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) (x : Space n) (hx : x ∈ B.carrier) :
    productExpansion u l a γ x =
      ∑ β ∈ countsBox (directionCounts l), (countsChoose (directionCounts l) β : ℂ) *
        coefficientJet β a x * jet u (γ + directionCounts l - β) x := by
  classical
  induction l generalizing a γ with
  | nil =>
    have hz : countsBox (0 : Counts n) = {0} := by
      ext β
      simp only [mem_countsBox, Pi.zero_apply, Nat.le_zero, Finset.mem_singleton]
      exact ⟨fun h => funext h, fun h j => congrFun h j⟩
    simp only [directionCounts_nil, hz, Finset.sum_singleton, countsChoose_zero_right,
      Nat.cast_one, one_mul, coefficientJet_zero, add_zero, sub_zero, productExpansion]
    have he : γ - 0 = γ := by funext j; exact Nat.sub_zero _
    rw [he]
  | cons i l ih =>
    let δ := directionCounts l
    have hp : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList [i] a) B.carrier :=
      coordinateDerivativeList_smooth_on [i] ha
    simp only [productExpansion]
    rw [ih γ hp, ih (γ + unitCount i) ha, directionCounts_cons]
    have hd : unitCount i + directionCounts l = δ + unitCount i := add_comm _ _
    rw [hd]
    rw [show (∑ β ∈ countsBox (δ + unitCount i), (countsChoose (δ + unitCount i) β : ℂ) *
      coefficientJet β a x * jet u (γ + (δ + unitCount i) - β) x) =
      ∑ β ∈ countsBox (δ + unitCount i), (countsChoose (δ + unitCount i) β : ℂ) *
        (coefficientJet β a x * jet u (γ + (δ + unitCount i) - β) x) by
          apply Finset.sum_congr rfl; intro β hβ; ring]
    rw [countsBox_pascal]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro β hβ
      have he : γ + unitCount i + directionCounts l - β = γ + (δ + unitCount i) - β := by
        funext j
        change γ j + unitCount i j + δ j - β j = γ j + (δ j + unitCount i j) - β j
        omega
      rw [he]
      ring
    · apply Finset.sum_congr rfl
      intro β hβ
      have he : γ + directionCounts l - β = γ + (δ + unitCount i) - (β + unitCount i) := by
        funext j
        change γ j + δ j - β j = γ j + (δ j + unitCount i j) - (β j + unitCount i j)
        omega
      rw [he, coefficientJet_partial_on β i ha hx]
      ring

theorem weak_product_rule {n k : ℕ} (B : LocalBall n) : WeakProductRule B k := by
  classical
  intro u γ r α hγ a ha φ
  rw [weak_product_rule_uncollected u γ α hγ ha φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  rw [productExpansion_countsBox u α.directions γ ha x hx,
    directionCounts_directions]
  simp only [← countsChoose_eq_multiChoose]
  rw [sum_below_countsBox α (fun β => (countsChoose (counts α) β : ℂ) *
    coefficientJet β a x * jet u (γ + counts α - β) x)]

end DedekindZetaZeroFree.WeakJets.Raw

end
