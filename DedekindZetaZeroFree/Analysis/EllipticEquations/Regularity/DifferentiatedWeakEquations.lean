module

public import DedekindZetaZeroFree.Analysis.Sobolev.Restriction.BallNormMonotonicity
public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.MultiIndexCommutatorPairing

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

open MeasureTheory KPContLocalNorm
namespace Raw
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

def SmoothNearClosedBall {n : ℕ} {outer : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients outer cρ Cρ κ Λ) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧
    Metric.closedBall outer.center outer.radius ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) D.density U ∧
    ∀ i j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => D.matrix x i j) U

def BoundedCoefficientDerivatives {n : ℕ} {outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (k : ℕ) (L : ℝ) : Prop :=
  ∀ α : MultiIndex n k, ∀ x ∈ outer.carrier,
    ‖coordinateDerivative α (fun y => (D.density y : ℂ)) x‖ ≤ L ∧
    ∀ i j : Fin n,
      ‖coordinateDerivative α
        (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x‖ ≤ L

def functionSobolevNorm {n : ℕ} (B : LocalBall n) (r : ℕ)
    (h : Space n → ℂ) : ℝ :=
  Real.sqrt (∑ α : MultiIndex n r, (functionL2Norm B (coordinateDerivative α h)) ^ 2)

def WeakIntegerEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (r : ℕ) (M C : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ M →
    ∀ (u : IntegerSobolev outer 1) (h : IntegerSobolev outer r),
      WeakEquation D z u (value h) →
      ∃ v : IntegerSobolev inner (r + 2),
        Represents v (fun x => value u x) ∧
        v.sobolevNorm ≤ C * (‖value u‖ + h.sobolevNorm)

def SmoothSourceIntegerEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (r : ℕ) (M C : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ M →
    ∀ (u : IntegerSobolev outer 1) (h : Space n → ℂ)
      (U : Set (Space n)), IsOpen U →
      Metric.closedBall outer.center outer.radius ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) h U →
      ∀ hL2 : MemLp h 2 (volume.restrict outer.carrier),
        WeakEquation D z u (hL2.toLp h) →
        ∃ v : IntegerSobolev inner (r + 2),
          Represents v (fun x => value u x) ∧
          v.sobolevNorm ≤ C * (‖value u‖ + functionSobolevNorm outer r h)

def SmoothIntegerEstimate {n : ℕ} (inner outer : LocalBall n)
    {cρ Cρ κ Λ : ℝ} (D : Coefficients outer cρ Cρ κ Λ)
    (r : ℕ) (M C : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ M →
    ∀ (u h : Space n → ℂ) (U : Set (Space n)), IsOpen U →
      Metric.closedBall outer.center outer.radius ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) u U → ContDiffOn ℝ (⊤ : ℕ∞) h U →
      (∀ᵐ x ∂volume.restrict outer.carrier,
        divergenceOperator D u x - z * u x = h x) →
      ∃ v : IntegerSobolev inner (r + 2),
        RepresentsClassicalDerivatives v u ∧
        v.sobolevNorm ≤ C * (functionL2Norm outer u + functionSobolevNorm outer r h)
end Raw

def restrictCoefficients {n : ℕ} {inner outer : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (hsub : inner.carrier ⊆ outer.carrier)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ) :
    KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients inner cρ Cρ κ Λ where
  density := D.density
  matrix := D.matrix
  density_smooth := D.density_smooth.mono hsub
  matrix_smooth i j := (D.matrix_smooth i j).mono hsub
  density_bounds x hx := D.density_bounds x (hsub hx)
  symmetric x hx := D.symmetric x (hsub hx)
  ellipticity x hx := D.ellipticity x (hsub hx)
  upper_bound x hx := D.upper_bound x (hsub hx)

open KPContLocalEnergy
open KPContLocalEnergy.SobolevEnergyEstimates.Raw hiding gradient value

theorem restrict_weak_equation {n : ℕ} {inner outer : LocalBall n}
    {cρ Cρ κ Λ : ℝ} (hsub : inner.carrier ⊆ outer.carrier)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients outer cρ Cρ κ Λ)
    (z : ℂ) (u : IntegerSobolev outer 1) (h : BallL2 outer)
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u h) :
    ∃ (v : IntegerSobolev inner 1) (g : BallL2 inner),
      (∀ α : MultiIndex n 1, ∀ᵐ x ∂volume.restrict inner.carrier,
        v.derivatives α x = u.derivatives α x) ∧
      (∀ᵐ x ∂volume.restrict inner.carrier, g x = h x) ∧
      v.sobolevNorm ≤ u.sobolevNorm ∧ ‖g‖ ≤ ‖h‖ ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation (restrictCoefficients hsub D) z v g := by
  refine ⟨restrictSobolev hsub u, restrictBallL2 hsub h,
    (fun α => restrictBallL2_ae hsub _), restrictBallL2_ae hsub h,
    sobolevNorm_restrictSobolev_le hsub u, norm_restrictBallL2_le hsub h, ?_⟩
  intro φ
  let ψ : TestFunction outer.toOpens ℂ ⊤ :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hsub⟩
  have heqOuter := heq ψ
  have hgrad : ∀ᵐ x ∂volume.restrict inner.carrier,
      ∀ j, gradient (restrictSobolev hsub u) j x = gradient u j x := by
    apply ae_all_iff.mpr
    intro j
    exact restrictBallL2_ae hsub _
  have hv := restrictSobolev_represents hsub u
  have hh := restrictBallL2_ae hsub h
  change (∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hsub u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in inner.carrier, (D.density x : ℂ) * value (restrictSobolev hsub u) x * star (φ x)) =
        ∫ x in inner.carrier, (D.density x : ℂ) * restrictBallL2 hsub h x * star (φ x)
  have hi : (∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient (restrictSobolev hsub u) j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      ∫ x in outer.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x) := by
    trans ∫ x in inner.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)
    · apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      simp only [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      intro x hx
      have hz : ∀ i, coordinateDerivativeList [i] (fun y => φ y) x = 0 := by
        intro i
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact hx.2 (φ.tsupport_subset (coordinateDerivativeList_tsupport_subset [i] _ hm))
      simp [hz]
  have h0 (f : BallL2 outer) :
      (∫ x in inner.carrier, (D.density x : ℂ) * restrictBallL2 hsub f x * star (φ x)) =
      ∫ x in outer.carrier, (D.density x : ℂ) * f x * star (φ x) := by
    trans ∫ x in inner.carrier, (D.density x : ℂ) * f x * star (φ x)
    · apply integral_congr_ae
      filter_upwards [restrictBallL2_ae hsub f] with x hx
      rw [hx]
    · symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx.2 (φ.tsupport_subset hm))
      simp [hz]
  rw [hi, h0 h]
  change (∫ x in outer.carrier, _) - z * (∫ x in inner.carrier,
    (D.density x : ℂ) * restrictBallL2 hsub (value u) x * star (φ x)) = _
  rw [h0 (value u)]
  exact heqOuter

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

def commutatorSource {n r : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (z : ℂ) (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
    (α : MultiIndex n r) : Space n → ℂ := by
  classical
  let below := Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i)
  let positive := below.filter (fun β => 0 < β.degree)
  let ρ : Space n → ℂ := fun x => (D.density x : ℂ)
  let b (i j : Fin n) : Space n → ℂ := fun x => ((D.density x * D.matrix x i j : ℝ) : ℂ)
  exact fun x => (ρ x)⁻¹ *
    ((∑ β ∈ below, (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x *
        jet h (counts α - counts β) x) +
     z * (∑ β ∈ positive, (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x *
        jet u (counts α - counts β) x) +
     ∑ i, ∑ j, ∑ β ∈ positive, (multiChoose α β : ℂ) *
       (coefficientJet (counts β + unitCount i) (b i j) x *
          jet u (counts α - counts β + unitCount j) x +
        coefficientJet (counts β) (b i j) x *
          jet u (counts α - counts β + unitCount i + unitCount j) x))

open KPContLocalEnergy.SobolevEnergyEstimates.Raw

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
      (KPContLocalEnergy.coordinateDerivativeList_tsupport_subset _ _),
    (KPContLocalEnergy.coordinateDerivativeList_tsupport_subset _ _).trans φ.tsupport_subset⟩

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

theorem shifted_jet_sobolev {n r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B (r + 1)) (α : MultiIndex n r) :
    ∃ w : IntegerSobolev B 1, ∀ δ : MultiIndex n 1,
      w.derivatives δ = jet u (counts α + counts δ) := by
  have hab (δ : MultiIndex n 1) : (∑ i, (counts α + counts δ) i) ≤ r + 1 := by
    simpa only [Pi.add_apply, Finset.sum_add_distrib, counts] using
      Nat.add_le_add α.property δ.property
  have ha : (∑ i, counts α i) ≤ r + 1 := α.property.trans (Nat.le_succ r)
  have hz : counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1) = 0 := rfl
  refine ⟨⟨fun δ => jet u (counts α + counts δ), ?_⟩, fun _ => rfl⟩
  intro δ
  change IsWeakDerivative B δ (jet u (counts α + counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1))) _
  rw [hz, add_zero]
  exact jet_weak_derivative u α δ ha (hab δ)

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

private theorem counts_zero {n k : ℕ} :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n k) = 0 := rfl

private theorem counts_injective {n k : ℕ} :
    Function.Injective (counts (n := n) (k := k)) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

private theorem below_zero {n r : ℕ} :
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

private theorem coefficientJet_zero {n : ℕ} (f : Space n → ℂ) :
    coefficientJet (0 : Counts n) f = f := by
  have hl : (List.finRange n).flatMap (fun _ => ([] : List (Fin n))) = [] := by
    simp
  simp [coefficientJet, hl, coordinateDerivativeList]

private theorem jet_index {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n k) :
    jet u (counts α) = u.derivatives α := by
  have hi : indexOfCounts (counts α) α.property = α := by
    apply counts_injective
    rfl
  have ha : (∑ i, counts α i) ≤ k := α.property
  rw [jet, dif_pos ha, hi]

private theorem jet_zero {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) :
    jet u (0 : Counts n) = KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u := by
  rw [← counts_zero]
  exact jet_index u _

private theorem zero_degree {n r : ℕ} :
    (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r).degree = 0 := by
  simp [MultiIndex.degree, KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex]

 theorem commutatorSource_zero {n r : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (z : ℂ) (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
    (x : Space n) (hx : x ∈ B.carrier) :
    commutatorSource D z u h (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) x =
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h x := by
  classical
  have hρ : (D.density x : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hcρ.trans_le (D.density_bounds x hx).1)
  have hp : (Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ 0)).filter
      (fun β => 0 < β.degree) = ∅ := by
    rw [below_zero]
    simp [zero_degree]
  have hb : Finset.univ.filter (fun β : MultiIndex n r => ∀ i,
      counts β i ≤ counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) i) =
      {KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r} := below_zero
  have hp' : (Finset.univ.filter (fun β : MultiIndex n r => ∀ i,
      counts β i ≤ counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) i)).filter
      (fun β => 0 < β.degree) = ∅ := hp
  simp only [commutatorSource, hp', hb, Finset.sum_empty, mul_zero,
    Finset.sum_const_zero, add_zero, Finset.sum_singleton]
  have hs : ({KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r} : Finset (MultiIndex n r)).filter
      (fun β => 0 < β.degree) = ∅ := by
    simp [zero_degree]
  rw [hs]
  simp only [Finset.sum_empty, mul_zero, Finset.sum_const_zero, add_zero,
    multiChoose, counts_zero, Pi.zero_apply, Nat.choose_zero_right,
    Finset.prod_const_one, Nat.cast_one, one_mul, coefficientJet_zero,
    sub_self, jet_zero]
  have hzero : (0 - 0 : Counts n) = 0 := by funext i; rfl
  rw [hzero, jet_zero]
  exact inv_mul_cancel_left₀ hρ _

theorem differentiated_weak_equation_zero {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1))
    (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (hg : MemLp (commutatorSource D z u h (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r))
      2 (volume.restrict B.carrier)) :
    ∃ w : IntegerSobolev B 1,
      (∀ δ : MultiIndex n 1, ∀ᵐ x ∂volume.restrict B.carrier,
        w.derivatives δ x = jet u (counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) + counts δ) x) ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z w
        (hg.toLp (commutatorSource D z u h (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r))) := by
  have hj (δ : MultiIndex n 1) : u₁.derivatives δ = jet u (counts δ) := by
    rw [← jet_index u₁ δ]
    exact (jet_unique_of_represents u u₁ hu δ
      (δ.property.trans (by omega)) δ.property).symm
  refine ⟨u₁, ?_, ?_⟩
  · intro δ
    rw [counts_zero, zero_add, ← hj δ]
    exact Filter.Eventually.of_forall (fun _ => rfl)
  · intro φ
    have hi : (∫ x in B.carrier, (D.density x : ℂ) *
        hg.toLp (commutatorSource D z u h (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r)) x * star (φ x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h x * star (φ x) := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
      rw [hx, commutatorSource_zero D hcρ z u h x hxB]
    rw [hi]
    exact heq φ

private theorem counts_first {n : ℕ} (i : Fin n) :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i) = unitCount i := by
  classical
  funext j
  by_cases hji : j = i <;> simp [counts, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, unitCount, hji]

theorem differentiated_weak_equation_of_jet_pairing {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
    (α : MultiIndex n r)
    (hg : MemLp (commutatorSource D z u h α) 2 (volume.restrict B.carrier))
    (hpair : ∀ φ : TestFunction B.toOpens ℂ ⊤,
      (∫ x in B.carrier, (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * jet u (counts α + unitCount j) x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) -
        z * (∫ x in B.carrier, (D.density x : ℂ) * jet u (counts α) x * star (φ x)) =
      ∫ x in B.carrier, (D.density x : ℂ) * commutatorSource D z u h α x * star (φ x)) :
    ∃ w : IntegerSobolev B 1,
      (∀ δ : MultiIndex n 1, ∀ᵐ x ∂volume.restrict B.carrier,
        w.derivatives δ x = jet u (counts α + counts δ) x) ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z w
        (hg.toLp (commutatorSource D z u h α)) := by
  obtain ⟨w, hw⟩ := shifted_jet_sobolev u α
  refine ⟨w, fun δ => Filter.Eventually.of_forall (fun x => congrArg (fun f : BallL2 B => f x) (hw δ)), ?_⟩
  intro φ
  have hgrad (j : Fin n) : KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient w j =
      jet u (counts α + unitCount j) := by
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient, counts_first] using
      hw (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)
  have hvalue : KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w = jet u (counts α) := by
    simpa only [KPContLocalEnergy.SobolevEnergyEstimates.Raw.value, counts_zero, add_zero] using
      hw (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n 1)
  change (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient w j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w x * star (φ x)) = _
  simp only [hgrad, hvalue]
  rw [hpair φ]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem differentiated_weak_equation {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1))
    (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (α : MultiIndex n r)
    (hg : MemLp (commutatorSource D z u h α) 2 (volume.restrict B.carrier)) :
    ∃ w : IntegerSobolev B 1,
      (∀ δ : MultiIndex n 1, ∀ᵐ x ∂volume.restrict B.carrier,
        w.derivatives δ x = jet u (counts α + counts δ) x) ∧
      KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z w
        (hg.toLp (commutatorSource D z u h α)) := by
  apply differentiated_weak_equation_of_jet_pairing D z u h α hg
  intro φ
  exact DedekindZetaZeroFree.WeakJets.Raw.differentiated_pairing
    (DedekindZetaZeroFree.WeakJets.Raw.weak_product_rule B)
    (DedekindZetaZeroFree.WeakJets.Raw.weak_product_rule B)
    D hcρ z u₁ u h hu heq α φ

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

end
