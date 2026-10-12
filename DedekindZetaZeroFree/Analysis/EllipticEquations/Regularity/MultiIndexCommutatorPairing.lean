module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.MultiIndexLeibnizRule

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.WeakJets.Raw
open MeasureTheory KPContLocalNorm
open scoped Topology

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

private theorem counts_first {n : ℕ} (i : Fin n) :
    counts (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i) = unitCount i := by
  classical
  funext j
  by_cases hji : j = i <;> simp [counts, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, unitCount, hji]

theorem coordinateDerivativeList_star {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    coordinateDerivativeList l (fun x => star (f x)) =
      fun x => star (coordinateDerivativeList l f x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      funext x
      simp only [coordinateDerivativeList, ih, fderiv_star,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

private theorem density_smooth {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (D.density x : ℂ)) B.carrier :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn D.density_smooth

private theorem flux_smooth {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ((D.density x * D.matrix x i j : ℝ) : ℂ)) B.carrier :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (D.density_smooth.mul (D.matrix_smooth i j))

theorem differentiated_pairing_shifted {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1))
    (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (α : MultiIndex n r) (φ : TestFunction B.toOpens ℂ ⊤) :
    (∑ i, ∑ j, ∫ x in B.carrier,
      ((D.density x * D.matrix x i j : ℝ) : ℂ) * jet u (unitCount j) x *
        coordinateDerivative α (coordinateDerivativeList [i] (fun y => star (φ y))) x) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * jet u 0 x *
        coordinateDerivative α (fun y => star (φ y)) x) =
      ∫ x in B.carrier, (D.density x : ℂ) * jet h 0 x *
        coordinateDerivative α (fun y => star (φ y)) x := by
  classical
  have hj (j : Fin n) : jet u (unitCount j) = KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient u₁ j := by
    rw [← counts_first]
    exact (jet_unique_of_represents u u₁ hu _ (by
      exact (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).property.trans (by omega))
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).property).trans (jet_index u₁ _)
  let ψ := coordinateDerivativeTest α φ
  have htest (i : Fin n) :
      (fun x => star (coordinateDerivativeList [i] (fun y => ψ y) x)) =
        coordinateDerivative α (coordinateDerivativeList [i] (fun y => star (φ y))) := by
    change (fun x => star (coordinateDerivativeList [i] (coordinateDerivative α (fun y => φ y)) x)) = _
    rw [← coordinateDerivative_comm_first α i φ.contDiff]
    rw [coordinateDerivative, ← coordinateDerivativeList_star α.directions,
      ← coordinateDerivativeList_star [i]]
    rfl
  have htest0 : (fun x => star (ψ x)) = coordinateDerivative α (fun y => star (φ y)) := by
    exact (coordinateDerivativeList_star α.directions (fun y => φ y)).symm
  have hw := heq ψ
  have hv : (∫ x in B.carrier, (D.density x : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x * star (ψ x)) =
      ∫ x in B.carrier, (D.density x : ℂ) * jet u 0 x * star (ψ x) := by
    rw [jet_zero]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx]
  rw [hv] at hw
  have hi (i j : Fin n) : Integrable (fun x =>
      ((D.density x * D.matrix x i j : ℝ) : ℂ) * jet u (unitCount j) x *
        star (coordinateDerivativeList [i] (fun y => ψ y) x)) (volume.restrict B.carrier) := by
    let χ : TestFunction B.toOpens ℂ ⊤ := conjugateTest
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) ψ)
    have hχ : (fun x => χ x) = fun x => star (coordinateDerivativeList [i] (fun y => ψ y) x) := by
      funext x
      simp only [χ, conjugateTest_apply]
      rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ (by simp)]
      rfl
    simpa only [hχ] using smooth_jet_test_integrable u (unitCount j) (flux_smooth D i j) χ
  have hf : (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient u₁ j x *
        star (coordinateDerivativeList [i] (fun y => ψ y) x)) =
      ∑ i, ∑ j, ∫ x in B.carrier,
        ((D.density x * D.matrix x i j : ℝ) : ℂ) * jet u (unitCount j) x *
          star (coordinateDerivativeList [i] (fun y => ψ y) x) := by
    simp only [← hj, Finset.mul_sum, ← mul_assoc, ← Complex.ofReal_mul]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finset_sum _ (fun j _ => hi i j)
  rw [hf] at hw
  have ht (i : Fin n) (x : Space n) := congrFun (htest i) x
  have ht0 (x : Space n) := congrFun htest0 x
  simpa only [ht, ht0, jet_zero] using hw

theorem differentiated_pairing_collected {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (hproduct : WeakProductRule B (r + 1)) (hproductSource : WeakProductRule B r)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (α : MultiIndex n r) (φ : TestFunction B.toOpens ℂ ⊤) :
    (∑ i, ∑ j, ∫ x in B.carrier,
      (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
        (multiChoose α β : ℂ) *
          coefficientJet (counts β) (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
          jet u (unitCount j + counts α - counts β) x) *
            star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier,
        (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
          (multiChoose α β : ℂ) * coefficientJet (counts β) (fun y => (D.density y : ℂ)) x *
            jet u (counts α - counts β) x) * star (φ x)) =
      ∫ x in B.carrier,
        (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
          (multiChoose α β : ℂ) * coefficientJet (counts β) (fun y => (D.density y : ℂ)) x *
            jet h (counts α - counts β) x) * star (φ x) := by
  classical
  have hw := differentiated_pairing_shifted D z u₁ u h hu heq α φ
  have hb (j : Fin n) : (∑ i, (unitCount j + counts α) i) ≤ r + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    have hs : (∑ i, unitCount j i) = 1 := by simp [unitCount]
    rw [hs]
    have hd : (∑ i, counts α i) ≤ r := α.property
    omega
  have hf (i j : Fin n) :
      (∫ x in B.carrier, ((D.density x * D.matrix x i j : ℝ) : ℂ) * jet u (unitCount j) x *
        coordinateDerivative α (coordinateDerivativeList [i] (fun y => star (φ y))) x) =
      (-1 : ℂ) ^ α.degree * (∫ x in B.carrier,
        (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
          (multiChoose α β : ℂ) *
            coefficientJet (counts β) (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
              jet u (unitCount j + counts α - counts β) x) *
                star (coordinateDerivativeList [i] (fun y => φ y) x)) := by
    let ψ : TestFunction B.toOpens ℂ ⊤ := conjugateTest
      (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ)
    have hψ : (fun x => ψ x) = coordinateDerivativeList [i] (fun y => star (φ y)) := by
      rw [coordinateDerivativeList_star]
      funext x
      simp only [ψ, conjugateTest_apply]
      rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ (by simp)]
      rfl
    have ht := hproduct u (unitCount j) r α (hb j) _ (flux_smooth D i j) ψ
    simpa only [hψ, coordinateDerivativeList_star] using ht
  have hd := hproduct u (0 : Counts n) r α
    (by simpa only [zero_add, counts, Nat.succ_eq_add_one] using α.property.trans (Nat.le_succ r))
    _ (density_smooth D) (conjugateTest φ)
  have hh := hproductSource h (0 : Counts n) r α
    (by simpa only [zero_add, counts] using α.property) _ (density_smooth D) (conjugateTest φ)
  simp only [conjugateTest_apply, zero_add] at hd hh
  simp_rw [hf, hd, hh] at hw
  simp only [← Finset.mul_sum] at hw
  apply mul_left_cancel₀ (pow_ne_zero α.degree (by norm_num : (-1 : ℂ) ≠ 0))
  linear_combination hw

theorem positive_flux_pairing {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (u : IntegerSobolev B (r + 1)) (α β : MultiIndex n r)
    (hβα : ∀ q, counts β q ≤ counts α q) (hβ : 0 < β.degree)
    (i j : Fin n) (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier,
      coefficientJet (counts β) (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
        jet u (counts α - counts β + unitCount j) x *
          star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      -(∫ x in B.carrier,
        (coefficientJet (counts β + unitCount i)
            (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
            jet u (counts α - counts β + unitCount j) x +
          coefficientJet (counts β) (fun y => ((D.density y * D.matrix y i j : ℝ) : ℂ)) x *
            jet u (counts α - counts β + unitCount i + unitCount j) x) * star (φ x)) := by
  classical
  have hb : (∑ q, (counts α - counts β + unitCount j + unitCount i) q) ≤ r + 1 := by
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib]
    have hi : (∑ q, unitCount i q) = 1 := by simp [unitCount]
    have hj : (∑ q, unitCount j q) = 1 := by simp [unitCount]
    rw [hi, hj, Finset.sum_tsub_distrib _ (fun q _ => hβα q)]
    have ha : (∑ q, counts α q) ≤ r := α.property
    change 0 < ∑ q, counts β q at hβ
    have hle : (∑ q, counts β q) ≤ ∑ q, counts α q := Finset.sum_le_sum (fun q _ => hβα q)
    omega
  have hs := coefficientJet_smooth_on (counts β) (flux_smooth D i j)
  have hw := weak_product_rule_first u (counts α - counts β + unitCount j) i hb hs (conjugateTest φ)
  simp only [conjugateTest_apply, coordinateDerivativeList_star] at hw
  rw [hw]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  rw [← coefficientJet_add_unit_on (counts β) i (flux_smooth D i j) hx]
  have hc : counts α - counts β + unitCount j + unitCount i =
      counts α - counts β + unitCount i + unitCount j := by ac_rfl
  rw [hc]

theorem sum_below_split_zero {n r : ℕ} (α : MultiIndex n r)
    (f : MultiIndex n r → ℂ) :
    (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i), f β) =
      f (KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r) +
        ∑ β ∈ (Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i)).filter
          (fun β => 0 < β.degree), f β := by
  classical
  let S := Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i)
  let Z := KPContLocalEnergy.SobolevEnergyEstimates.Raw.zeroIndex n r
  have hz : Z ∈ S := by simp [S, Z, counts_zero]
  have hpos : S.filter (fun β => 0 < β.degree) = S.erase Z := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_erase]
    have he : β.degree = 0 ↔ β = Z := by
      constructor
      · intro h
        apply counts_injective
        rw [counts_zero]
        funext i
        have hi : counts β i ≤ ∑ j, counts β j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        change (∑ j, counts β j) = 0 at h
        change counts β i = 0
        omega
      · rintro rfl; exact zero_degree
    have hp : 0 < β.degree ↔ β ≠ Z := by
      exact Nat.pos_iff_ne_zero.trans (not_congr he)
    rw [hp]
    exact and_comm
  rw [hpos]
  exact (Finset.add_sum_erase S f hz).symm

theorem collected_jet_integrable {n k r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n r) (γ : Counts n)
    (S : Finset (MultiIndex n r)) {a : Space n → ℂ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => (∑ β ∈ S, (multiChoose α β : ℂ) *
      coefficientJet (counts β) a x * jet u (γ + counts α - counts β) x) * φ x)
      (volume.restrict B.carrier) := by
  classical
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro β hβ
  simpa only [mul_assoc] using
    (smooth_jet_test_integrable u _ (coefficientJet_smooth_on (counts β) ha) φ).const_mul (multiChoose α β : ℂ)

theorem collected_jet_split_zero {n k r : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (α : MultiIndex n r) (γ : Counts n)
    {a : Space n → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a B.carrier)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier,
      (∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
        (multiChoose α β : ℂ) * coefficientJet (counts β) a x * jet u (γ + counts α - counts β) x) * φ x) =
      (∫ x in B.carrier, a x * jet u (γ + counts α) x * φ x) +
      (∫ x in B.carrier,
        (∑ β ∈ (Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q)).filter
          (fun β => 0 < β.degree),
          (multiChoose α β : ℂ) * coefficientJet (counts β) a x * jet u (γ + counts α - counts β) x) * φ x) := by
  classical
  simp_rw [sum_below_split_zero α]
  simp only [multiChoose, counts_zero, Pi.zero_apply,
    Nat.choose_zero_right, Finset.prod_const_one, Nat.cast_one, one_mul,
    coefficientJet_zero, sub_zero]
  simp only [add_mul]
  exact integral_add (smooth_jet_test_integrable u _ ha φ)
    (collected_jet_integrable u α γ _ ha φ)

theorem differentiated_pairing {n r : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ : ℝ}
    (hproduct : WeakProductRule B (r + 1))
    (hproductSource : WeakProductRule B r)
    (D : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Coefficients B cρ Cρ κ Λ)
    (hcρ : 0 < cρ) (z : ℂ)
    (u₁ : IntegerSobolev B 1) (u : IntegerSobolev B (r + 1))
    (h : IntegerSobolev B r)
    (hu : KPContLocalEnergy.SobolevEnergyEstimates.Raw.Represents u
      (fun x => KPContLocalEnergy.SobolevEnergyEstimates.Raw.value u₁ x))
    (heq : KPContLocalEnergy.SobolevEnergyEstimates.Raw.WeakEquation D z u₁
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.value h))
    (α : MultiIndex n r)
    (φ : TestFunction B.toOpens ℂ ⊤) :
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * jet u (counts α + unitCount j) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * jet u (counts α) x * star (φ x)) =
    ∫ x in B.carrier, (D.density x : ℂ) * commutatorSource D z u h α x * star (φ x) := by
  classical
  let S := (Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q)).filter (fun β => 0 < β.degree)
  let ρ : Space n → ℂ := fun x => (D.density x : ℂ)
  let b (i j : Fin n) : Space n → ℂ := fun x => ((D.density x * D.matrix x i j : ℝ) : ℂ)
  let F (i j : Fin n) : Space n → ℂ := fun x => ∑ β ∈ S, (multiChoose α β : ℂ) *
    (coefficientJet (counts β + unitCount i) (b i j) x * jet u (counts α - counts β + unitCount j) x +
      coefficientJet (counts β) (b i j) x * jet u (counts α - counts β + unitCount i + unitCount j) x)
  have hw := differentiated_pairing_collected hproduct hproductSource D z u₁ u h hu heq α φ
  have hs (i j : Fin n) := collected_jet_split_zero u α (unitCount j) (flux_smooth D i j)
    (conjugateTest (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ))
  have hds := collected_jet_split_zero u α 0 (density_smooth D) (conjugateTest φ)
  simp only [zero_add, conjugateTest_apply] at hds
  have htest (i : Fin n) :
      (fun x => conjugateTest (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ) x) =
        fun x => star (coordinateDerivativeList [i] (fun y => φ y) x) := by
    funext x
    simp only [conjugateTest_apply]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rfl
  simp_rw [htest] at hs
  simp_rw [hs, hds] at hw
  have hfint (i j : Fin n) : Integrable (fun x => F i j x * star (φ x)) (volume.restrict B.carrier) := by
    simp only [F, Finset.sum_mul]
    apply integrable_finsetSum
    intro β hβ
    have h₁ := smooth_jet_test_integrable u (counts α - counts β + unitCount j)
      (coefficientJet_smooth_on (counts β + unitCount i) (flux_smooth D i j)) (conjugateTest φ)
    have h₂ := smooth_jet_test_integrable u (counts α - counts β + unitCount i + unitCount j)
      (coefficientJet_smooth_on (counts β) (flux_smooth D i j)) (conjugateTest φ)
    simpa only [Pi.add_apply, mul_add, add_mul, mul_assoc, conjugateTest_apply] using
      (h₁.add h₂).const_mul (multiChoose α β : ℂ)
  have hshift (β : MultiIndex n r) (hβ : β ∈ S) (j : Fin n) :
      unitCount j + counts α - counts β = counts α - counts β + unitCount j := by
    have hbβ : ∀ q, counts β q ≤ counts α q := (Finset.mem_filter.mp (Finset.mem_filter.mp hβ).1).2
    funext q
    simp only [Pi.add_apply, Pi.sub_apply]
    have := hbβ q
    omega
  have hfp (i j : Fin n) :
      (∫ x in B.carrier, (∑ β ∈ S, (multiChoose α β : ℂ) * coefficientJet (counts β) (b i j) x *
        jet u (unitCount j + counts α - counts β) x) * star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      -(∫ x in B.carrier, F i j x * star (φ x)) := by
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ (fun β _ => by
      simpa only [mul_assoc, htest] using
        (smooth_jet_test_integrable u _ (coefficientJet_smooth_on (counts β) (flux_smooth D i j))
          (conjugateTest (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ))).const_mul (multiChoose α β : ℂ))]
    rw [show (fun x => F i j x * star (φ x)) =
      fun x => ∑ β ∈ S, (multiChoose α β : ℂ) *
        ((coefficientJet (counts β + unitCount i) (b i j) x * jet u (counts α - counts β + unitCount j) x +
          coefficientJet (counts β) (b i j) x * jet u (counts α - counts β + unitCount i + unitCount j) x) * star (φ x)) by
        funext x; simp only [F, Finset.sum_mul, mul_assoc]]
    rw [integral_finsetSum _ (fun β _ => by
      simpa only [Pi.add_apply, add_mul, conjugateTest_apply] using
        ((smooth_jet_test_integrable u (counts α - counts β + unitCount j)
        (coefficientJet_smooth_on (counts β + unitCount i) (flux_smooth D i j)) (conjugateTest φ)).add
        (smooth_jet_test_integrable u (counts α - counts β + unitCount i + unitCount j) (coefficientJet_smooth_on (counts β) (flux_smooth D i j)) (conjugateTest φ))).const_mul (multiChoose α β : ℂ))]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro β hβ
    simp only [mul_assoc, integral_const_mul]
    rw [hshift β hβ j]
    have hbβ := (Finset.mem_filter.mp (Finset.mem_filter.mp hβ).1).2
    have hpos := (Finset.mem_filter.mp hβ).2
    have hp := positive_flux_pairing D u α β hbβ hpos i j φ
    simp only [mul_assoc] at hp
    rw [hp]
    ring
  change (∑ i, ∑ j, ((∫ x in B.carrier, b i j x * jet u (unitCount j + counts α) x * star (coordinateDerivativeList [i] (fun y => φ y) x)) +
    (∫ x in B.carrier, (∑ β ∈ S, (multiChoose α β : ℂ) * coefficientJet (counts β) (b i j) x * jet u (unitCount j + counts α - counts β) x) * star (coordinateDerivativeList [i] (fun y => φ y) x)))) -
    z * ((∫ x in B.carrier, ρ x * jet u (counts α) x * star (φ x)) +
      (∫ x in B.carrier, (∑ β ∈ S, (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet u (counts α - counts β) x) * star (φ x))) = _ at hw
  simp_rw [hfp] at hw
  have hleft : (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * jet u (counts α + unitCount j) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      ∑ i, ∑ j, ∫ x in B.carrier, b i j x * jet u (unitCount j + counts α) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x) := by
    rw [show (fun x => (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * jet u (counts α + unitCount j) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) =
      (fun x => ∑ i, ∑ j, b i j x * jet u (unitCount j + counts α) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) by
          funext x
          simp only [Finset.mul_sum, b, Complex.ofReal_mul, add_comm (counts α), mul_assoc]]
    have hi (i j : Fin n) : Integrable (fun x => b i j x * jet u (unitCount j + counts α) x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) (volume.restrict B.carrier) := by
      simpa only [htest] using smooth_jet_test_integrable u _ (flux_smooth D i j)
        (conjugateTest (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ))
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i hi'
    exact integral_finsetSum _ (fun j _ => hi i j)
  let H : Space n → ℂ := fun x => ∑ β ∈ Finset.univ.filter (fun β : MultiIndex n r => ∀ q, counts β q ≤ counts α q),
    (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet h (counts α - counts β) x
  let U : Space n → ℂ := fun x => ∑ β ∈ S,
    (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet u (counts α - counts β) x
  have hHint : Integrable (fun x => H x * star (φ x)) (volume.restrict B.carrier) := by
    simpa only [zero_add, conjugateTest_apply] using collected_jet_integrable h α 0 _ (density_smooth D) (conjugateTest φ)
  have hUint : Integrable (fun x => U x * star (φ x)) (volume.restrict B.carrier) := by
    simpa only [zero_add, conjugateTest_apply] using collected_jet_integrable u α 0 S (density_smooth D) (conjugateTest φ)
  have hright : (∫ x in B.carrier, (D.density x : ℂ) * commutatorSource D z u h α x * star (φ x)) =
      (∫ x in B.carrier, H x * star (φ x)) +
      z * (∫ x in B.carrier, U x * star (φ x)) +
      ∑ i, ∑ j, ∫ x in B.carrier, F i j x * star (φ x) := by
    have hc : (∫ x in B.carrier, (D.density x : ℂ) * commutatorSource D z u h α x * star (φ x)) =
        ∫ x in B.carrier, (H x + z * U x + ∑ i, ∑ j, F i j x) * star (φ x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hρ : (D.density x : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (hcρ.trans_le (D.density_bounds x hx).1)
      change (D.density x : ℂ) * ((D.density x : ℂ)⁻¹ * _) * star (φ x) = _
      rw [mul_inv_cancel_left₀ hρ]
    rw [hc]
    simp only [add_mul, Finset.sum_mul, mul_assoc]
    have hsum : Integrable (fun x => ∑ i, ∑ j, F i j x * star (φ x)) (volume.restrict B.carrier) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfint i j))
    have hhu := hHint.add (hUint.const_mul z)
    change Integrable (fun x => H x * star (φ x) + z * (U x * star (φ x))) (volume.restrict B.carrier) at hhu
    rw [integral_add hhu hsum,
      integral_add hHint (hUint.const_mul z), integral_const_mul,
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hfint i j))]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ (fun j _ => hfint i j)
  rw [hleft, hright]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hw
  change _ - z * ((_ : ℂ) + (∫ x in B.carrier, U x * star (φ x))) =
    ∫ x in B.carrier, H x * star (φ x) at hw
  linear_combination hw

end DedekindZetaZeroFree.WeakJets.Raw

end
