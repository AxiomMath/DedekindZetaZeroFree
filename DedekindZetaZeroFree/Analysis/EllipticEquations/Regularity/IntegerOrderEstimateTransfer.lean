module

public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.DifferentiatedWeakEquations
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.DifferenceQuotientH2Estimates

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

open KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates.Raw

 def castIndex {n j k : ℕ} (hjk : j ≤ k) (α : MultiIndex n j) : MultiIndex n k :=
  ⟨fun i => Fin.castLE (Nat.succ_le_succ hjk) (α.val i), by
    have hsum : (∑ i, (Fin.castLE (Nat.succ_le_succ hjk) (α.val i)).val) =
        ∑ i, (α.val i).val :=
      Finset.sum_congr rfl fun i _ => Fin.val_castLE _ _
    rw [hsum]
    exact le_trans α.property hjk⟩

private theorem directions_castIndex {n j k : ℕ} (hjk : j ≤ k) (α : MultiIndex n j) :
    (castIndex hjk α).directions = α.directions := by
  simp only [MultiIndex.directions, castIndex]
  apply List.flatMap_congr
  intro i _
  rw [Fin.val_castLE]

private theorem coordinateDerivative_castIndex {n j k : ℕ} (hjk : j ≤ k)
    (α : MultiIndex n j) (u : Space n → ℂ) :
    coordinateDerivative (castIndex hjk α) u = coordinateDerivative α u := by
  simp only [coordinateDerivative, directions_castIndex]

theorem coefficient_bound_lower_order {n j k : ℕ} {B : LocalBall n}
    {cρ Cρ κ Λ L : ℝ} (D : Coefficients B cρ Cρ κ Λ)
    (hjk : j ≤ k) (hD : Raw.BoundedCoefficientDerivatives D k L) :
    Raw.BoundedCoefficientDerivatives D j L := by
  intro α x hx
  obtain ⟨h1, h2⟩ := hD (castIndex hjk α) x hx
  exact ⟨by rw [← coordinateDerivative_castIndex hjk α]; exact h1,
    fun i j' => by rw [← coordinateDerivative_castIndex hjk α]; exact h2 i j'⟩

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

open MeasureTheory KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates.Raw

 def lowerIndex {n k l : ℕ} (hkl : k ≤ l) (α : MultiIndex n k) : MultiIndex n l :=
  ⟨fun i => ⟨(α.val i).val, by have := (α.val i).isLt; omega⟩, α.property.trans hkl⟩
 def lowerSobolev {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : IntegerSobolev B k where
  derivatives α := u.derivatives (lowerIndex hkl α)
  weak_derivatives α := u.weak_derivatives (lowerIndex hkl α)
private theorem lower_value {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : value (lowerSobolev hkl u) = value u := rfl
private theorem lower_norm {n k l : ℕ} {B : LocalBall n} (hkl : k ≤ l)
    (u : IntegerSobolev B l) : (lowerSobolev hkl u).sobolevNorm ≤ u.sobolevNorm := by
  classical
  apply Real.sqrt_le_sqrt
  change (∑ α : MultiIndex n k, ‖u.derivatives (lowerIndex hkl α)‖ ^ 2) ≤
    ∑ α : MultiIndex n l, ‖u.derivatives α‖ ^ 2
  apply Finset.sum_le_sum_of_injOn (lowerIndex hkl)
  · intro α _ β _ hab
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun a : MultiIndex n l => (a.val i).val) hab
  · intro α _; exact Finset.mem_univ _
  · intro α _; exact le_rfl
  · intro α _ _; exact sq_nonneg _

theorem compose_nested_integer_gain {n r : ℕ}
    {inner mid outer : LocalBall n} {cρ Cρ κ Λ M C K : ℝ}
    (hmo : mid.carrier ⊆ outer.carrier) (him : inner.carrier ⊆ mid.carrier)
    (D : Coefficients outer cρ Cρ κ Λ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hprevious : Raw.WeakIntegerEstimate mid outer D r M C)
    (hbootstrap : ∀ z : ℂ, ‖z‖ ≤ M →
      ∀ (u₁ : IntegerSobolev mid 1) (u : IntegerSobolev mid (r + 2))
        (h : IntegerSobolev mid (r + 1)),
        Represents u (fun x => value u₁ x) →
        WeakEquation (restrictCoefficients hmo D) z u₁ (value h) →
        ∃ v : IntegerSobolev inner (r + 1 + 2),
          Represents v (fun x => value u₁ x) ∧
          v.sobolevNorm ≤ K * (u.sobolevNorm + h.sobolevNorm)) :
    Raw.WeakIntegerEstimate inner outer D (r + 1) M (K * (C + 1)) := by
  intro z hz u h heq
  let hlow : IntegerSobolev outer r := lowerSobolev (by omega) h
  have heqLow : WeakEquation D z u (value hlow) := by
    simpa only [hlow, lower_value] using heq
  obtain ⟨v, hv, hvnorm⟩ := hprevious z hz u hlow heqLow
  obtain ⟨u₁, g, hu₁, hg, hu₁norm, hgnorm, heqMid⟩ :=
    restrict_weak_equation hmo D z u (value h) heq
  let hm := KPContLocalEnergy.restrictSobolev hmo h
  have hu₁value : Represents u₁ (fun x => value u x) :=
    hu₁ (zeroIndex n 1)
  change (fun x => value u₁ x) =ᵐ[volume.restrict mid.carrier]
    (fun x => value u x) at hu₁value
  change (fun x => value v x) =ᵐ[volume.restrict mid.carrier]
    (fun x => value u x) at hv
  have hmg : g = value hm := by
    apply Lp.ext
    have hh : (fun x => value hm x) =ᵐ[volume.restrict mid.carrier]
        (fun x => value h x) := KPContLocalEnergy.restrictSobolev_represents hmo h
    exact Filter.EventuallyEq.trans hg hh.symm
  rw [hmg] at heqMid
  obtain ⟨w, hw, hwnorm⟩ := hbootstrap z hz u₁ v hm
    (Filter.EventuallyEq.trans hv hu₁value.symm) heqMid
  refine ⟨w, ?_, ?_⟩
  · have hi : (fun x => value u₁ x) =ᵐ[volume.restrict inner.carrier]
        (fun x => value u x) :=
      ae_mono (Measure.restrict_mono him le_rfl) hu₁value
    exact Filter.EventuallyEq.trans hw hi
  · have hlowNorm : hlow.sobolevNorm ≤ h.sobolevNorm := lower_norm (by omega) h
    have hmNorm : hm.sobolevNorm ≤ h.sobolevNorm :=
      KPContLocalEnergy.sobolevNorm_restrictSobolev_le hmo h
    calc
      w.sobolevNorm ≤ K * (v.sobolevNorm + hm.sobolevNorm) := hwnorm
      _ ≤ K * (C * (‖value u‖ + h.sobolevNorm) + h.sobolevNorm) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (hvnorm.trans (mul_le_mul_of_nonneg_left
            (add_le_add_right hlowNorm _) hC)) hmNorm) hK
      _ ≤ K * ((C + 1) * (‖value u‖ + h.sobolevNorm)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        nlinarith [norm_nonneg (value u)]
      _ = K * (C + 1) * (‖value u‖ + h.sobolevNorm) := by ring

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

open MeasureTheory KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates.Raw

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

private theorem sum_counts_list {n : ℕ} (l : List (Fin n)) :
    (∑ i, l.count i) = l.length := by
  classical
  rw [← List.sum_toFinset_count_eq_length l]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hn
  exact List.count_eq_zero_of_not_mem (by simpa using hn)

private theorem split_index {n r s : ℕ} (γ : MultiIndex n (r+s)) :
    ∃ α : MultiIndex n r, ∃ β : MultiIndex n s,
      counts γ = counts α + counts β := by
  let l := γ.directions
  have hlen : l.length ≤ r+s := by
    rw [← sum_counts_list]
    simpa only [l, directions_count, counts] using γ.property
  let α : MultiIndex n r := indexOfCounts (fun i => (l.take r).count i) (by
    rw [sum_counts_list, List.length_take]
    exact min_le_left _ _)
  let β : MultiIndex n s := indexOfCounts (fun i => (l.drop r).count i) (by
    rw [sum_counts_list, List.length_drop]
    omega)
  refine ⟨α, β, ?_⟩
  funext i
  change counts γ i = (l.take r).count i + (l.drop r).count i
  rw [← List.count_append, List.take_append_drop]
  exact (directions_count γ i).symm

private theorem counts_ext {n k : ℕ} {α β : MultiIndex n k}
    (h : counts α = counts β) : α = β := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

private theorem compose_weak {n r s : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B r) (w : IntegerSobolev B s)
    (α : MultiIndex n r) (β : MultiIndex n s)
    (hw : Represents w (fun x => u.derivatives α x))
    (γ : MultiIndex n (r+s)) (hγ : counts γ = counts α + counts β) :
    IsWeakDerivative B γ (value u) (w.derivatives β) := by
  intro φ
  have h₁ := u.weak_derivatives α (derivativeTest β φ)
  have h₂ := w.weak_derivatives β φ
  have hab : (∑ i, (counts α + counts β) i) ≤ r+s := by
    simpa only [← hγ, counts] using γ.property
  have he : indexOfCounts (counts α + counts β) hab = γ :=
    counts_ext hγ.symm
  have hc : coordinateDerivative α (coordinateDerivative β (fun y => φ y)) =
      coordinateDerivative γ (fun y => φ y) := by
    rw [coordinate_add α β hab φ.contDiff, he]
  change (∫ x in B.carrier, value u x *
    coordinateDerivative α (coordinateDerivative β (fun y => φ y)) x) =
    (-1 : ℂ)^α.degree * (∫ x in B.carrier,
      u.derivatives α x * coordinateDerivative β (fun y => φ y) x) at h₁
  have hi : (∫ x in B.carrier, u.derivatives α x *
      coordinateDerivative β (fun y => φ y) x) =
      ∫ x in B.carrier, value w x * coordinateDerivative β (fun y => φ y) x := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  have hd : γ.degree = α.degree + β.degree := by
    change (∑ i, counts γ i) = (∑ i, counts α i) + (∑ i, counts β i)
    rw [hγ, Pi.add_def, Finset.sum_add_distrib]
  rw [hc, hi] at h₁
  change (∫ x in B.carrier, value w x * coordinateDerivative β (fun y => φ y) x) =
    (-1 : ℂ)^β.degree * (∫ x in B.carrier, w.derivatives β x * φ x) at h₂
  rw [h₂, ← mul_assoc, ← pow_add, ← hd] at h₁
  exact h₁

theorem collect_shifted_sobolev_jets {n r s : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B r) (q : MultiIndex n r → IntegerSobolev B s)
    (hq : ∀ α : MultiIndex n r,
      Represents (q α) (fun x => u.derivatives α x)) :
    ∃ v : IntegerSobolev B (r + s),
      Represents v (fun x => value u x) ∧
      v.sobolevNorm ≤ Real.sqrt (∑ α : MultiIndex n r, (q α).sobolevNorm ^ 2) := by
  classical
  have hex (γ : MultiIndex n (r+s)) :
      ∃ p : MultiIndex n r × MultiIndex n s, counts γ = counts p.1 + counts p.2 := by
    obtain ⟨α, β, h⟩ := split_index γ
    exact ⟨(α, β), h⟩
  let f (γ : MultiIndex n (r+s)) := Classical.choose (hex γ)
  have hf (γ : MultiIndex n (r+s)) : counts γ = counts (f γ).1 + counts (f γ).2 :=
    Classical.choose_spec (hex γ)
  let d (γ : MultiIndex n (r+s)) : BallL2 B := (q (f γ).1).derivatives (f γ).2
  have hzα : (f (zeroIndex n (r+s))).1 = zeroIndex n r := by
    apply counts_ext
    funext i
    have hh := congrFun (hf (zeroIndex n (r+s))) i
    change 0 = counts (f (zeroIndex n (r+s))).1 i +
      counts (f (zeroIndex n (r+s))).2 i at hh
    change counts (f (zeroIndex n (r+s))).1 i = 0
    omega
  have hzβ : (f (zeroIndex n (r+s))).2 = zeroIndex n s := by
    apply counts_ext
    funext i
    have hh := congrFun (hf (zeroIndex n (r+s))) i
    change 0 = counts (f (zeroIndex n (r+s))).1 i +
      counts (f (zeroIndex n (r+s))).2 i at hh
    change counts (f (zeroIndex n (r+s))).2 i = 0
    omega
  have hz : d (zeroIndex n (r+s)) = value u := by
    dsimp only [d]
    rw [hzα, hzβ]
    exact Lp.ext (hq (zeroIndex n r))
  let v : IntegerSobolev B (r+s) := ⟨d, by
    intro γ
    change IsWeakDerivative B γ (d (zeroIndex n (r+s))) (d γ)
    rw [hz]
    exact compose_weak u (q (f γ).1) (f γ).1 (f γ).2 (hq _) γ (hf γ)⟩
  refine ⟨v, ?_, ?_⟩
  · change ∀ᵐ x ∂volume.restrict B.carrier, d (zeroIndex n (r+s)) x = value u x
    rw [hz]
    exact Filter.Eventually.of_forall (fun _ => rfl)
  · apply Real.sqrt_le_sqrt
    change (∑ γ : MultiIndex n (r+s), ‖d γ‖ ^ 2) ≤ _
    have hinj : Function.Injective f := by
      intro γ δ h
      apply counts_ext
      rw [hf γ, hf δ, h]
    have hsum : (∑ γ : MultiIndex n (r+s), ‖d γ‖ ^ 2) ≤
        ∑ p : MultiIndex n r × MultiIndex n s, ‖(q p.1).derivatives p.2‖ ^ 2 := by
      apply Finset.sum_le_sum_of_injOn f (hinj.injOn)
        (Finset.subset_univ _)
      · intro γ hγ
        exact le_rfl
      · intro p hp hnp
        exact sq_nonneg _
    refine hsum.trans_eq ?_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro α hα
    exact (q α).sobolevNorm_sq.symm

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

end

end

section

noncomputable section

set_option maxHeartbeats 1000000

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

open MeasureTheory KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates.Raw

 def L2Bound {n : ℕ} (B : LocalBall n) (f : Space n → ℂ) (C : ℝ) : Prop :=
  ∃ hf : MemLp f 2 (volume.restrict B.carrier), ‖hf.toLp f‖ ≤ C

private theorem bound_mono {n : ℕ} {B : LocalBall n} {f : Space n → ℂ} {C C' : ℝ}
    (hf : L2Bound B f C) (h : C ≤ C') : L2Bound B f C' := by
  obtain ⟨hf, hn⟩ := hf
  exact ⟨hf, hn.trans h⟩

private theorem bound_add {n : ℕ} {B : LocalBall n} {f g : Space n → ℂ} {C D : ℝ}
    (hf : L2Bound B f C) (hg : L2Bound B g D) :
    L2Bound B (fun x => f x + g x) (C + D) := by
  obtain ⟨hf, hn⟩ := hf
  obtain ⟨hg, hm⟩ := hg
  refine ⟨hf.add hg, ?_⟩
  change ‖(hf.add hg).toLp (f + g)‖ ≤ C + D
  rw [MemLp.toLp_add hf hg]
  exact (norm_add_le _ _).trans (add_le_add hn hm)

private theorem bound_sum {n : ℕ} {B : LocalBall n} {ι : Type*}
    (s : Finset ι) (f : ι → Space n → ℂ) (C : ι → ℝ)
    (hf : ∀ i ∈ s, L2Bound B (f i) (C i)) :
    L2Bound B (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using (MemLp.zero' : MemLp (fun _ : Space n => (0 : ℂ)) 2 (volume.restrict B.carrier)), by simp⟩
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      bound_add (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

private theorem bound_mul {n : ℕ} {B : LocalBall n} {a f : Space n → ℂ} {A C : ℝ}
    (hA : 0 ≤ A) (ha : AEStronglyMeasurable a (volume.restrict B.carrier))
    (hab : ∀ x ∈ B.carrier, ‖a x‖ ≤ A) (hf : L2Bound B f C) :
    L2Bound B (fun x => a x * f x) (A * C) := by
  obtain ⟨hf, hn⟩ := hf
  have hmeas := ha.mul hf.aestronglyMeasurable
  have hle : ∀ᵐ x ∂volume.restrict B.carrier, ‖a x * f x‖ ≤ A * ‖f x‖ := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hab x hx) (norm_nonneg _)
  have hm := hf.of_le_mul hmeas hle
  refine ⟨hm, ?_⟩
  have hh : ∀ᵐ x ∂volume.restrict B.carrier,
      ‖hm.toLp (fun x => a x * f x) x‖ ≤ A * ‖hf.toLp f x‖ := by
    filter_upwards [hle, hm.coeFn_toLp, hf.coeFn_toLp] with x hx h1 h2
    change ‖hm.toLp (a * f) x‖ ≤ A * ‖hf.toLp f x‖
    rw [h1, h2]
    exact hx
  exact (Lp.norm_le_mul_norm_of_ae_le_mul hh).trans
    (mul_le_mul_of_nonneg_left hn hA)

private theorem bound_jet {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) :
    L2Bound B (fun x => jet u γ x) u.sobolevNorm := by
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hnorm : ‖jet u γ‖ ≤ u.sobolevNorm := by
    unfold jet
    split_ifs with hγ
    · have hs : ‖u.derivatives (indexOfCounts γ hγ)‖ ^ 2 ≤ u.normSq :=
        by
          unfold IntegerSobolev.normSq
          exact Finset.single_le_sum (fun α _ => sq_nonneg ‖u.derivatives α‖) (Finset.mem_univ _)
      have := u.sobolevNorm_sq
      nlinarith [norm_nonneg (u.derivatives (indexOfCounts γ hγ))]
    · simpa using hu
  refine ⟨Lp.memLp _, ?_⟩
  simpa using hnorm

private theorem coeff_smooth {n : ℕ} {B : LocalBall n} (γ : Counts n)
    {f : Space n → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier) :
    AEStronglyMeasurable (coefficientJet γ f) (volume.restrict B.carrier) := by
  have hh : ∀ l : List (Fin n),
      ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) B.carrier := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih =>
      exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const
  exact (hh _).continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet

private theorem coeff_bound {n k : ℕ} {B : LocalBall n} {L : ℝ}
    {f : Space n → ℂ} (hf : ∀ α : MultiIndex n k, ∀ x ∈ B.carrier,
      ‖coordinateDerivative α f x‖ ≤ L) (γ : Counts n) (hγ : (∑ i, γ i) ≤ k) :
    ∀ x ∈ B.carrier, ‖coefficientJet γ f x‖ ≤ L := by
  exact hf (indexOfCounts γ hγ)

private theorem bound_sum_uniform {n : ℕ} {B : LocalBall n} {ι : Type*} [Fintype ι]
    (s : Finset ι) (f : ι → Space n → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i ∈ s, L2Bound B (f i) C) :
    L2Bound B (fun x => ∑ i ∈ s, f i x) ((Fintype.card ι : ℝ) * C) := by
  apply bound_mono (bound_sum s f (fun _ => C) hf)
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast s.card_le_univ) hC

private theorem counts_bound {n k : ℕ} (α : MultiIndex n k) :
    (∑ i, counts α i) ≤ k := α.property

private theorem counts_unit_bound {n k : ℕ} (α : MultiIndex n k) (j : Fin n) :
    (∑ i, (counts α + unitCount j) i) ≤ k + 1 := by
  simpa [Pi.add_apply, unitCount, Finset.sum_add_distrib] using Nat.add_le_add_right (counts_bound α) 1

theorem commutatorSource_memLp_bound (n r : ℕ) (cρ Cρ κ Λ L M : ℝ)
    (hcρ : 0 < cρ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : LocalBall n)
      (D : Coefficients B cρ Cρ κ Λ),
      Raw.BoundedCoefficientDerivatives D (r + 1) L →
      ∀ (z : ℂ), ‖z‖ ≤ M →
      ∀ (u : IntegerSobolev B (r + 1)) (h : IntegerSobolev B r)
        (α : MultiIndex n r),
      ∃ hg : MemLp (commutatorSource D z u h α) 2 (volume.restrict B.carrier),
        ‖hg.toLp (commutatorSource D z u h α)‖ ≤
          K * (u.sobolevNorm + h.sobolevNorm) := by
  classical
  let Q : ℝ := 1 + ∑ a : MultiIndex n r, ∑ b : MultiIndex n r, (multiChoose a b : ℝ)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hchoose : ∀ a b : MultiIndex n r, (multiChoose a b : ℝ) ≤ Q := by
    intro a b
    have hb : (multiChoose a b : ℝ) ≤ ∑ b' : MultiIndex n r, (multiChoose a b' : ℝ) :=
      Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ b)
    have ha : (∑ b' : MultiIndex n r, (multiChoose a b' : ℝ)) ≤
        ∑ a' : MultiIndex n r, ∑ b' : MultiIndex n r, (multiChoose a' b' : ℝ) :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ a)
    dsimp [Q]
    linarith
  let N : ℝ := Fintype.card (MultiIndex n r)
  let A : ℝ := N * Q * L * (1 + M + 2 * (n : ℝ) * n)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1 + cρ⁻¹ * A, by positivity, ?_⟩
  intro B D hD z hz u h α
  let ρ : Space n → ℂ := fun x => (D.density x : ℂ)
  let b (i j : Fin n) : Space n → ℂ := fun x => ((D.density x * D.matrix x i j : ℝ) : ℂ)
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ B.carrier :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn D.density_smooth
  have hb : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (b i j) B.carrier := by
    intro i j
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (D.density_smooth.mul (D.matrix_smooth i j))
  have hρb : ∀ γ : Counts n, (∑ i, γ i) ≤ r + 1 →
      ∀ x ∈ B.carrier, ‖coefficientJet γ ρ x‖ ≤ L := by
    intro γ hγ
    exact coeff_bound (fun a x hx => (hD a x hx).1) γ hγ
  have hbb : ∀ i j (γ : Counts n), (∑ i, γ i) ≤ r + 1 →
      ∀ x ∈ B.carrier, ‖coefficientJet γ (b i j) x‖ ≤ L := by
    intro i j γ hγ
    exact coeff_bound (fun a x hx => (hD a x hx).2 i j) γ hγ
  let S := u.sobolevNorm + h.sobolevNorm
  have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  have hh0 : 0 ≤ h.sobolevNorm := Real.sqrt_nonneg _
  have hS : 0 ≤ S := add_nonneg hu0 hh0
  have hjetu : ∀ γ, L2Bound B (fun x => jet u γ x) S :=
    fun γ => bound_mono (bound_jet u γ) (by dsimp [S]; linarith)
  have hjeth : ∀ γ, L2Bound B (fun x => jet h γ x) S :=
    fun γ => bound_mono (bound_jet h γ) (by dsimp [S]; linarith)
  have hterm : ∀ (β : MultiIndex n r) (γ : Counts n) (f g : Space n → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) f B.carrier →
      (∀ x ∈ B.carrier, ‖coefficientJet γ f x‖ ≤ L) → L2Bound B g S →
      L2Bound B (fun x => (multiChoose α β : ℂ) * coefficientJet γ f x * g x)
        (Q * L * S) := by
    intro β γ f g hf hfb hg
    have ht := bound_mul (a := fun _ => (multiChoose α β : ℂ))
      (Nat.cast_nonneg (multiChoose α β)) aestronglyMeasurable_const
      (fun x hx => by simp) (bound_mul hL (coeff_smooth γ hf) hfb hg)
    apply bound_mono (by simpa only [mul_assoc] using ht)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hchoose α β) (mul_nonneg hL hS)
  let below := Finset.univ.filter (fun β : MultiIndex n r => ∀ i, counts β i ≤ counts α i)
  let positive := below.filter (fun β => 0 < β.degree)
  have hd : ∀ β : MultiIndex n r, (∑ i, counts β i) ≤ r + 1 :=
    fun β => (counts_bound β).trans (Nat.le_succ r)
  have hfirst : L2Bound B (fun x => ∑ β ∈ below,
      (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet h (counts α - counts β) x)
      (N * (Q * L * S)) :=
    bound_sum_uniform below _ (by positivity)
      (fun β hβ => hterm β (counts β) ρ _ hρ (hρb _ (hd β)) (hjeth _))
  have hsecond : L2Bound B (fun x => ∑ β ∈ positive,
      (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet u (counts α - counts β) x)
      (N * (Q * L * S)) :=
    bound_sum_uniform positive _ (by positivity)
      (fun β hβ => hterm β (counts β) ρ _ hρ (hρb _ (hd β)) (hjetu _))
  have hthird : L2Bound B (fun x => ∑ i, ∑ j, ∑ β ∈ positive,
      (multiChoose α β : ℂ) *
        (coefficientJet (counts β + unitCount i) (b i j) x * jet u (counts α - counts β + unitCount j) x +
         coefficientJet (counts β) (b i j) x * jet u (counts α - counts β + unitCount i + unitCount j) x))
      ((n : ℝ) * ((n : ℝ) * (N * (2 * (Q * L * S))))) := by
    have hncard : (n : ℝ) = (Fintype.card (Fin n) : ℝ) := by simp
    rw [hncard]
    apply bound_sum_uniform Finset.univ _ (by positivity)
    intro i hi
    apply bound_sum_uniform Finset.univ _ (by positivity)
    intro j hj
    apply bound_sum_uniform positive _ (by positivity)
    intro β hβ
    have ht1 := hterm β (counts β + unitCount i) (b i j) _ (hb i j)
      (hbb i j _ (counts_unit_bound β i)) (hjetu (counts α - counts β + unitCount j))
    have ht2 := hterm β (counts β) (b i j) _ (hb i j)
      (hbb i j _ (hd β)) (hjetu (counts α - counts β + unitCount i + unitCount j))
    simpa only [mul_add, two_mul, mul_assoc] using bound_add ht1 ht2
  have hzin := bound_mul hM aestronglyMeasurable_const (fun x hx => hz) hsecond
  have hinn := bound_add (bound_add hfirst hzin) hthird
  have hin : L2Bound B (fun x =>
      ((∑ β ∈ below, (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet h (counts α - counts β) x) +
       z * (∑ β ∈ positive, (multiChoose α β : ℂ) * coefficientJet (counts β) ρ x * jet u (counts α - counts β) x) +
       ∑ i, ∑ j, ∑ β ∈ positive, (multiChoose α β : ℂ) *
         (coefficientJet (counts β + unitCount i) (b i j) x * jet u (counts α - counts β + unitCount j) x +
          coefficientJet (counts β) (b i j) x * jet u (counts α - counts β + unitCount i + unitCount j) x))) (A * S) := by
    apply bound_mono hinn
    dsimp [A]
    ring_nf
    exact le_rfl
  have hρnz : ∀ x ∈ B.carrier, ρ x ≠ 0 := by
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hcρ.trans_le (D.density_bounds x hx).1))
  have hinv : ∀ x ∈ B.carrier, ‖(ρ x)⁻¹‖ ≤ cρ⁻¹ := by
    intro x hx
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hcρ.trans_le (D.density_bounds x hx).1)]
    exact (inv_le_inv₀ (hcρ.trans_le (D.density_bounds x hx).1) hcρ).mpr (D.density_bounds x hx).1
  have hout := bound_mul (le_of_lt (inv_pos.mpr hcρ))
    ((hρ.continuousOn.inv₀ hρnz).aestronglyMeasurable Metric.isOpen_ball.measurableSet) hinv hin
  apply bound_mono hout
  dsimp [S]
  nlinarith

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

end

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

open MeasureTheory KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates.Raw

 def canonicalCoefficients {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) : KPContLocalEnergy.Coefficients B cρ Cρ κ Λ where
  density := D.density
  matrix := D.matrix
  density_smooth := D.density_smooth
  matrix_smooth := D.matrix_smooth
  density_bounds := D.density_bounds
  symmetric := D.symmetric
  ellipticity := D.ellipticity
  upper_bound := D.upper_bound

private theorem first_derivative_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ L : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hD : Raw.BoundedCoefficientDerivatives D 1 L) :
    KPContLocalDifference.BoundedFirstDerivatives (canonicalCoefficients D) L := by
  intro x hx i j k
  have h := (hD (firstIndex k) x hx).2 i j
  simp only [coordinateDerivative, KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions,
    coordinateDerivativeList] at h
  let f : Space n → ℝ := fun y => D.density y * D.matrix y i j
  have hf : DifferentiableAt ℝ f x :=
    ((D.density_smooth.mul (D.matrix_smooth i j)).differentiableOn (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)
  have heq : fderiv ℝ (fun y => (f y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  change ‖fderiv ℝ f x (EuclideanSpace.single k 1)‖ ≤ L
  change ‖fderiv ℝ (fun y => (f y : ℂ)) x (EuclideanSpace.single k 1)‖ ≤ L at h
  rw [heq] at h
  simpa using h

private theorem jet_norm_le {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (γ : Counts n) : ‖jet u γ‖ ≤ u.sobolevNorm := by
  have hu : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  unfold jet
  split_ifs with hγ
  · have hs : ‖u.derivatives (indexOfCounts γ hγ)‖ ^ 2 ≤ u.normSq :=
      Finset.single_le_sum (fun α _ => sq_nonneg ‖u.derivatives α‖) (Finset.mem_univ _)
    have := u.sobolevNorm_sq
    nlinarith [norm_nonneg (u.derivatives (indexOfCounts γ hγ))]
  · simpa using hu

private theorem finite_sqrt_bound {ι : Type*} [Fintype ι] (f : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ T) :
    Real.sqrt (∑ i, f i ^ 2) ≤ ((Fintype.card ι : ℝ) + 1) * T := by
  have hs : (∑ i, f i ^ 2) ≤ (Fintype.card ι : ℝ) * T ^ 2 := by
    calc
      _ ≤ ∑ _ : ι, T ^ 2 := Finset.sum_le_sum fun i _ => by
        nlinarith [(hf i).1, (hf i).2]
      _ = _ := by simp
  have hp : 0 ≤ ∑ i, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he := Real.sq_sqrt hp
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hn' : (Fintype.card ι : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) ^ 2 := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right hn' (sq_nonneg T)
  have hnonneg : 0 ≤ ((Fintype.card ι : ℝ) + 1) * T := by positivity
  nlinarith [Real.sqrt_nonneg (∑ i, f i ^ 2)]

theorem quantitative_shifted_jet_gain (n r : ℕ) (hn : 0 < n)
    (a R cρ Cρ κ Λ L M : ℝ) (ha : 0 < a) (haR : a < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ inner outer : LocalBall n,
      inner.center = outer.center → inner.radius = a → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        Raw.BoundedCoefficientDerivatives D (r + 1) L →
        ∀ z : ℂ, ‖z‖ ≤ M →
        ∀ (u₁ : IntegerSobolev outer 1) (u : IntegerSobolev outer (r + 1))
          (h : IntegerSobolev outer r),
          Represents u (fun x => value u₁ x) → WeakEquation D z u₁ (value h) →
          ∃ (w : IntegerSobolev inner r)
            (q : MultiIndex n r → IntegerSobolev inner 2),
            Represents w (fun x => value u₁ x) ∧
            (∀ α : MultiIndex n r,
              Represents (q α) (fun x => w.derivatives α x)) ∧
            Real.sqrt (∑ α : MultiIndex n r, (q α).sobolevNorm ^ 2) ≤
              C * (u.sobolevNorm + h.sobolevNorm) := by
  classical
  obtain ⟨K, hK, hcomm⟩ := commutatorSource_memLp_bound n r cρ Cρ κ Λ L M hcρ hL hM
  obtain ⟨H, hH, hh2⟩ := kp_cont_local_difference_h2 n hn a R cρ Cρ κ Λ L M
    ha haR hcρ hκ hL hM
  let J : ℝ := (Fintype.card (MultiIndex n 1) : ℝ) + 1
  let N : ℝ := (Fintype.card (MultiIndex n r) : ℝ) + 1
  refine ⟨N * H * (J + K), by dsimp [N, J]; positivity, ?_⟩
  intro inner outer hc hi ho D hD z hz u₁ u h hu heq
  have hsub : inner.carrier ⊆ outer.carrier := by
    change Metric.ball inner.center inner.radius ⊆ Metric.ball outer.center outer.radius
    rw [hc, hi, ho]
    exact Metric.ball_subset_ball haR.le
  let b : IntegerSobolev outer r :=
    ⟨fun δ => jet u (counts δ), by
      intro δ
      have hzero : counts (zeroIndex n r) = 0 := rfl
      have hh := jet_weak_derivative u (zeroIndex n r) δ
        (by simp only [hzero, Pi.zero_apply, Finset.sum_const_zero]; omega)
        (by simpa only [hzero, zero_add, counts] using δ.property.trans (Nat.le_succ r))
      change IsWeakDerivative outer δ (jet u (counts (zeroIndex n r))) _
      simpa only [hzero, zero_add] using hh⟩
  obtain ⟨w, hw, _⟩ := KPContLocalEnergy.SobolevEnergyEstimates.restrict_integerSobolev inner outer hsub b
  have hbval : value b = value u := by
    change jet u (counts (zeroIndex n r)) = value u
    unfold jet
    rw [dif_pos (show (∑ i, counts (zeroIndex n r) i) ≤ r + 1 by
      simp [counts, zeroIndex])]
    rfl
  have hwrep : Represents w (fun x => value u₁ x) := by
    have hv := hw (zeroIndex n r)
    change ∀ᵐ x ∂volume.restrict inner.carrier, value w x = value b x at hv
    rw [hbval] at hv
    filter_upwards [hv, ae_restrict_of_ae_restrict_of_subset hsub hu] with x hx hy
    exact hx.trans hy
  have hgain : ∀ α : MultiIndex n r, ∃ v : IntegerSobolev inner 2,
      Represents v (fun x => w.derivatives α x) ∧
      v.sobolevNorm ≤ H * (J + K) * (u.sobolevNorm + h.sobolevNorm) := by
    intro α
    obtain ⟨hg, hgnorm⟩ := hcomm outer D hD z hz u h α
    obtain ⟨t, ht, hteq⟩ := differentiated_weak_equation D hcρ z u₁ u h hu heq α hg
    have htval : ∀ᵐ x ∂volume.restrict outer.carrier, value t x = jet u (counts α) x := by
      simpa only [value, show counts (zeroIndex n 1) = 0 from rfl, add_zero] using
        ht (zeroIndex n 1)
    have htnorm : t.sobolevNorm ≤ J * u.sobolevNorm := by
      apply (finite_sqrt_bound (fun δ => ‖t.derivatives δ‖) (Real.sqrt_nonneg _)
        (fun δ => ⟨norm_nonneg _, ?_⟩))
      have he : t.derivatives δ = jet u (counts α + counts δ) := Lp.ext (ht δ)
      rw [he]
      exact jet_norm_le u _
    obtain ⟨v, hv, hvnorm⟩ := hh2 inner outer hc hi ho (canonicalCoefficients D)
      (first_derivative_bound D (coefficient_bound_lower_order D (by omega) hD))
      z hz t (hg.toLp (commutatorSource D z u h α)) hteq
    refine ⟨v, ?_, ?_⟩
    · have htval' := ae_restrict_of_ae_restrict_of_subset hsub htval
      have hwα := hw α
      change ∀ᵐ x ∂volume.restrict inner.carrier,
        w.derivatives α x = jet u (counts α) x at hwα
      filter_upwards [hv, htval', hwα] with x hx hy hz'
      exact hx.trans (hy.trans hz'.symm)
    · calc
        v.sobolevNorm ≤ H * (t.sobolevNorm + ‖hg.toLp (commutatorSource D z u h α)‖) := hvnorm
        _ ≤ H * (J * u.sobolevNorm + K * (u.sobolevNorm + h.sobolevNorm)) :=
          mul_le_mul_of_nonneg_left (add_le_add htnorm hgnorm) hH.le
        _ ≤ H * (J + K) * (u.sobolevNorm + h.sobolevNorm) := by
          have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
          have hh0 : 0 ≤ h.sobolevNorm := Real.sqrt_nonneg _
          have hJ : 0 ≤ J := by dsimp [J]; positivity
          have hhJ : 0 ≤ J * h.sobolevNorm := mul_nonneg hJ hh0
          have hinner : J * u.sobolevNorm + K * (u.sobolevNorm + h.sobolevNorm) ≤
              (J + K) * (u.sobolevNorm + h.sobolevNorm) := by nlinarith only [hhJ]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hH.le
  choose q hq hqnorm using hgain
  refine ⟨w, q, hwrep, hq, ?_⟩
  have hbound := finite_sqrt_bound (fun α => (q α).sobolevNorm)
    (show 0 ≤ H * (J + K) * (u.sobolevNorm + h.sobolevNorm) by
      have hu0 : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
      have hh0 : 0 ≤ h.sobolevNorm := Real.sqrt_nonneg _
      dsimp [J]; positivity)
    (fun α => ⟨Real.sqrt_nonneg _, hqnorm α⟩)
  dsimp only [N] at *
  convert hbound using 1 <;> ring

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration.Iteration

end

end

section

set_option maxHeartbeats 1000000

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

open MeasureTheory KPContLocalNorm KPContLocalEnergy.SobolevEnergyEstimates KPContLocalEnergy.SobolevEnergyEstimates.Raw

private theorem derivative_unique {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (f g v : BallL2 B) (hg : IsWeakDerivative B α f g)
    (hv : IsWeakDerivative B α f v) : g = v := by
  apply Lp.ext
  apply Distribution.ofFun_injective (Ω := B.toOpens) (μ := volume) (f := g) (f' := v)
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp v).locallyIntegrable (by norm_num)))
    (n := (⊤ : ℕ∞))
  ext φ
  let ψ : TestFunction B.toOpens ℂ ⊤ :=
    ⟨fun x => (φ x : ℂ), Complex.ofRealCLM.contDiff.comp φ.contDiff,
      φ.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl,
      (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) rfl φ).trans φ.tsupport_subset⟩
  have h := (mul_left_cancel₀ (show (-1 : ℂ) ^ α.degree ≠ 0 by simp)
    ((hg ψ).symm.trans (hv ψ)))
  have heq (w : BallL2 B) : (∫ x, φ x • w x) = ∫ x in B.carrier, w x * ψ x := by
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
      (s := B.carrier) (Filter.Eventually.of_forall (fun x hx => by
        simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_smul]))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by change φ x • w x = w x * (φ x : ℂ); simp [Complex.real_smul, mul_comm])
  rw [Distribution.ofFun_apply
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable (by norm_num))),
    Distribution.ofFun_apply
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp v).locallyIntegrable (by norm_num))),
    heq, heq]
  exact h

private theorem smooth_norm {n k : ℕ} (B : LocalBall n) (u : Space n → ℂ)
    (v : IntegerSobolev B k) (hv : RepresentsClassicalDerivatives v u) :
    v.sobolevNorm = Raw.functionSobolevNorm B k u := by
  unfold IntegerSobolev.sobolevNorm IntegerSobolev.normSq Raw.functionSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [l2_norm_eq_functionL2Norm_of_ae B (v.derivatives α) (coordinateDerivative α u) (hv α)]

private theorem represents_classical {n k : ℕ} {B : LocalBall n} (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (hL2 : ∀ α : MultiIndex n k, MemLp (coordinateDerivative α u) 2 (volume.restrict B.carrier))
    (v : IntegerSobolev B k) (hv : Represents v u) :
    RepresentsClassicalDerivatives v u := by
  obtain ⟨w, hw⟩ := smooth_has_integerSobolev_data B u hu hL2
  have hrep : RepresentsClassicalDerivatives w u := by
    intro α
    rw [hw α]
    exact (hL2 α).coeFn_toLp
  have heq : value v = value w := by
    apply Lp.ext
    have hwvalue : ∀ᵐ x ∂volume.restrict B.carrier, value w x = u x := by
      simpa only [value, coordinateDerivative_zeroIndex] using hrep (zeroIndex n k)
    filter_upwards [hv, hwvalue] with x hx hy
    exact hx.trans hy.symm
  intro α
  have hder : v.derivatives α = w.derivatives α := by
    apply derivative_unique B α (value v)
    · exact v.weak_derivatives α
    · rw [heq]
      exact w.weak_derivatives α
  rw [hder]
  exact hrep α

 def canonicalCoefficients {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) : KPContLocalEnergy.Coefficients B cρ Cρ κ Λ where
  density := D.density
  matrix := D.matrix
  density_smooth := D.density_smooth
  matrix_smooth := D.matrix_smooth
  density_bounds := D.density_bounds
  symmetric := D.symmetric
  ellipticity := D.ellipticity
  upper_bound := D.upper_bound

private theorem first_derivative_bound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ L : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (hD : Raw.BoundedCoefficientDerivatives D 1 L) :
    KPContLocalDifference.BoundedFirstDerivatives (canonicalCoefficients D) L := by
  intro x hx i j k
  have h := (hD (firstIndex k) x hx).2 i j
  simp only [coordinateDerivative, firstIndex_directions, coordinateDerivativeList] at h
  let f : Space n → ℝ := fun y => D.density y * D.matrix y i j
  have hf : DifferentiableAt ℝ f x :=
    ((D.density_smooth.mul (D.matrix_smooth i j)).differentiableOn (by simp)).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)
  have heq : fderiv ℝ (fun y => (f y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ f x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  change ‖fderiv ℝ f x (EuclideanSpace.single k 1)‖ ≤ L
  change ‖fderiv ℝ (fun y => (f y : ℂ)) x (EuclideanSpace.single k 1)‖ ≤ L at h
  rw [heq] at h
  simpa using h

private theorem value_norm_le {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) :
    ‖value u‖ ≤ u.sobolevNorm := by
  have hh : ‖value u‖ ^ 2 ≤ u.normSq :=
    Finset.single_le_sum (fun α _ => sq_nonneg ‖u.derivatives α‖)
      (Finset.mem_univ (zeroIndex n k))
  have hs := u.sobolevNorm_sq
  have hp : 0 ≤ u.sobolevNorm := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (value u)]

private theorem sobolev_unique {n k : ℕ} {B : LocalBall n}
    (u v : IntegerSobolev B k) (heq : Represents u (fun x => value v x)) : u = v := by
  have hd : u.derivatives = v.derivatives := by
    funext α
    exact derivative_unique B α (value u) _ _ (u.weak_derivatives α)
      (by
        have h0 : value u = value v := Lp.ext heq
        rw [h0]
        exact v.weak_derivatives α)
  cases u
  cases v
  simp_all

private theorem quantitative_weak_zero_gain (n : ℕ) (hn : 0 < n)
    (a R cρ Cρ κ Λ L M : ℝ) (ha : 0 < a) (haR : a < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ inner outer : LocalBall n,
      inner.center = outer.center → inner.radius = a → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        Raw.BoundedCoefficientDerivatives D 1 L →
        Raw.WeakIntegerEstimate inner outer D 0 M C := by
  let b : ℝ := (a + R) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a < b := by dsimp [b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  obtain ⟨E, hE, henergy⟩ := kp_cont_local_energy_h1 n hn b R cρ Cρ κ Λ M hb hbR hcρ hκ hM
  obtain ⟨H, hH, hh2⟩ := kp_cont_local_difference_h2 n hn a b cρ Cρ κ Λ L M ha hab hcρ hκ hL hM
  refine ⟨H * (E + 1), by positivity, ?_⟩
  intro inner outer hc hi ho D hD z hz u h heq
  let mid : LocalBall n := ⟨hn, outer.center, b, hb⟩
  have hmo : mid.carrier ⊆ outer.carrier := by
    change Metric.ball outer.center b ⊆ Metric.ball outer.center outer.radius
    rw [ho]
    exact Metric.ball_subset_ball hbR.le
  have him : inner.carrier ⊆ mid.carrier := by
    change Metric.ball inner.center inner.radius ⊆ Metric.ball outer.center b
    rw [hc, hi]
    exact Metric.ball_subset_ball hab.le
  obtain ⟨v, hv, hvnorm⟩ := (henergy mid outer rfl rfl ho (canonicalCoefficients D)).1
    z hz u (value h) heq
  obtain ⟨w, g, hw, hg, hwnorm, hgnorm, hweq⟩ := restrict_weak_equation hmo D z u (value h) heq
  have hw0 : Represents w (fun x => value u x) := hw (zeroIndex n 1)
  have hvw : v = w := sobolev_unique v w (Filter.EventuallyEq.trans hv (Filter.EventuallyEq.symm hw0))
  let Dm := restrictCoefficients hmo D
  have hDm : Raw.BoundedCoefficientDerivatives Dm 1 L := fun α x hx => hD α x (hmo hx)
  obtain ⟨q, hq, hqnorm⟩ := hh2 inner mid hc hi rfl (canonicalCoefficients Dm)
    (first_derivative_bound Dm hDm) z hz v g (by rw [hvw]; exact hweq)
  refine ⟨q, Filter.EventuallyEq.trans hq (ae_restrict_of_ae_restrict_of_subset him hv), ?_⟩
  have hh : ‖value h‖ ≤ h.sobolevNorm := value_norm_le h
  have hu : 0 ≤ ‖value u‖ := norm_nonneg _
  have hh0 : 0 ≤ h.sobolevNorm := Real.sqrt_nonneg _
  calc
    q.sobolevNorm ≤ H * (v.sobolevNorm + ‖g‖) := hqnorm
    _ ≤ H * (E * (‖value u‖ + h.sobolevNorm) + h.sobolevNorm) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (hvnorm.trans (mul_le_mul_of_nonneg_left (add_le_add_right hh _) hE.le))
        (hgnorm.trans hh)) hH.le
    _ ≤ H * (E + 1) * (‖value u‖ + h.sobolevNorm) := by nlinarith

theorem quantitative_weak_integer_gain (n r : ℕ) (hn : 0 < n)
    (a R cρ Cρ κ Λ L M : ℝ) (ha : 0 < a) (haR : a < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ inner outer : LocalBall n,
      inner.center = outer.center → inner.radius = a → outer.radius = R →
      ∀ D : Coefficients outer cρ Cρ κ Λ,
        Raw.SmoothNearClosedBall D → Raw.BoundedCoefficientDerivatives D (r + 1) L →
        Raw.WeakIntegerEstimate inner outer D r M C := by
  induction r generalizing a R with
  | zero =>
    obtain ⟨C, hC, hest⟩ := quantitative_weak_zero_gain n hn a R cρ Cρ κ Λ L M
      ha haR hcρ hκ hL hM
    exact ⟨C, hC, fun inner outer hc hi ho D _hnear hD => hest inner outer hc hi ho D hD⟩
  | succ r ih =>
    let b : ℝ := (a + R) / 2
    have hb : 0 < b := by dsimp [b]; linarith
    have hab : a < b := by dsimp [b]; linarith
    have hbR : b < R := by dsimp [b]; linarith
    obtain ⟨C, hC, hprevious⟩ := ih b R hb hbR
    obtain ⟨K, hK, hshift⟩ := Iteration.quantitative_shifted_jet_gain n (r + 1) hn
      a b cρ Cρ κ Λ L M ha hab hcρ hκ hL hM
    refine ⟨K * (C + 1), by positivity, ?_⟩
    intro inner outer hc hi ho D hnear hD
    let mid : LocalBall n := ⟨hn, outer.center, b, hb⟩
    have hmo : mid.carrier ⊆ outer.carrier := by
      change Metric.ball outer.center b ⊆ Metric.ball outer.center outer.radius
      rw [ho]
      exact Metric.ball_subset_ball hbR.le
    have him : inner.carrier ⊆ mid.carrier := by
      change Metric.ball inner.center inner.radius ⊆ Metric.ball outer.center b
      rw [hc, hi]
      exact Metric.ball_subset_ball hab.le
    have hDlow : Raw.BoundedCoefficientDerivatives D (r + 1) L :=
      Iteration.coefficient_bound_lower_order D (by omega) hD
    have hprev := hprevious mid outer rfl rfl ho D hnear hDlow
    apply Iteration.compose_nested_integer_gain hmo him D hC.le hK.le hprev
    intro z hz u₁ u h hu heq
    have hDm : Raw.BoundedCoefficientDerivatives (restrictCoefficients hmo D) (r + 1 + 1) L :=
      fun α x hx => hD α x (hmo hx)
    obtain ⟨w, q, hw, hq, hqnorm⟩ := hshift inner mid hc hi rfl
      (restrictCoefficients hmo D) hDm z hz u₁ u h hu heq
    obtain ⟨v, hv, hvnorm⟩ := Iteration.collect_shifted_sobolev_jets w q hq
    exact ⟨v, Filter.EventuallyEq.trans hv hw, hvnorm.trans hqnorm⟩

theorem smooth_estimates_of_weak_integer_estimate {n r : ℕ}
    {inner outer : LocalBall n} {cρ Cρ κ Λ M C : ℝ}
    (D : Coefficients outer cρ Cρ κ Λ) (hcρ : 0 < cρ)
    (hsub : inner.carrier ⊆ outer.carrier)
    (hweak : Raw.WeakIntegerEstimate inner outer D r M C) :
    Raw.SmoothSourceIntegerEstimate inner outer D r M C ∧
    Raw.SmoothIntegerEstimate inner outer D r M C := by
  have hsource : Raw.SmoothSourceIntegerEstimate inner outer D r M C := by
    intro z hz u h U hU hclosed hh hL2 heq
    have hL2all (α : MultiIndex n r) :=
      coordinateDerivative_memLp_of_closedBall outer hU hclosed hh α
    obtain ⟨g, hg⟩ := smooth_has_integerSobolev_data outer h
      (hh.mono (Metric.ball_subset_closedBall.trans hclosed)) hL2all
    have hgclass : RepresentsClassicalDerivatives g h := by
      intro α
      rw [hg α]
      exact (hL2all α).coeFn_toLp
    have hvalue : value g = hL2.toLp h := by
      apply Lp.ext
      have hgvalue : ∀ᵐ x ∂volume.restrict outer.carrier, value g x = h x := by
        simpa only [value, coordinateDerivative_zeroIndex] using hgclass (zeroIndex n r)
      exact Filter.EventuallyEq.trans hgvalue hL2.coeFn_toLp.symm
    obtain ⟨v, hv, hvnorm⟩ := hweak z hz u g (by simpa only [hvalue] using heq)
    refine ⟨v, hv, ?_⟩
    simpa only [smooth_norm outer h g hgclass] using hvnorm
  refine ⟨hsource, ?_⟩
  intro z hz u h U hU hclosed hu hh heq
  have hL2 := coordinateDerivative_memLp_of_closedBall outer hU hclosed hh (zeroIndex n 0)
  simp only [coordinateDerivative_zeroIndex] at hL2
  obtain ⟨w, hw, hweq, hwnorm⟩ := smooth_solution_to_weak outer hcρ D z u
    (hL2.toLp h) U hU hclosed hu (by
      filter_upwards [heq, hL2.coeFn_toLp] with x hx hy
      exact hx.trans hy.symm)
  obtain ⟨v, hv, hvnorm⟩ := hsource z hz w h U hU hclosed hh hL2 hweq
  have hwvalue : ∀ᵐ x ∂volume.restrict outer.carrier, value w x = u x := by
    simpa only [value, coordinateDerivative_zeroIndex] using hw (zeroIndex n 1)
  have hvrep : Represents v u := Filter.EventuallyEq.trans hv
    (Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)) hwvalue)
  refine ⟨v, represents_classical u
    (hu.mono (hsub.trans (Metric.ball_subset_closedBall.trans hclosed)))
    (fun α => (coordinateDerivative_memLp_of_closedBall outer hU hclosed hu α).mono_measure
      (Measure.restrict_mono hsub le_rfl)) v hvrep, ?_⟩
  simpa only [hwnorm] using hvnorm

end DedekindZetaZeroFree.KPContLocalRegularity.SobolevIteration

end

end
