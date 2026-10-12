module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets

open MeasureTheory KPContLocalNorm

private theorem mixed_smooth {n : ℕ} (l : List (Fin n)) {f : Space n → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem mixed_support {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    tsupport (coordinateDerivativeList l f) ⊆ tsupport f := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih =>
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

private theorem mixed_append {n : ℕ} (l k : List (Fin n)) (f : Space n → ℂ) :
    coordinateDerivativeList (l ++ k) f =
      coordinateDerivativeList l (coordinateDerivativeList k f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, coordinateDerivativeList, ih]

private theorem mixed_perm {n : ℕ} {l k : List (Fin n)} (hp : l.Perm k)
    {f : Space n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    coordinateDerivativeList l f = coordinateDerivativeList k f := by
  induction hp with
  | nil => rfl
  | cons i hp ih => simp only [coordinateDerivativeList, ih]
  | swap i j l =>
    have hs := mixed_smooth l hf
    funext x
    simp only [coordinateDerivativeList]
    have hd : Differentiable ℝ (fderiv ℝ (coordinateDerivativeList l f)) :=
      (hs.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiable (by norm_num)
    simpa [fderiv_clm_apply (hd x) (differentiableAt_const _)] using
      (hs.contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp)).eq
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  | trans hp hq ih ij => exact ih.trans ij

private theorem directions_count {n k : ℕ} (α : MultiIndex n k) (i : Fin n) :
    α.directions.count i = (α.val i).val := by
  rw [MultiIndex.directions, List.count_flatMap, ← List.sum_toFinset _ (List.nodup_finRange n)]
  simp [Function.comp_def, List.count_replicate]

private theorem full_mixed_index {n m : ℕ} (hn : 0 < n) (α : MultiIndex n m)
    {w : Space n → ℂ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ∃ β : MultiIndex n (m + n),
      coordinateDerivativeList (List.finRange n) (coordinateDerivative α w) =
        coordinateDerivative β w := by
  classical
  let β : MultiIndex n (m + n) := ⟨fun i => ⟨(α.val i).val + 1, by
    have hi := (α.val i).isLt
    omega⟩, by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
      exact Nat.add_le_add_right α.property n⟩
  refine ⟨β, ?_⟩
  rw [coordinateDerivative, ← mixed_append]
  apply mixed_perm _ hw
  apply List.perm_iff_count.mpr
  intro i
  simp only [List.count_append, List.count_finRange, directions_count]
  change 1 + (α.val i).val = (α.val i).val + 1
  omega

private theorem compact_l1_l2 {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {g : Space n → ℂ} (hg : Continuous g) (hsub : tsupport g ⊆ K) :
    (∫ x, ‖g x‖) ≤ Real.sqrt (volume.real K) * Real.sqrt (∫ x, ‖g x‖ ^ 2) := by
  have hs : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport g) hsub
  have hzero (x) (hx : x ∉ K) : g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsub hx'))
  have heq : (∫ x in K, ‖g x‖) = ∫ x, ‖g x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
  have heq2 : (∫ x in K, ‖g x‖ ^ 2) = ∫ x, ‖g x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict K)
    Real.HolderConjugate.two_two
    (f := fun _ : Space n => (1 : ℝ)) (g := fun x => ‖g x‖)
    (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (memLp_const 1) ((hg.memLp_of_hasCompactSupport hs).norm.restrict K)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [Real.rpow_two, heq, heq2, integral_const, measureReal_def] using hh

theorem full_mixed_integral_le_sobolev {n : ℕ} (hn : 0 < n)
    (lower upper : Fin n → ℝ) (hbox : ∀ i, lower i < upper i) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Space n → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      tsupport w ⊆ {x | ∀ i, lower i < x i ∧ x i < upper i} →
      ∀ α : MultiIndex n m,
        (∫ y, ‖coordinateDerivativeList (List.finRange n)
          (coordinateDerivative α w) y‖) ≤
        C * Real.sqrt (∑ β : MultiIndex n (m + n),
          ∫ y, ‖coordinateDerivative β w y‖ ^ 2) := by
  classical
  let K : Set (Space n) := {x | ∀ i, lower i ≤ x i ∧ x i ≤ upper i}
  have hK : IsCompact K := by
    let e := EuclideanSpace.equiv (Fin n) ℝ
    have hc : IsCompact {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (lower i) (upper i)} :=
      isCompact_pi_infinite (fun _ => isCompact_Icc)
    convert hc.image e.symm.continuous using 1
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  refine ⟨Real.sqrt (volume.real K) + 1, by positivity, ?_⟩
  intro w hw hcomp hsub α
  obtain ⟨β, hβ⟩ := full_mixed_index hn α hw
  rw [hβ]
  have hd := mixed_smooth β.directions hw
  have hs : tsupport (coordinateDerivative β w) ⊆ K := by
    intro x hx
    have hx' := hsub (mixed_support β.directions w hx)
    exact fun i => ⟨(hx' i).1.le, (hx' i).2.le⟩
  have hle : (∫ y, ‖coordinateDerivative β w y‖ ^ 2) ≤
      ∑ γ : MultiIndex n (m + n), ∫ y, ‖coordinateDerivative γ w y‖ ^ 2 := by
    apply Finset.single_le_sum (f := fun γ : MultiIndex n (m + n) =>
      ∫ y, ‖coordinateDerivative γ w y‖ ^ 2) _ (Finset.mem_univ β)
    intro γ _
    exact integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∫ y, ‖coordinateDerivative β w y‖) ≤
        Real.sqrt (volume.real K) * Real.sqrt (∫ y, ‖coordinateDerivative β w y‖ ^ 2) :=
      compact_l1_l2 hK hd.continuous hs
    _ ≤ (Real.sqrt (volume.real K) + 1) *
        Real.sqrt (∑ γ : MultiIndex n (m + n), ∫ y, ‖coordinateDerivative γ w y‖ ^ 2) := by
      gcongr
      linarith

end DedekindZetaZeroFree.KPLocalCubeSobolevJets

end
