module

public import Mathlib

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalNorm

open MeasureTheory Filter Topology TopologicalSpace

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure LocalBall (n : ℕ) where
  dimension_pos : 0 < n
  center : Space n
  radius : ℝ
  radius_pos : 0 < radius

def LocalBall.carrier {n : ℕ} (B : LocalBall n) : Set (Space n) :=
  Metric.ball B.center B.radius

def LocalBall.toOpens {n : ℕ} (B : LocalBall n) : Opens (Space n) :=
  ⟨B.carrier, Metric.isOpen_ball⟩

abbrev MultiIndex (n k : ℕ) :=
  {α : Fin n → Fin (k + 1) // (∑ i, (α i).val) ≤ k}

def MultiIndex.degree {n k : ℕ} (α : MultiIndex n k) : ℕ :=
  ∑ i, (α.val i).val

def MultiIndex.directions {n k : ℕ} (α : MultiIndex n k) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (α.val i).val i)

def coordinateDerivativeList {n : ℕ} : List (Fin n) → (Space n → ℂ) →
    (Space n → ℂ)
  | [], u => u
  | i :: is, u => fun x =>
      fderiv ℝ (coordinateDerivativeList is u) x (EuclideanSpace.single i 1)

def coordinateDerivative {n k : ℕ} (α : MultiIndex n k)
    (u : Space n → ℂ) : Space n → ℂ :=
  coordinateDerivativeList α.directions u

abbrev BallL2 {n : ℕ} (B : LocalBall n) :=
  Lp ℂ 2 (volume.restrict B.carrier)

def IsWeakDerivative {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u v : BallL2 B) : Prop :=
  ∀ φ : TestFunction B.toOpens ℂ ⊤,
    (∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x) =
      (-1 : ℂ) ^ α.degree * (∫ x in B.carrier, v x * φ x)

structure IntegerSobolev {n : ℕ} (B : LocalBall n) (k : ℕ) where
  derivatives : MultiIndex n k → BallL2 B
  weak_derivatives : ∀ α : MultiIndex n k,
    IsWeakDerivative B α (derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k))
      (derivatives α)

def IntegerSobolev.normSq {n : ℕ} {B : LocalBall n} {k : ℕ}
    (u : IntegerSobolev B k) : ℝ :=
  ∑ α : MultiIndex n k, ‖u.derivatives α‖ ^ 2

def IntegerSobolev.sobolevNorm {n : ℕ} {B : LocalBall n} {k : ℕ}
    (u : IntegerSobolev B k) : ℝ :=
  Real.sqrt u.normSq

theorem IntegerSobolev.sobolevNorm_sq {n : ℕ} {B : LocalBall n} {k : ℕ}
    (u : IntegerSobolev B k) : u.sobolevNorm ^ 2 = u.normSq := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun α _ => sq_nonneg _)

theorem IntegerSobolev.sobolevNorm_sq_eq_integral {n : ℕ}
    {B : LocalBall n} {k : ℕ} (u : IntegerSobolev B k) :
    u.sobolevNorm ^ 2 =
      ∑ α : MultiIndex n k,
        ∫ x in B.carrier, ‖u.derivatives α x‖ ^ (2 : ℕ) := by
  rw [u.sobolevNorm_sq]
  unfold IntegerSobolev.normSq
  apply Finset.sum_congr rfl
  intro α _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem list_smooth {n : ℕ} (B : LocalBall n)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (l : List (Fin n)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
  induction l with
  | nil => exact hu
  | cons i is ih =>
    exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const

private theorem list_global_smooth {n : ℕ} (u : Space n → ℂ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (l : List (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) := by
  induction l with
  | nil => exact hu
  | cons i is ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem list_support {n : ℕ} (u : Space n → ℂ) (l : List (Fin n)) :
    tsupport (coordinateDerivativeList l u) ⊆ tsupport u := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i is ih =>
    exact (tsupport_fderiv_apply_subset ℝ _).trans ih

private theorem list_swap {n : ℕ} (B : LocalBall n) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) (i j : Fin n) (l : List (Fin n)) :
    Set.EqOn (coordinateDerivativeList (i :: j :: l) u)
      (coordinateDerivativeList (j :: i :: l) u) B.carrier := by
  intro x hx
  have hs := (list_smooth B u hu l).contDiffAt (Metric.isOpen_ball.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ (coordinateDerivativeList l u)) x :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  simp only [coordinateDerivativeList, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_const_apply, ContinuousLinearMap.comp_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, zero_add]
  exact (hs.isSymmSndFDerivAt (by simp)).eq _ _

private theorem list_perm {n : ℕ} (B : LocalBall n) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) {l m : List (Fin n)} (h : l.Perm m) :
    Set.EqOn (coordinateDerivativeList l u) (coordinateDerivativeList m u) B.carrier := by
  induction h with
  | nil => intro x hx; rfl
  | cons i h ih =>
    intro x hx
    have hh : coordinateDerivativeList _ u =ᶠ[𝓝 x] coordinateDerivativeList _ u :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) ih
    exact congrArg (fun A => A (EuclideanSpace.single i 1)) (hh.fderiv_eq (𝕜 := ℝ))
  | swap i j l => exact list_swap B u hu j i l
  | trans h h' ih ih' => exact ih.trans ih'

private theorem compact_product_integrable {n : ℕ} (B : LocalBall n) (u g : Space n → ℂ)
    (hu : ContinuousOn u B.carrier) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ B.carrier) : Integrable (fun x => u x * g x) volume := by
  have hp : Continuous (fun x => u x * g x) :=
    (hu.mul hg.continuousOn).continuous_of_tsupport_subset Metric.isOpen_ball
      (tsupport_mul_subset_right.trans hs)
  exact hp.integrable_of_hasCompactSupport hc.mul_left

private theorem first_ibp {n : ℕ} (B : LocalBall n) (u g : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ B.carrier) (i : Fin n) :
    (∫ x in B.carrier, u x * coordinateDerivativeList [i] g x) =
      -(∫ x in B.carrier, coordinateDerivativeList [i] u x * g x) := by
  have hdc : HasCompactSupport (coordinateDerivativeList [i] g) :=
    hc.fderiv_apply ℝ _
  have hds : tsupport (coordinateDerivativeList [i] g) ⊆ B.carrier :=
    (list_support g [i]).trans hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Space n))) (v := EuclideanSpace.single i 1)
    (compact_product_integrable B _ g (list_smooth B u hu [i]).continuousOn hg.continuous hc hs)
    (compact_product_integrable B u _ hu.continuousOn (list_global_smooth g hg [i]).continuous hdc hds)
    (compact_product_integrable B u g hu.continuousOn hg.continuous hc hs)
    (fun x hx => (hu.contDiffAt (Metric.isOpen_ball.mem_nhds (hs hx))).differentiableAt (by simp))
    (fun x _ => (hg.differentiable (by simp)).differentiableAt)
  have hl : (∫ x in B.carrier, u x * coordinateDerivativeList [i] g x) =
      ∫ x, u x * coordinateDerivativeList [i] g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (hds hh))
    simp [hz]
  have hr : (∫ x in B.carrier, coordinateDerivativeList [i] u x * g x) =
      ∫ x, coordinateDerivativeList [i] u x * g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
    simp [hz]
  rw [hl, hr]
  exact h

private theorem list_append {n : ℕ} (l m : List (Fin n)) (u : Space n → ℂ) :
    coordinateDerivativeList (l ++ m) u =
      coordinateDerivativeList l (coordinateDerivativeList m u) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, coordinateDerivativeList, ih]

private theorem list_ibp {n : ℕ} (B : LocalBall n) (u g : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ B.carrier) (l : List (Fin n)) :
    (∫ x in B.carrier, u x * coordinateDerivativeList l g x) =
      (-1 : ℂ) ^ l.length * (∫ x in B.carrier, coordinateDerivativeList l u x * g x) := by
  induction l generalizing u with
  | nil => simp [coordinateDerivativeList]
  | cons i l ih =>
    have hglc : HasCompactSupport (coordinateDerivativeList l g) :=
      hc.of_isClosed_subset (isClosed_tsupport _) (list_support g l)
    have hgls := (list_support g l).trans hs
    have h1 := first_ibp B u (coordinateDerivativeList l g) hu
      (list_global_smooth g hg l) hglc hgls i
    change (∫ x in B.carrier, u x * coordinateDerivativeList [i] (coordinateDerivativeList l g) x) = _
    rw [h1, ih _ (list_smooth B u hu [i])]
    have heq : Set.EqOn (coordinateDerivativeList l (coordinateDerivativeList [i] u))
        (coordinateDerivativeList (i :: l) u) B.carrier := by
      rw [← list_append]
      exact list_perm B u hu (List.perm_append_comm.trans (by simp))
    have hint : (∫ x in B.carrier, coordinateDerivativeList l (coordinateDerivativeList [i] u) x * g x) =
        ∫ x in B.carrier, coordinateDerivativeList (i :: l) u x * g x := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      exact congrArg (fun z : ℂ => z * g x) (heq hx)
    rw [hint, List.length_cons, pow_succ]
    ring

private theorem directions_length {n k : ℕ} (α : MultiIndex n k) :
    α.directions.length = α.degree := by
  simp [MultiIndex.directions, MultiIndex.degree, List.length_flatMap,
    ← List.ofFn_eq_map, List.sum_ofFn]

theorem smooth_has_integerSobolev_data {n k : ℕ} (B : LocalBall n)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (hL2 : ∀ α : MultiIndex n k,
      MemLp (coordinateDerivative α u) 2 (volume.restrict B.carrier)) :
    ∃ v : IntegerSobolev B k,
      ∀ α : MultiIndex n k,
        v.derivatives α = (hL2 α).toLp (coordinateDerivative α u) := by
  let d : MultiIndex n k → BallL2 B := fun α => (hL2 α).toLp (coordinateDerivative α u)
  have hw : ∀ α : MultiIndex n k,
      IsWeakDerivative B α (d (⟨fun _ => 0, by simp⟩ : MultiIndex n k)) (d α) := by
    intro α φ
    have hzero : coordinateDerivative (⟨fun _ => 0, by simp⟩ : MultiIndex n k) u = u := by
      have hnil : ∀ l : List (Fin n), l.flatMap (fun _ => ([] : List (Fin n))) = [] := by
        intro l
        induction l with
        | nil => rfl
        | cons i l ih => simpa using ih
      simp [coordinateDerivative, MultiIndex.directions, coordinateDerivativeList, hnil]
    have h0 : (fun x => d (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) =ᵐ[volume.restrict B.carrier] u := by
      simpa only [d, hzero] using (hL2 (⟨fun _ => 0, by simp⟩ : MultiIndex n k)).coeFn_toLp
    have hα : (fun x => d α x) =ᵐ[volume.restrict B.carrier] coordinateDerivative α u :=
      (hL2 α).coeFn_toLp
    have hl : (∫ x in B.carrier, d (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x *
        coordinateDerivative α (fun y => φ y) x) =
        ∫ x in B.carrier, u x * coordinateDerivative α (fun y => φ y) x := by
      apply integral_congr_ae
      filter_upwards [h0] with x hx
      rw [hx]
    have hr : (∫ x in B.carrier, d α x * φ x) =
        ∫ x in B.carrier, coordinateDerivative α u x * φ x := by
      apply integral_congr_ae
      filter_upwards [hα] with x hx
      rw [hx]
    rw [hl, hr]
    simpa only [coordinateDerivative, directions_length] using
      list_ibp B u (fun y => φ y) hu φ.contDiff φ.hasCompactSupport φ.tsupport_subset α.directions
  exact ⟨⟨d, hw⟩, fun _ => rfl⟩

abbrev CompactJets {n : ℕ} (K : Set (Space n)) (m : ℕ) :=
  MultiIndex n m → ContinuousMap K ℂ

 theorem coordinateDerivativeList_smooth {n : ℕ} (B : LocalBall n)
    (u : Space n → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier)
    (l : List (Fin n)) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivativeList l u) B.carrier := by
  induction l with
  | nil => exact hu
  | cons i is ih =>
    exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const

def compactJet {n m : ℕ} (B : LocalBall n) (K : Set (Space n))
    (hK : K ⊆ B.carrier) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) : CompactJets K m := by
  intro α
  exact ⟨fun x => coordinateDerivative α u x,
    ((coordinateDerivativeList_smooth B u hu α.directions).continuousOn.mono hK).restrict⟩

def jetMaxNorm {n m : ℕ} {K : Set (Space n)} (hcompact : IsCompact K)
    (j : CompactJets K m) : ℝ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  exact ‖j‖

def compactJetSeminorm {n : ℕ} (m : ℕ) (B : LocalBall n) (K : Set (Space n))
    (hcompact : IsCompact K) (hK : K ⊆ B.carrier) (u : Space n → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u B.carrier) : ℝ :=
  jetMaxNorm hcompact (compactJet (m := m) B K hK u hu)

def SmoothPowerSeriesOn {n : ℕ} (B : LocalBall n) (z₀ : ℂ) (ρ : ℝ)
    (coeff : ℕ → Space n → ℂ) (f : ℂ → Space n → ℂ) : Prop :=
  (∀ q, ContDiffOn ℝ (⊤ : ℕ∞) (coeff q) B.carrier) ∧
  (∀ z ∈ Metric.ball z₀ ρ, ContDiffOn ℝ (⊤ : ℕ∞) (f z) B.carrier) ∧
  ∀ (K : Set (Space n)), IsCompact K → K ⊆ B.carrier →
    ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r → r < ρ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
        ∀ α : MultiIndex n m, ∀ x : K,
          ‖coordinateDerivative α
              (fun y => (∑ q ∈ Finset.range M, (z - z₀) ^ q * coeff q y) - f z y) x‖ < ε

def SmoothCompactOpenHolomorphicOn {n : ℕ} (B : LocalBall n)
    (f : ℂ → Space n → ℂ) (U : Set ℂ) : Prop :=
  ∀ z₀ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₀ ρ ⊆ U ∧
    ∃ coeff : ℕ → Space n → ℂ, SmoothPowerSeriesOn B z₀ ρ coeff f

end DedekindZetaZeroFree.KPContLocalNorm

end
