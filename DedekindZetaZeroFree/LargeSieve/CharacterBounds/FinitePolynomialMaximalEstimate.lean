module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.PrefixMaximalInequality

@[expose] public section

namespace DedekindZetaZeroFree.DetectorMaximalFiniteHeight
noncomputable section
open scoped BigOperators
open MeasureTheory

def maxSq {κ : Type*} [Fintype κ] [Nonempty κ] (P : κ → ℝ → ℂ) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => ‖P k t‖ ^ 2)

lemma maxSq_continuous {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ → ℝ → ℂ) (hP : ∀ k, Continuous (P k)) : Continuous (maxSq P) := by
  apply Continuous.finset_sup'_apply
  intro k _
  exact (hP k).norm.pow 2

lemma le_maxSq {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ → ℝ → ℂ) (t : ℝ) (k : κ) : ‖P k t‖ ^ 2 ≤ maxSq P t := by
  exact Finset.le_sup' (f := fun k => ‖P k t‖ ^ 2) (Finset.mem_univ k)

lemma maxSq_nonneg {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ → ℝ → ℂ) (t : ℝ) : 0 ≤ maxSq P t :=
  (sq_nonneg _).trans (le_maxSq P t (Classical.arbitrary κ))

theorem maxSq_sobolev {κ : Type*} [Fintype κ] [Nonempty κ]
    (P : κ → ℝ → ℂ) (hP : ∀ k, ContDiff ℝ 1 (P k))
    (T : ℝ) (hT : 0 ≤ T) :
    sSup (maxSq P '' Set.Icc (-T) T) ≤
      2 * ∫ t in (-T - 1)..(T + 1),
        (maxSq P t + maxSq (fun k => deriv (P k)) t) := by
  let M := maxSq P
  let D := maxSq (fun k => deriv (P k))
  let H := fun t => M t + D t
  have hMc : Continuous M := maxSq_continuous P (fun k => (hP k).continuous)
  have hDc : Continuous D := maxSq_continuous _
    (fun k => (hP k).continuous_deriv (by norm_num))
  have hHc : Continuous H := hMc.add hDc
  have hHnonneg : ∀ x, 0 ≤ H x := fun x =>
    add_nonneg (maxSq_nonneg P x) (maxSq_nonneg _ x)
  have hbound : ∀ k x, ‖deriv (fun t => ‖P k t‖ ^ 2) x‖ ≤ H x := by
    intro k x
    have hd : Differentiable ℝ (P k) := (hP k).differentiable (by norm_num)
    rw [(hd x).hasDerivAt.norm_sq.deriv]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hi := abs_real_inner_le_norm (P k x) (deriv (P k) x)
    change |(deriv (P k) x * (starRingEnd ℂ) (P k x)).re| ≤
      ‖P k x‖ * ‖deriv (P k) x‖ at hi
    have hp := le_maxSq P x k
    have hd' := le_maxSq (fun k => deriv (P k)) x k
    dsimp [H, M, D]
    nlinarith [sq_nonneg (‖P k x‖ - ‖deriv (P k) x‖)]
  have hI : IntervalIntegrable H volume (-T - 1) (T + 1) :=
    hHc.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-T) T, M t ≤
      2 * ∫ x in (-T - 1)..(T + 1), H x := by
    intro t ht
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k => ‖P k t‖ ^ 2)
    have hkt : M t = ‖P k t‖ ^ 2 := hk
    let I : ℝ := ∫ x in (-T - 1)..(T + 1), H x
    have hx : ∀ x ∈ Set.Icc t (t + 1), M t ≤ M x + I := by
      intro x hx
      have hd : Differentiable ℝ (P k) := (hP k).differentiable (by norm_num)
      have he := norm_sub_le_integral_of_norm_deriv_le_of_le hx.1
        ((hP k).continuous.norm.pow 2).continuousOn
        (hd.norm_sq ℂ).differentiableOn
        (Filter.Eventually.of_forall (fun u _ => hbound k u))
        (hHc.intervalIntegrable t x)
      have hm : (∫ u in t..x, H u) ≤ I :=
        intervalIntegral.integral_mono_interval (by linarith [ht.1]) hx.1
          (by linarith [hx.2, ht.2])
          (Filter.Eventually.of_forall hHnonneg) hI
      have ha : ‖P k t‖ ^ 2 - ‖P k x‖ ^ 2 ≤
          ‖‖P k x‖ ^ 2 - ‖P k t‖ ^ 2‖ := by
        rw [Real.norm_eq_abs]
        linarith [neg_le_abs (‖P k x‖ ^ 2 - ‖P k t‖ ^ 2)]
      change ‖‖P k x‖ ^ 2 - ‖P k t‖ ^ 2‖ ≤ ∫ u in t..x, H u at he
      have hl := le_maxSq P x k
      rw [hkt]
      dsimp [M] at hl ⊢
      linarith
    have havg := intervalIntegral.integral_mono_on (by linarith : t ≤ t + 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M t)
        volume t (t + 1))
      ((hMc.add continuous_const).intervalIntegrable t (t + 1)) hx
    have hm : (∫ x in t..(t + 1), M x) ≤ I := by
      calc
        _ ≤ ∫ x in t..(t + 1), H x :=
          intervalIntegral.integral_mono_on (by linarith)
            (hMc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)
            (fun x _ => by dsimp [H]; exact le_add_of_nonneg_right (maxSq_nonneg _ x))
        _ ≤ I := intervalIntegral.integral_mono_interval (by linarith [ht.1])
          (by linarith) (by linarith [ht.2])
          (Filter.Eventually.of_forall hHnonneg) hI
    change (∫ u in t..(t + 1), M t) ≤ (∫ u in t..(t + 1), M u + I) at havg
    rw [intervalIntegral.integral_add (hMc.intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const] at havg
    simp only [add_sub_cancel_left, one_smul] at havg
    dsimp [I] at hm havg
    linarith
  apply csSup_le
  · exact ⟨M 0, 0, ⟨by linarith, hT⟩, rfl⟩
  · rintro y ⟨t, ht, rfl⟩
    exact hpoint t ht

def phase (q t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * (Real.log q : ℂ))

lemma phase_norm (q t : ℝ) : ‖phase q t‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_contDiff (q : ℝ) : ContDiff ℝ 1 (phase q) := by
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

lemma phase_hasDerivAt (q t : ℝ) :
    HasDerivAt (phase q) (phase q t * (-Complex.I * (Real.log q : ℂ))) t := by
  have hlin : HasDerivAt (fun x : ℝ =>
      -Complex.I * (x : ℂ) * (Real.log q : ℂ))
      (-Complex.I * (Real.log q : ℂ)) t := by
    convert (((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).comp_ofReal).mul_const
      (Real.log q : ℂ) using 1 <;> simp only [id_eq, mul_one]
  exact hlin.cexp

lemma prefix_contDiff {m : ℕ} (a b : Fin m → ℂ) (q : Fin m → ℝ)
    (l : Fin (m+1)) :
    ContDiff ℝ 1 (fun t => detector_prefixSum a (fun k => b k * phase (q k) t) l) := by
  apply ContDiff.sum
  intro k _
  by_cases h : k.val < l.val
  · simp only [if_pos h]
    exact contDiff_const.mul (contDiff_const.mul (phase_contDiff (q k)))
  · simp only [if_neg h]
    exact contDiff_const

lemma prefix_deriv {m : ℕ} (a b : Fin m → ℂ) (q : Fin m → ℝ)
    (l : Fin (m+1)) (t : ℝ) :
    deriv (fun t => detector_prefixSum a (fun k => b k * phase (q k) t) l) t =
      detector_prefixSum a
        (fun k => ((-Complex.I * (Real.log (q k) : ℂ)) * b k) * phase (q k) t) l := by
  apply HasDerivAt.deriv
  unfold detector_prefixSum
  apply HasDerivAt.fun_sum
  intro k _
  by_cases h : k.val < l.val
  · simp only [if_pos h]
    convert (phase_hasDerivAt (q k) t).const_mul (a k * b k) using 1
    · funext x; ring
    · ring
  · simp only [if_neg h]
    exact hasDerivAt_const t 0

theorem finite_polynomial_maximal :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (ι : Type) [Fintype ι]
      (A : ι → Fin m → ℂ) (q : Fin m → ℝ) (K L T : ℝ),
      0 ≤ K → 0 ≤ L → 0 ≤ T →
      (∀ k, |Real.log (q k)| ≤ L) →
      (∀ c : Fin m → ℂ, (∑ i, ‖∑ k, A i k * c k‖ ^ 2) ≤ K * ∑ k, ‖c k‖ ^ 2) →
      ∀ b : Fin m → ℂ,
      (∑ i, sSup ((fun t => detector_prefixMaxSq (A i)
        (fun k => b k * phase (q k) t)) '' Set.Icc (-T) T)) ≤
      C * (T + 1) * K * (1 + Real.log (m + 1)) ^ 2 * (1 + L ^ 2) *
        ∑ k, ‖b k‖ ^ 2 := by
  obtain ⟨C₁, hC₁, hprefix⟩ := detector_prefix_maximal
  refine ⟨4 * C₁, by positivity, ?_⟩
  intro m ι _ A q K L T hK hL hT hq hop b
  let P := fun i (l : Fin (m+1)) t =>
    detector_prefixSum (A i) (fun k => b k * phase (q k) t) l
  let H := fun i t => maxSq (P i) t + maxSq (fun l => deriv (P i l)) t
  have hc : ∀ i, Continuous (H i) := by
    intro i
    exact (maxSq_continuous (P i) (fun l => (prefix_contDiff _ _ _ l).continuous)).add
      (maxSq_continuous _ (fun l => (prefix_contDiff _ _ _ l).continuous_deriv (by norm_num)))
  have hheight := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    maxSq_sobolev (P i) (fun l => prefix_contDiff _ _ _ l) T hT)
  change (∑ i, sSup ((fun t => detector_prefixMaxSq (A i)
      (fun k => b k * phase (q k) t)) '' Set.Icc (-T) T)) ≤
    ∑ i, 2 * ∫ t in (-T-1)..(T+1), H i t at hheight
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum
    (fun i _ => (hc i).intervalIntegrable _ _)] at hheight
  let E := ∑ k, ‖b k‖ ^ 2
  let R := C₁ * K * (1 + Real.log (m+1)) ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoint : ∀ t, (∑ i, H i t) ≤ R * (1 + L ^ 2) * E := by
    intro t
    have he : (∑ k, ‖b k * phase (q k) t‖ ^ 2) = E := by
      simp [phase_norm, norm_mul, E]
    have hb := hprefix m ι A K hK hop (fun k => b k * phase (q k) t)
    rw [he] at hb
    let d := fun k => (-Complex.I * (Real.log (q k) : ℂ)) * b k
    have hd := hprefix m ι A K hK hop (fun k => d k * phase (q k) t)
    have hde : (∑ k, ‖d k * phase (q k) t‖ ^ 2) ≤ L ^ 2 * E := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      dsimp [d]
      simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, one_mul, phase_norm, mul_one, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (sq_le_sq₀ (abs_nonneg _) hL |>.mpr (hq k)) (sq_nonneg _)
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hde hR)
    have hm : (∑ i, H i t) =
        (∑ i, detector_prefixMaxSq (A i) (fun k => b k * phase (q k) t)) +
        (∑ i, detector_prefixMaxSq (A i) (fun k => d k * phase (q k) t)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [H, P, maxSq, detector_prefixMaxSq]
      congr 2
      funext l
      rw [prefix_deriv]
    rw [hm]
    change _ ≤ R * E at hb
    change _ ≤ R * (L ^ 2 * E) at hd'
    nlinarith
  have hi := intervalIntegral.integral_mono_on (by linarith : -T-1 ≤ T+1)
    ((continuous_finset_sum _ (fun i _ => hc i)).intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => R * (1+L^2) * E)
      volume (-T-1) (T+1)) (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const] at hi
  have hfinal := hheight.trans (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2))
  dsimp [R, E] at hfinal
  convert hfinal using 1 <;> ring

theorem finite_polynomial_maximal_universe :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (ι : Type*) [Fintype ι]
      (A : ι → Fin m → ℂ) (q : Fin m → ℝ) (K L T : ℝ),
      0 ≤ K → 0 ≤ L → 0 ≤ T →
      (∀ k, |Real.log (q k)| ≤ L) →
      (∀ c : Fin m → ℂ, (∑ i, ‖∑ k, A i k * c k‖ ^ 2) ≤ K * ∑ k, ‖c k‖ ^ 2) →
      ∀ b : Fin m → ℂ,
      (∑ i, sSup ((fun t => detector_prefixMaxSq (A i)
        (fun k => b k * phase (q k) t)) '' Set.Icc (-T) T)) ≤
      C * (T + 1) * K * (1 + Real.log (m + 1)) ^ 2 * (1 + L ^ 2) *
        ∑ k, ‖b k‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := finite_polynomial_maximal
  refine ⟨C, hC, ?_⟩
  intro m ι _ A q K L T hK hL hT hq hop b
  let e := (Fintype.equivFin ι).symm
  have hop' : ∀ c : Fin m → ℂ,
      (∑ j : Fin (Fintype.card ι), ‖∑ k, A (e j) k * c k‖ ^ 2) ≤
        K * ∑ k, ‖c k‖ ^ 2 := by
    intro c
    rw [e.sum_comp (fun i => ‖∑ k, A i k * c k‖ ^ 2)]
    exact hop c
  have hh := h m (Fin (Fintype.card ι)) (fun j => A (e j)) q K L T hK hL hT hq hop' b
  rw [e.sum_comp (fun i => sSup ((fun t => detector_prefixMaxSq (A i)
    (fun k => b k * phase (q k) t)) '' Set.Icc (-T) T))] at hh
  exact hh

end
end DedekindZetaZeroFree.DetectorMaximalFiniteHeight
