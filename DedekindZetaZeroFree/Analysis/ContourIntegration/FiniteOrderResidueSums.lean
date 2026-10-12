module

public import DedekindZetaZeroFree.Analysis.ContourIntegration.HigherPrincipalParts
public import DedekindZetaZeroFree.Analysis.ContourIntegration.SubquadraticGrowthAndGaussianRegulation

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma sum_Icc_one_eq (f : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, f k
      = (∑ k ∈ Finset.Icc 2 m, f k) + (if m = 0 then 0 else f 1) := by
  rcases m with _ | m
  · simp
  · rw [if_neg (Nat.succ_ne_zero m)]
    have h : Finset.Icc 1 (m + 1) = insert 1 (Finset.Icc 2 (m + 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]

private lemma differentiableOn_rational_principal (R : ℂ) (p : ℝ) (k : ℕ) :
    DifferentiableOn ℂ (fun s : ℂ => R / (s - (p : ℂ)) ^ k) {s | s ≠ (p : ℂ)} := by
  intro s hs
  have hne : s - (p : ℂ) ≠ 0 := sub_ne_zero.mpr hs
  exact ((differentiableAt_const R).div ((differentiableAt_id.sub_const (p : ℂ)).pow k)
    (pow_ne_zero k hne)).differentiableWithinAt

private theorem verticalIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (c : ℝ) (hf : ∀ i ∈ s, Complex.VerticalIntegrable (f i) c) :
    verticalIntegral c (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, verticalIntegral c (f i) := by
  classical
  revert hf
  induction s using Finset.induction with
  | empty =>
    intro _
    simp [verticalIntegral]
  | insert a s ha ih =>
    intro hf
    have hfa : Complex.VerticalIntegrable (f a) c := hf a (Finset.mem_insert_self a s)
    have hfs : Complex.VerticalIntegrable (fun z => ∑ i ∈ s, f i z) c :=
      integrable_finsetSum s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsplit : (fun z => ∑ i ∈ insert a s, f i z)
        = (fun z => f a z + ∑ i ∈ s, f i z) := by
      funext z; rw [Finset.sum_insert ha]
    rw [hsplit, verticalIntegral_add c (f a) (fun z => ∑ i ∈ s, f i z) hfa hfs,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

theorem verticalIntegral_sub_eq_sum_residues_of_finite_order
    {a b : ℝ} (hab : a < b) (S : Finset ℝ)
    (hp_strip : ∀ p ∈ S, a < p ∧ p < b)
    (n : S → ℕ) (C : S → ℕ → ℂ)
    (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hstrip : {s : ℂ | s.re ∈ Set.Icc a b} ⊆ U)
    (hF_holo : DifferentiableOn ℂ F
      (U \ Set.range (fun p : S => (p.val : ℂ))))
    (hregular : ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ s ∈ U, (∀ p : S, s ≠ (p.val : ℂ)) →
        G s = F s - ∑ p : S, ∑ k ∈ Finset.Icc 1 (n p),
          C p k / (s - (p.val : ℂ)) ^ k)
    (ha : Complex.VerticalIntegrable F a MeasureTheory.volume)
    (hb : Complex.VerticalIntegrable F b MeasureTheory.volume)
    (hgrowth : ∃ C₀ A : ℝ, 0 ≤ C₀ ∧ 0 ≤ A ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C₀ * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ))) :
    verticalIntegral b F - verticalIntegral a F =
      ∑ p : S, if n p = 0 then 0 else C p 1 := by
  classical
  have hcard : Fintype.card ↥S = S.card := by simp [Finset.card_attach]
  let e : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq hcard
  let p : Fin S.card → ℝ := fun j => (e.symm j).val
  let R : Fin S.card → ℂ := fun j => if n (e.symm j) = 0 then 0 else C (e.symm j) 1
  let H : ℂ → ℂ := fun s => ∑ q : ↥S, ∑ k ∈ Finset.Icc 2 (n q),
      C q k / (s - (q.val : ℂ)) ^ k
  let G : ℂ → ℂ := fun s => F s - H s
  have hp_inj : Function.Injective p := by
    intro j₁ j₂ h
    exact e.symm.injective (Subtype.ext h)
  have hp_mem : ∀ j, p j ∈ Set.Ioo a b := by
    intro j
    exact hp_strip (e.symm j).val (e.symm j).property
  have hrange : Set.range (fun j : Fin S.card => (p j : ℂ))
      = Set.range (fun q : ↥S => (q.val : ℂ)) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e q, by simp [p, Equiv.symm_apply_apply]⟩

  have hinner_int (c : ℝ) (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) (q : ↥S) :
      Complex.VerticalIntegrable (fun z => ∑ k ∈ Finset.Icc 2 (n q),
        C q k / (z - (q.val : ℂ)) ^ k) c :=
    integrable_finsetSum (Finset.Icc 2 (n q))
      (fun k hk => verticalIntegrable_higher_principal_part (C q k) (hc q)
        (Finset.mem_Icc.mp hk).1)
  have hH_int_of (c : ℝ) (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) :
      Complex.VerticalIntegrable H c := by
    show Integrable (fun y : ℝ => H (c + y * Complex.I)) volume
    simp only [H]
    exact integrable_finsetSum Finset.univ (fun q _ => hinner_int c hc q)
  have hinner_vert_zero (c : ℝ) (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) (q : ↥S) :
      verticalIntegral c (fun z => ∑ k ∈ Finset.Icc 2 (n q),
        C q k / (z - (q.val : ℂ)) ^ k) = 0 := by
    rw [verticalIntegral_finset_sum (Finset.Icc 2 (n q))
      (fun k z => C q k / (z - (q.val : ℂ)) ^ k) c
      (fun k hk => verticalIntegrable_higher_principal_part (C q k) (hc q)
        (Finset.mem_Icc.mp hk).1)]
    exact Finset.sum_eq_zero (fun k hk => verticalIntegral_higher_principal_part_eq_zero
      (C q k) (hc q) (Finset.mem_Icc.mp hk).1)
  have hH_vert_zero (c : ℝ) (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) :
      verticalIntegral c H = 0 := by
    have h1 : verticalIntegral c H = ∑ q : ↥S, verticalIntegral c
        (fun z => ∑ k ∈ Finset.Icc 2 (n q), C q k / (z - (q.val : ℂ)) ^ k) := by
      show verticalIntegral c (fun z => ∑ i ∈ Finset.univ,
          (fun q z => ∑ k ∈ Finset.Icc 2 (n q), C q k / (z - (q.val : ℂ)) ^ k) i z) = _
      exact verticalIntegral_finset_sum Finset.univ
        (fun q z => ∑ k ∈ Finset.Icc 2 (n q), C q k / (z - (q.val : ℂ)) ^ k) c
        (fun q _ => hinner_int c hc q)
    rw [h1]
    exact Finset.sum_eq_zero (fun q _ => hinner_vert_zero c hc q)

  have hH_diff : DifferentiableOn ℂ H (U \ Set.range (fun q : ↥S => (q.val : ℂ))) := by
    simp only [H]
    refine DifferentiableOn.fun_sum (u := Finset.univ)
      (A := fun q s => ∑ k ∈ Finset.Icc 2 (n q), C q k / (s - (q.val : ℂ)) ^ k) ?_
    intro q _
    refine DifferentiableOn.fun_sum (u := Finset.Icc 2 (n q))
      (A := fun k s => C q k / (s - (q.val : ℂ)) ^ k) ?_
    intro k _
    exact (differentiableOn_rational_principal (C q k) q.val k).mono (by
      intro s hs
      simp only [Set.mem_setOf_eq]
      exact fun h => hs.2 ⟨q, h.symm⟩)
  have hG_diff : DifferentiableOn ℂ G (U \ Set.range (fun j : Fin S.card => (p j : ℂ))) := by
    have h : DifferentiableOn ℂ G (U \ Set.range (fun q : ↥S => (q.val : ℂ))) := by
      simp only [G]
      exact hF_holo.sub hH_diff
    rwa [← hrange] at h

  have hG_int (c : ℝ) (hFc : Complex.VerticalIntegrable F c)
      (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) : Complex.VerticalIntegrable G c := by
    have hHint : Complex.VerticalIntegrable H c := hH_int_of c hc
    show Integrable (fun y : ℝ => G (c + y * Complex.I)) volume
    simp only [G]
    exact hFc.sub hHint
  have hG_vert_eq (c : ℝ) (hFc : Complex.VerticalIntegrable F c)
      (hc : ∀ q : ↥S, c ≠ (q.val : ℝ)) :
      verticalIntegral c G = verticalIntegral c F := by
    have hHint : Complex.VerticalIntegrable H c := hH_int_of c hc
    have hsplit : verticalIntegral c G = verticalIntegral c F - verticalIntegral c H := by
      show (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, G (c + t * Complex.I) = _
      rw [show (fun t : ℝ => G (c + t * Complex.I))
          = (fun t : ℝ => F (c + t * Complex.I) - H (c + t * Complex.I)) from by
        funext t; simp only [G]]
      rw [verticalIntegral, verticalIntegral, ← mul_sub, integral_sub]
      · exact hFc
      · exact hHint
    rw [hsplit, hH_vert_zero c hc, sub_zero]

  have hgrowthG : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (σ t : ℝ), σ ∈ Set.Icc a b → 1 ≤ |t| →
        ‖G ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := by
    obtain ⟨C₀, A, hC₀, hA, hgr⟩ := hgrowth
    let K : ℝ := ∑ q : ↥S, ∑ k ∈ Finset.Icc 2 (n q), ‖C q k‖
    have hKnn : 0 ≤ K := by
      simp only [K]
      exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
    refine ⟨C₀ + K, A, add_nonneg hC₀ hKnn, hA, ?_⟩
    intro σ t hσ ht
    have hsre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    have hsim : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have hexp1 : 1 ≤ Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := by
      rw [Real.one_le_exp_iff]
      exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
    have hFs : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C₀ * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := hgr σ t hσ ht
    have hstep : ∀ q : ↥S, ‖∑ k ∈ Finset.Icc 2 (n q),
        C q k / (((σ : ℂ) + (t : ℂ) * Complex.I) - (q.val : ℂ)) ^ k‖
        ≤ ∑ k ∈ Finset.Icc 2 (n q), ‖C q k‖ := by
      intro q
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k hk => ?_))
      have hle := norm_higher_principal_part_le_on_strip (C q k) q.val
        (Finset.mem_Icc.mp hk).1 (a := a) (b := b)
        (s := ((σ : ℂ) + (t : ℂ) * Complex.I))
        (by rw [hsre]; exact hσ) (by rw [hsim]; exact ht)
      simpa using hle
    have hHs : ‖H ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K := by
      simp only [H, K]
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun q _ => hstep q))
    have hGle : ‖G ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C₀ * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) + K := by
      have := norm_sub_le (F ((σ : ℂ) + (t : ℂ) * Complex.I))
        (H ((σ : ℂ) + (t : ℂ) * Complex.I))
      simp only [G]
      exact le_trans this (add_le_add hFs hHs)
    have hKexp : K ≤ K * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) :=
      le_mul_of_one_le_right hKnn hexp1
    calc ‖G ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C₀ * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) + K := hGle
      _ ≤ C₀ * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ))
            + K * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := add_le_add le_rfl hKexp
      _ = (C₀ + K) * Real.exp (A * (1 + |t|) ^ (3 / 2 : ℝ)) := by ring

  obtain ⟨Freg, hFreg_diff, hFreg_eq⟩ := hregular
  have hregular' : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ s ∈ U, (∀ j : Fin S.card, s ≠ (p j : ℂ)) →
        g s = G s - ∑ j : Fin S.card, R j / (s - (p j : ℂ)) := by
    refine ⟨Freg, hFreg_diff, ?_⟩
    intro s hs hsp
    have hsne : ∀ q : ↥S, s ≠ (q.val : ℂ) := by
      intro q
      have := hsp (e q)
      simpa [p, Equiv.symm_apply_apply] using this
    have hRfun : (∑ j : Fin S.card, R j / (s - (p j : ℂ)))
        = ∑ q : ↥S, R (e q) / (s - (q.val : ℂ)) := by
      rw [← Equiv.sum_comp (e := e.symm)
        (g := fun q : ↥S => R (e q) / (s - (q.val : ℂ)))]
      exact Finset.sum_congr rfl (fun j _ => by simp [p, Equiv.apply_symm_apply])
    have hP : (∑ q : ↥S, ∑ k ∈ Finset.Icc 1 (n q), C q k / (s - (q.val : ℂ)) ^ k)
        = H s + ∑ q : ↥S, R (e q) / (s - (q.val : ℂ)) := by
      have hH : H s = ∑ q : ↥S, ∑ k ∈ Finset.Icc 2 (n q),
          C q k / (s - (q.val : ℂ)) ^ k := rfl
      rw [hH, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [sum_Icc_one_eq (fun k => C q k / (s - (q.val : ℂ)) ^ k) (n q)]
      simp only [R, Equiv.symm_apply_apply]
      by_cases hn : n q = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn, pow_one]
    rw [hFreg_eq s hs hsne]
    simp only [G]
    rw [hRfun, hP]
    ring
  have hmain : verticalIntegral b G - verticalIntegral a G = ∑ j : Fin S.card, R j :=
    verticalIntegral_sub_eq_sum_residues_of_subquadratic_strip_growth hab S.card p R
      hp_inj hp_mem G U hU hstrip hG_diff hregular'
      (hG_int a ha (fun q => ne_of_lt (hp_strip q.val q.property).1))
      (hG_int b hb (fun q => ne_of_gt (hp_strip q.val q.property).2))
      hgrowthG
  rw [hG_vert_eq b hb (fun q => ne_of_gt (hp_strip q.val q.property).2),
    hG_vert_eq a ha (fun q => ne_of_lt (hp_strip q.val q.property).1)] at hmain
  rw [hmain]
  rw [← Equiv.sum_comp (e := e.symm)
    (g := fun q : ↥S => if n q = 0 then 0 else C q 1)]

end DedekindZetaZeroFree.LargeSieve.Vendor

end
