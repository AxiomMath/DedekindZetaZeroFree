module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TruncatedLogarithmicPolynomials
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.EulerIntegrationByParts

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped Classical ContDiff
open MeasureTheory Filter Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def logMellinRemainder (f : ℝ → ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  f x - truncatedLogPolynomial P x

def logMellinHolomorphicPart (f : ℝ → ℂ) (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  mellin (logMellinRemainder f P) s

def logMellinContinuation (f : ℝ → ℂ) (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  logMellinHolomorphicPart f P s + logPrincipalPart P s

section Helpers

private lemma continuousOn_eval_log_polynomial (P : Polynomial ℂ) :
    ContinuousOn (fun x : ℝ => Polynomial.eval (Real.log x : ℂ) P) (Set.Ioi 0) := by
  have hlog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx)
  exact (Polynomial.continuous P).comp_continuousOn hlog

private lemma locallyIntegrableOn_truncatedLogPolynomial (P : Polynomial ℂ) :
    LocallyIntegrableOn (truncatedLogPolynomial P) (Set.Ioi 0) := by
  have heq : truncatedLogPolynomial P = Set.indicator (Set.Ioo (0 : ℝ) 1)
      (fun x : ℝ => Polynomial.eval (Real.log x : ℂ) P) := by
    funext x
    simp only [truncatedLogPolynomial, Set.indicator, Set.mem_Ioo]
  rw [heq, locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkcomp
  have hint : IntegrableOn (fun x : ℝ => Polynomial.eval (Real.log x : ℂ) P) k :=
    ((continuousOn_eval_log_polynomial P).mono hk).integrableOn_compact hkcomp
  exact hint.indicator measurableSet_Ioo

private lemma locallyIntegrableOn_logMellinRemainder {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) :
    LocallyIntegrableOn (logMellinRemainder f P) (Set.Ioi 0) := by
  have hf : LocallyIntegrableOn f (Set.Ioi 0) :=
    h.contDiffOn.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have ht := locallyIntegrableOn_truncatedLogPolynomial P
  change LocallyIntegrableOn (f - truncatedLogPolynomial P) (Set.Ioi 0)
  exact hf.sub ht

private lemma logMellinRemainder_isBigO_origin {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) :
    logMellinRemainder f P =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ δ) := by
  obtain ⟨C, hC0, hC⟩ := h.origin_remainder 0
  refine Asymptotics.IsBigO.of_bound C ?_
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx0 hx1
  have hx : logMellinRemainder f P x = f x - Polynomial.eval (Real.log x : ℂ) P := by
    simp only [logMellinRemainder, truncatedLogPolynomial, Set.mem_Ioo]
    rw [if_pos ⟨hx0, hx1⟩]
  rw [hx, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le δ)]
  exact hC x hx0 hx1.le

private lemma logMellinRemainder_isBigO_top {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (a : ℝ) :
    logMellinRemainder f P =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  obtain ⟨C, hC0, hC⟩ := h.rapid_decay 0 (Nat.ceil a + 1)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hzero : truncatedLogPolynomial P x = 0 := by
    simp only [truncatedLogPolynomial, Set.mem_Ioo]
    rw [if_neg (by push Not; intro h1; linarith)]
  rw [logMellinRemainder, hzero, sub_zero,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
  refine le_trans (hC x hx) (mul_le_mul_of_nonneg_left ?_ hC0)
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  push_cast
  have := Nat.le_ceil a
  linarith

private lemma punctured_halfPlane_preconnected {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected {s : ℂ | -δ < s.re ∧ s ≠ 0} := by
  let A : Set ℂ := {s | 0 < s.re}
  let B : Set ℂ := {s | -δ < s.re ∧ 0 < s.im}
  let C : Set ℂ := {s | -δ < s.re ∧ s.im < 0}
  let D : Set ℂ := {s | -δ < s.re ∧ s.re < 0}
  have hA : IsPreconnected A := (convex_halfSpace_re_gt 0).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC : IsPreconnected C :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hD : IsPreconnected D :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt 0)).isPreconnected
  have hAB := hA.union (1 + Complex.I) (by simp [A]) (by simp [B]; linarith) hB
  have hABC := hAB.union (1 - Complex.I) (by simp [A, B]) (by simp [C]; linarith) hC
  have hall := hABC.union ((-δ / 2 : ℝ) + Complex.I)
    (by simp [A, B, C]; left; right; linarith)
    (by simp [D]; constructor <;> linarith) hD
  convert hall using 1
  ext z
  simp only [A, B, C, D, Set.mem_setOf_eq, Set.mem_union]
  have hz : z ≠ 0 ↔ z.re ≠ 0 ∨ z.im ≠ 0 := by
    simp only [ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and_or]
  rw [hz]
  constructor
  · rintro ⟨hr, hne⟩
    rcases lt_trichotomy z.re 0 with hl | he | hg
    · exact Or.inr ⟨hr, hl⟩
    · rcases hne with hn | hn
      · exact (hn he).elim
      · rcases lt_or_gt_of_ne hn with hi | hi
        · exact Or.inl (Or.inr ⟨hr, hi⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨hr, hi⟩))
    · exact Or.inl (Or.inl (Or.inl hg))
  · rintro (((hr | ⟨hr, hi⟩) | ⟨hr, hi⟩) | ⟨hr, hi⟩)
    · exact ⟨by linarith, Or.inl (ne_of_gt hr)⟩
    · exact ⟨hr, Or.inr (ne_of_gt hi)⟩
    · exact ⟨hr, Or.inr (ne_of_lt hi)⟩
    · exact ⟨hr, Or.inl (ne_of_lt hi)⟩

private lemma halfPlane_identity {δ : ℝ} (hδ : 0 < δ) {F G : ℂ → ℂ}
    (hF : ∀ z, -δ < z.re → z ≠ 0 → DifferentiableAt ℂ F z)
    (hG : ∀ z, -δ < z.re → z ≠ 0 → DifferentiableAt ℂ G z)
    (heq : ∀ z, 0 < z.re → F z = G z)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) : F s = G s := by
  let U : Set ℂ := {z | -δ < z.re ∧ z ≠ 0}
  have hU : IsOpen U := (Complex.isOpen_re_gt (-δ)).inter isOpen_compl_singleton
  have hFa : AnalyticOnNhd ℂ F U :=
    (show DifferentiableOn ℂ F U from fun z hz =>
      (hF z hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU
  have hGa : AnalyticOnNhd ℂ G U :=
    (show DifferentiableOn ℂ G U from fun z hz =>
      (hG z hz.1 hz.2).differentiableWithinAt).analyticOnNhd hU
  have hevent : F =ᶠ[𝓝 (1 : ℂ)] G := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds (show 0 < (1 : ℂ).re by norm_num)]
      with z hz
    exact heq z hz
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (punctured_halfPlane_preconnected hδ)
    (show (1 : ℂ) ∈ U by simp [U]; linarith) hevent ⟨hs, hs0⟩

private lemma contDiffOn_eulerIter {a : ℝ → ℂ} (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0))
    (j : ℕ) : ContDiffOn ℝ ∞ (EulerIter j a) (Set.Ioi 0) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    have hderiv : ContDiffOn ℝ ∞ (deriv (EulerIter j a)) (Set.Ioi 0) :=
      ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hmul : ContDiffOn ℝ ∞
        (fun x : ℝ => (x : ℂ) * deriv (EulerIter j a) x) (Set.Ioi 0) :=
      (Complex.ofRealCLM.contDiff.contDiffOn).mul hderiv
    refine hmul.congr ?_
    intro x hx
    exact EulerIter_succ_of_pos j a x hx

private lemma eulerIter_add_of_pos {a b : ℝ → ℂ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioi 0)) (hb : ContDiffOn ℝ ∞ b (Set.Ioi 0)) (j : ℕ) :
    ∀ x : ℝ, 0 < x →
      EulerIter j (fun y => a y + b y) x = EulerIter j a x + EulerIter j b x := by
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    have hda : DifferentiableAt ℝ (EulerIter j a) x :=
      ((contDiffOn_eulerIter ha j).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hdb : DifferentiableAt ℝ (EulerIter j b) x :=
      ((contDiffOn_eulerIter hb j).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)
    have hcongr : EulerIter j (fun y => a y + b y) =ᶠ[𝓝 x]
        (fun y => EulerIter j a y + EulerIter j b y) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih y hy
    rw [EulerIter_succ_of_pos _ _ _ hx, EulerIter_succ_of_pos _ _ _ hx,
      EulerIter_succ_of_pos _ _ _ hx, hcongr.deriv_eq,
      show deriv (fun y => EulerIter j a y + EulerIter j b y) x =
          deriv (EulerIter j a) x + deriv (EulerIter j b) x from deriv_add hda hdb]
    ring

private lemma contDiffOn_eval_log (P : Polynomial ℂ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => P.eval (Real.log y : ℂ)) (Set.Ioi 0) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => P.eval z) := by
    have h : ContDiff ℂ ∞ (fun z : ℂ => P.aeval z) := Polynomial.contDiff_aeval P ∞
    have h' : ContDiff ℝ ∞ (fun z : ℂ => P.aeval z) := h.restrict_scalars ℝ
    simpa only [Polynomial.coe_aeval_eq_eval] using h'
  have h2 : ContDiffOn ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) (Set.Ioi 0) := by
    have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
      Real.contDiffOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hx)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  exact h1.comp_contDiffOn h2

private lemma eulerIter_sub_originPolynomial_eq {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} (h : LogMellinPhysical f δ P) (j : ℕ) :
    ∀ x : ℝ, 0 < x →
      EulerIter j f x =
        EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x +
          Polynomial.eval (Real.log x : ℂ) ((Polynomial.derivative^[j]) P) := by
  intro x hx
  have hf' : ContDiffOn ℝ ∞ (fun y : ℝ => f y - P.eval (Real.log y : ℂ)) (Set.Ioi 0) :=
    h.contDiffOn.sub (contDiffOn_eval_log P)
  have hp' : ContDiffOn ℝ ∞ (fun y : ℝ => P.eval (Real.log y : ℂ)) (Set.Ioi 0) :=
    contDiffOn_eval_log P
  have hsplit := eulerIter_add_of_pos hf' hp' j x hx
  have hfun : (fun y : ℝ => (f y - P.eval (Real.log y : ℂ)) + P.eval (Real.log y : ℂ)) = f := by
    funext y; ring
  rw [hfun] at hsplit
  rw [hsplit, EulerIter_eval_log_polynomial P j x hx]

private lemma eulerIter_eq_remainder_of_degree_lt {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} (h : LogMellinPhysical f δ P) (j : ℕ)
    (hj : P.natDegree < j) :
    ∀ x : ℝ, 0 < x →
      EulerIter j f x = EulerIter j (fun y => f y - P.eval (Real.log y : ℂ)) x := by
  intro x hx
  rw [eulerIter_sub_originPolynomial_eq h j x hx, Polynomial.iterate_derivative_eq_zero hj]
  simp

private lemma high_euler_mellin_differentiableAt {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (n : ℕ) (hn : P.natDegree < n)
    (s : ℂ) (hs : -δ < s.re) : DifferentiableAt ℂ (mellin (EulerIter n f)) s := by
  obtain ⟨N, hN⟩ := exists_nat_gt s.re
  obtain ⟨C₂, hC₂, hbound₂⟩ := h.rapid_decay n N
  obtain ⟨C₁, hC₁, hbound₁⟩ := h.origin_remainder n
  apply mellin_differentiableAt_of_isBigO_rpow (a := (N : ℝ)) (b := -δ)
    ((contDiffOn_eulerIter h.contDiffOn n).continuousOn.locallyIntegrableOn measurableSet_Ioi)
  · refine Asymptotics.IsBigO.of_bound C₂ ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)]
    exact hbound₂ x hx
  · exact hN
  · refine Asymptotics.IsBigO.of_bound C₁ ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with x hx
    rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _),
      eulerIter_eq_remainder_of_degree_lt h n hn x hx.1]
    exact hbound₁ x hx.1 hx.2
  · exact hs

end Helpers

theorem logMellinHolomorphicPart_differentiableAt {f : ℝ → ℂ} {δ : ℝ}
    {P : Polynomial ℂ} (h : LogMellinPhysical f δ P) (s : ℂ) (hs : -δ < s.re) :
    DifferentiableAt ℂ (logMellinHolomorphicPart f P) s :=
  mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_logMellinRemainder h)
    (logMellinRemainder_isBigO_top h (s.re + 1)) (by linarith)
    (by simpa using logMellinRemainder_isBigO_origin h) hs

theorem logMellinContinuation_eq_mellin {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (s : ℂ) (hs : 0 < s.re) :
    logMellinContinuation f P s = mellin f s := by
  have hfconv : MellinConvergent f s := h.euler_mellinConvergent 0 s hs
  have htconv : MellinConvergent (truncatedLogPolynomial P) s :=
    truncatedLogPolynomial_mellinConvergent P s hs
  have hsub : mellin (logMellinRemainder f P) s =
      mellin f s - mellin (truncatedLogPolynomial P) s :=
    (hasMellin_sub hfconv htconv).2
  simp only [logMellinContinuation, logMellinHolomorphicPart, hsub,
    mellin_truncatedLogPolynomial P s hs]
  ring

theorem logMellinContinuation_eq_euler {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (n : ℕ) (hn : P.natDegree < n)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) :
    logMellinContinuation f P s =
      (-s) ^ (-(n : ℤ)) * mellin (EulerIter n f) s := by
  refine halfPlane_identity h.delta_pos (F := logMellinContinuation f P)
    (G := fun z => (-z) ^ (-(n : ℤ)) * mellin (EulerIter n f) z) ?_ ?_ ?_ s hs hs0
  · intro z hz hz0
    exact (logMellinHolomorphicPart_differentiableAt h z hz).add
      (logPrincipalPart_differentiableAt P z hz0)
  · intro z hz hz0
    exact ((differentiableAt_id.neg).zpow (Or.inl (neg_ne_zero.mpr hz0))).mul
      (high_euler_mellin_differentiableAt h n hn z hz)
  · intro z hz
    have hz0 : z ≠ 0 := by intro he; simpa [he] using hz
    rw [logMellinContinuation_eq_mellin h z hz, h.euler_mellin_eq n z hz,
      zpow_neg, zpow_natCast, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr hz0)),
      one_mul]

theorem logMellinContinuation_unique {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (h : LogMellinPhysical f δ P) (H₀ : ℂ → ℂ)
    (hM : ∀ s : ℂ, 0 < s.re → H₀ s = mellin f s)
    (hR : ∀ s : ℂ, -δ < s.re → s ≠ 0 → DifferentiableAt ℂ H₀ s)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) :
    H₀ s = logMellinContinuation f P s := by
  refine halfPlane_identity h.delta_pos hR ?_ ?_ s hs hs0
  · intro z hz hz0
    exact (logMellinHolomorphicPart_differentiableAt h z hz).add
      (logPrincipalPart_differentiableAt P z hz0)
  · intro z hz
    exact (hM z hz).trans (logMellinContinuation_eq_mellin h z hz).symm

end DedekindZetaZeroFree.LargeSieve.Vendor

end
