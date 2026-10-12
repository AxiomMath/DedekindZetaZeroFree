module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open MeasureTheory

theorem mellinSplitRemainder_f_integrable (P : WeakFEPair ℂ) (hk : P.k = 1)
    (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (P.f t - P.f₀))
      (Set.Ioi 1) volume := by
  have h := (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t)
    (Set.Ioi 0) volume at h
  refine (h.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  simp [WeakFEPair.f_modif, Set.mem_Ioi.mp ht,
    Set.notMem_Ioo_of_ge (Set.mem_Ioi.mp ht).le, smul_eq_mul]

theorem mellinSplitRemainder_g_integrable (P : WeakFEPair ℂ) (hk : P.k = 1)
    (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s) * (P.g t - P.g₀))
      (Set.Ioi 1) volume := by
  simpa only [WeakFEPair.symm_f, WeakFEPair.symm_f₀, sub_sub_cancel_left]
    using mellinSplitRemainder_f_integrable P.symm hk (1 - s)

private lemma lower_eq (P : WeakFEPair ℂ) (hk : P.k = 1) (t : ℝ) (ht : 0 < t) :
    (Set.Ioo 0 1).indicator
        (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) t =
      P.ε • ((t : ℂ) ^ (-1 : ℂ) •
        (Set.Ioi 1).indicator (fun x => P.g x - P.g₀) t⁻¹) := by
  by_cases hlt : t < 1
  · have hi : 1 < t⁻¹ := by simpa only [one_div] using (lt_one_div ht zero_lt_one).1 (by simpa using hlt)
    have hfe := P.h_feq t⁻¹ (Set.mem_Ioi.mpr (inv_pos.mpr ht))
    simp only [one_div, inv_inv, hk, Real.rpow_one, Complex.ofReal_inv, smul_eq_mul] at hfe
    rw [Set.indicator_of_mem (show t ∈ Set.Ioo 0 1 from ⟨ht, hlt⟩),
      Set.indicator_of_mem (show t⁻¹ ∈ Set.Ioi 1 from hi)]
    simp only [hk, Real.rpow_neg_one, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.cpow_one, smul_eq_mul, hfe]
    ring
  · have hi : t⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using (one_div_le_one_div_of_le zero_lt_one (le_of_not_gt hlt))
    simp [Set.indicator_of_notMem (show t ∉ Set.Ioo 0 1 from fun h => hlt h.2),
      Set.indicator_of_notMem (show t⁻¹ ∉ Set.Ioi 1 from not_lt.mpr hi)]

private lemma mellin_tail (f : ℝ → ℂ) (s : ℂ) :
    mellin ((Set.Ioi 1).indicator f) s =
      ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) * f t := by
  unfold mellin
  change (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s - 1) * (Set.Ioi 1).indicator f t) = _
  simp_rw [← Set.indicator_mul_right (Set.Ioi 1) (fun t : ℝ => (t : ℂ) ^ (s - 1)) f]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

theorem mellinSplitRemainder (P : WeakFEPair ℂ) (hk : P.k = 1) (s : ℂ) :
    P.Λ₀ s =
      (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (s - 1) * (P.f t - P.f₀)) +
      P.ε * (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s) * (P.g t - P.g₀)) := by
  let A := (Set.Ioi 1).indicator (fun t => P.f t - P.f₀)
  let B := (Set.Ioo 0 1).indicator
    (fun t => P.f t - (P.ε * ↑(t ^ (-P.k))) • P.g₀)
  have hA : MellinConvergent A s := by
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * A t) (Set.Ioi 0) volume
    dsimp [A]
    simp_rw [← Set.indicator_mul_right (Set.Ioi 1)
      (fun t : ℝ => (t : ℂ) ^ (s - 1)) (fun t => P.f t - P.f₀)]
    rw [integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet,
      Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
    exact mellinSplitRemainder_f_integrable P hk s
  have htotal := (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t)
    (Set.Ioi 0) volume at htotal
  have hB : MellinConvergent B s := by
    refine (htotal.sub hA).congr_fun (fun t ht => ?_) measurableSet_Ioi
    change (t : ℂ) ^ (s - 1) • (A t + B t) - (t : ℂ) ^ (s - 1) • A t =
      (t : ℂ) ^ (s - 1) • B t
    rw [smul_add, add_sub_cancel_left]
  have hsplit : P.Λ₀ s = mellin A s + mellin B s := by
    change (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s - 1) • (A t + B t)) = _
    simp_rw [smul_add]
    exact integral_add hA hB
  have hlower : mellin B s = P.ε • mellin
      (fun t => (t : ℂ) ^ (-1 : ℂ) •
        (Set.Ioi 1).indicator (fun x => P.g x - P.g₀) t⁻¹) s := by
    rw [← mellin_const_smul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
      congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z) (lower_eq P hk t ht))
  rw [hsplit, hlower, mellin_cpow_smul, mellin_comp_inv, mellin_tail, mellin_tail]
  simp only [smul_eq_mul]
  have hexp : -(s + (-1 : ℂ)) - 1 = -s := by ring
  simp only [hexp]

end DedekindZetaZeroFree.Hecke
