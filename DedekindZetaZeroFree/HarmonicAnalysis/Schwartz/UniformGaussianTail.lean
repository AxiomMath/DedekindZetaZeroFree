module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree

theorem thetaUniformGaussianTail
    {ι : Type*} [Countable ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} (x : ι → E) (S : Set H) (F : ℝ → H → ι → ℂ)
    (P c p η : ℝ) (hP : 0 < P) (hc : 0 < c) (hp : 0 < p) (hη : 0 < η)
    (hgap : ∀ i, η ≤ ‖x i‖)
    (hsum : Summable (fun i => Real.exp (-(c / 2) * ‖x i‖ ^ 2)))
    (hbound : ∀ t : ℝ, 1 ≤ t → ∀ h ∈ S, ∀ i,
      ‖F t h i‖ ≤ P * Real.exp (-c * t ^ p * ‖x i‖ ^ 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 1 ≤ t → ∀ h ∈ S,
      Summable (F t h) ∧
        ‖∑' i, F t h i‖ ≤ A * Real.exp (-(c * η ^ 2 / 2) * t ^ p) := by
  set G : ι → ℝ := fun i => Real.exp (-(c / 2) * ‖x i‖ ^ 2) with hG
  have hGsum : Summable G := by simpa only [hG] using hsum
  have hGnonneg : ∀ i, 0 ≤ G i := fun i => by rw [hG]; exact Real.exp_nonneg _
  have hGtsum : 0 ≤ ∑' i, G i := tsum_nonneg hGnonneg
  have hc2 : 0 ≤ c / 2 := by positivity
  refine ⟨P * (1 + ∑' i, G i), mul_pos hP (by linarith), ?_⟩
  intro t ht h hh
  have htp : 1 ≤ t ^ p := Real.one_le_rpow ht hp.le
  set E' : ℝ := Real.exp (-(c * η ^ 2 / 2) * t ^ p) with hE'
  have hE'pos : 0 < E' := Real.exp_pos _
  have hpoint : ∀ i, ‖F t h i‖ ≤ (P * E') * G i := by
    intro i
    have hxnonneg : 0 ≤ ‖x i‖ := norm_nonneg _
    have hη2 : η ^ 2 ≤ ‖x i‖ ^ 2 := by nlinarith [hη.le, hgap i, hxnonneg]
    have hexp_eq : Real.exp (-c * t ^ p * ‖x i‖ ^ 2)
        = Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2)
          * Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle1 : Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) ≤ E' := by
      rw [hE', Real.exp_le_exp]
      have hmul : (c / 2) * t ^ p * η ^ 2 ≤ (c / 2) * t ^ p * ‖x i‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hη2 (by positivity)
      have heq : (c * η ^ 2 / 2) * t ^ p = (c / 2) * t ^ p * η ^ 2 := by ring
      linarith [hmul, heq]
    have hle2 : Real.exp (-(c / 2) * t ^ p * ‖x i‖ ^ 2) ≤ G i := by
      rw [hG, Real.exp_le_exp]
      have hA : 0 ≤ (c / 2) * ‖x i‖ ^ 2 := mul_nonneg hc2 (sq_nonneg _)
      have h1 : (c / 2) * ‖x i‖ ^ 2 * (t ^ p - 1) ≥ 0 :=
        mul_nonneg hA (by linarith)
      nlinarith [h1]
    have hprod : Real.exp (-c * t ^ p * ‖x i‖ ^ 2) ≤ E' * G i := by
      rw [hexp_eq]
      exact mul_le_mul hle1 hle2 (Real.exp_nonneg _) hE'pos.le
    calc ‖F t h i‖ ≤ P * Real.exp (-c * t ^ p * ‖x i‖ ^ 2) := hbound t ht h hh i
      _ ≤ P * (E' * G i) := mul_le_mul_of_nonneg_left hprod hP.le
      _ = (P * E') * G i := by ring
  have hsumPE : Summable (fun i => (P * E') * G i) := hGsum.mul_left (P * E')
  have hnormsum : Summable (fun i => ‖F t h i‖) :=
    Summable.of_norm_bounded hsumPE fun i => by simpa using hpoint i
  have hFsum : Summable (F t h) := hnormsum.of_norm
  refine ⟨hFsum, ?_⟩
  have step1 : ‖∑' i, F t h i‖ ≤ ∑' i, ‖F t h i‖ := norm_tsum_le_tsum_norm hnormsum
  have step2 : ∑' i, ‖F t h i‖ ≤ ∑' i, (P * E') * G i :=
    hnormsum.tsum_le_tsum hpoint hsumPE
  have step3 : ∑' i, (P * E') * G i = (P * E') * ∑' i, G i := tsum_mul_left
  have step4 : (P * E') * ∑' i, G i ≤ (P * (1 + ∑' i, G i)) * E' := by
    have hPE : 0 ≤ P * E' := mul_nonneg hP.le hE'pos.le
    nlinarith [hPE]
  calc ‖∑' i, F t h i‖ ≤ ∑' i, ‖F t h i‖ := step1
    _ ≤ ∑' i, (P * E') * G i := step2
    _ = (P * E') * ∑' i, G i := step3
    _ ≤ (P * (1 + ∑' i, G i)) * E' := step4
    _ = (P * (1 + ∑' i, G i)) * Real.exp (-(c * η ^ 2 / 2) * t ^ p) := by rw [hE']

end DedekindZetaZeroFree
