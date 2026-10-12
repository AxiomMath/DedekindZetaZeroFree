module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

private lemma key_sqrt_le (A b P₁ P₂ : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) :
    Real.sqrt ((2*A + b*P₁) * (2*A + b*P₂)) ≤ 2*A + b*(P₁*P₂) := by
  have hP₁0 : 0 ≤ P₁ := le_trans zero_le_one hP₁
  have hP₂0 : 0 ≤ P₂ := le_trans zero_le_one hP₂
  have hZ : 0 ≤ 2*A + b*(P₁*P₂) := by
    have := mul_nonneg hb (mul_nonneg hP₁0 hP₂0); linarith
  rw [Real.sqrt_le_left hZ]
  have hsum : P₁ + P₂ ≤ 2*(P₁*P₂) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP₁) (sub_nonneg.mpr hP₂)]
  have hmul1 : 2*A*b*(P₁+P₂) ≤ 2*A*b*(2*(P₁*P₂)) :=
    mul_le_mul_of_nonneg_left hsum (by nlinarith [mul_nonneg hA hb])
  have hmul2 : 0 ≤ b^2*(P₁*P₂)*(P₁*P₂-1) := by
    have : 0 ≤ P₁*P₂-1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hP₁) (sub_nonneg.mpr hP₂)]
    positivity
  nlinarith [hmul1, hmul2]

private lemma envelope (A b P₁ P₂ U₁ U₂ L : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂)
    (hP₁A : P₁ ≤ 2*A) (hP₂A : P₂ ≤ 2*A)
    (hU₁ : 0 ≤ U₁) (hU₂ : 0 ≤ U₂) (hL : 0 ≤ L)
    (hb₁ : U₁ ≤ L*(max 1 (A/P₁)+b)) (hb₂ : U₂ ≤ L*(max 1 (A/P₂)+b)) :
    Real.sqrt (U₁*U₂) ≤ L*(2*A + b*(P₁*P₂))/Real.sqrt (P₁*P₂) := by
  have hP₁0 : 0 < P₁ := lt_of_lt_of_le zero_lt_one hP₁
  have hP₂0 : 0 < P₂ := lt_of_lt_of_le zero_lt_one hP₂
  have hP0 : 0 < P₁*P₂ := mul_pos hP₁0 hP₂0
  have hmax₁ : max 1 (A/P₁) ≤ 2*A/P₁ := by
    rw [max_le_iff]
    exact ⟨by rw [le_div_iff₀ hP₁0]; linarith,
           div_le_div_of_nonneg_right (by linarith) hP₁0.le⟩
  have hmax₂ : max 1 (A/P₂) ≤ 2*A/P₂ := by
    rw [max_le_iff]
    exact ⟨by rw [le_div_iff₀ hP₂0]; linarith,
           div_le_div_of_nonneg_right (by linarith) hP₂0.le⟩
  have hU₁' : U₁ ≤ L*(2*A/P₁ + b) :=
    le_trans hb₁ (mul_le_mul_of_nonneg_left (by linarith [hmax₁]) hL)
  have hU₂' : U₂ ≤ L*(2*A/P₂ + b) :=
    le_trans hb₂ (mul_le_mul_of_nonneg_left (by linarith [hmax₂]) hL)
  have hx0 : 0 ≤ 2*A/P₁ + b := by positivity
  have hy0 : 0 ≤ 2*A/P₂ + b := by positivity
  have hprod : Real.sqrt (U₁*U₂) ≤ L*Real.sqrt ((2*A/P₁+b)*(2*A/P₂+b)) := by
    have hmul : U₁*U₂ ≤ (L*(2*A/P₁+b))*(L*(2*A/P₂+b)) :=
      mul_le_mul hU₁' hU₂' hU₂ (mul_nonneg hL hx0)
    have hs := Real.sqrt_le_sqrt hmul
    have heq : Real.sqrt ((L*(2*A/P₁+b))*(L*(2*A/P₂+b)))
        = L*Real.sqrt ((2*A/P₁+b)*(2*A/P₂+b)) := by
      rw [show (L*(2*A/P₁+b))*(L*(2*A/P₂+b)) = L*L*((2*A/P₁+b)*(2*A/P₂+b)) by ring,
          Real.sqrt_mul (mul_nonneg hL hL), Real.sqrt_mul_self hL]
    rw [heq] at hs
    exact hs
  have hsplit : Real.sqrt ((2*A/P₁+b)*(2*A/P₂+b))
      = Real.sqrt ((2*A+b*P₁)*(2*A+b*P₂))/Real.sqrt (P₁*P₂) := by
    have heq : (2*A/P₁+b)*(2*A/P₂+b) = (2*A+b*P₁)*(2*A+b*P₂)/(P₁*P₂) := by
      field_simp <;> ring
    rw [heq, Real.sqrt_div (by positivity : (0:ℝ) ≤ (2*A+b*P₁)*(2*A+b*P₂)) (P₁*P₂)]
  have hkey : Real.sqrt ((2*A+b*P₁)*(2*A+b*P₂)) ≤ 2*A + b*(P₁*P₂) :=
    key_sqrt_le A b P₁ P₂ hA.le hb hP₁ hP₂
  have hfin : Real.sqrt ((2*A/P₁+b)*(2*A/P₂+b)) ≤ (2*A + b*(P₁*P₂))/Real.sqrt (P₁*P₂) := by
    rw [hsplit]
    exact div_le_div_of_nonneg_right hkey (Real.sqrt_nonneg _)
  calc Real.sqrt (U₁*U₂) ≤ L*Real.sqrt ((2*A/P₁+b)*(2*A/P₂+b)) := hprod
    _ ≤ L*((2*A + b*(P₁*P₂))/Real.sqrt (P₁*P₂)) := mul_le_mul_of_nonneg_left hfin hL
    _ = L*(2*A + b*(P₁*P₂))/Real.sqrt (P₁*P₂) := by rw [mul_div_assoc]

private lemma sqrt_div_mul_sqrt (M B : ℝ) (hM : 0 < M) (hB : 0 < B) :
    Real.sqrt (M/B) * Real.sqrt (B*M) = M := by
  have h1 : Real.sqrt (M/B) * Real.sqrt (B*M) = Real.sqrt ((M/B)*(B*M)) :=
    (Real.sqrt_mul (div_nonneg hM.le hB.le) (B*M)).symm
  have h2 : (M/B)*(B*M) = M*M := by field_simp <;> ring
  rw [h1, h2, Real.sqrt_mul_self hM.le]

private lemma rpow_mul_sqrt_div (M B α : ℝ) (hM : 0 < M) (hB : 0 < B) :
    B^α * Real.sqrt (M/B) = Real.sqrt M * B^(α - 1/2) := by
  have h1 : Real.sqrt (M/B) = Real.sqrt M / Real.sqrt B := Real.sqrt_div hM.le B
  rw [h1]
  simp only [Real.sqrt_eq_rpow]
  rw [Real.rpow_sub hB, mul_div_assoc', mul_div_assoc']
  ring

private lemma mul_rpow_div_sqrt (M B α : ℝ) (hM : 0 < M) (hB : 0 < B) :
    M * B^α / Real.sqrt (B*M) = Real.sqrt M * B^(α - 1/2) := by
  have h := sqrt_div_mul_sqrt M B hM hB
  have hne : Real.sqrt (B*M) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos hB hM))
  have hstep : (Real.sqrt (M/B) * Real.sqrt (B*M)) * B^α / Real.sqrt (B*M)
      = Real.sqrt (M/B) * B^α := by
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ (B^α) hne]
  calc M * B^α / Real.sqrt (B*M)
      = (Real.sqrt (M/B) * Real.sqrt (B*M)) * B^α / Real.sqrt (B*M) :=
        congrArg (fun z => z * B^α / Real.sqrt (B*M)) h.symm
    _ = Real.sqrt (M/B) * B^α := hstep
    _ = B^α * Real.sqrt (M/B) := by ring
    _ = Real.sqrt M * B^(α - 1/2) := rpow_mul_sqrt_div M B α hM hB

theorem bilinear_rectangle_three_thresholds
    (M N n B α P₁ P₂ U₁ U₂ L : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (hnN : n ≤ 2 * N) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hP₁ : P₁ ∈ Set.Icc (1 : ℝ) (2 * (N / n)))
    (hP₂ : P₂ ∈ Set.Icc (1 : ℝ) (2 * (N / n)))
    (hU₁ : 0 ≤ U₁) (hU₂ : 0 ≤ U₂) (hL : 0 ≤ L)
    (hbound₁ : U₁ ≤ L * (max 1 ((N / n) / P₁) + Real.rpow B α))
    (hbound₂ : U₂ ≤ L * (max 1 ((N / n) / P₂) + Real.rpow B α)) :
    (∀ c : ℝ, 0 < c →
      c * N / (n * Real.sqrt (B * M)) ≤ P₁ * P₂ →
      Real.sqrt (M / B) * Real.sqrt (U₁ * U₂ / (P₁ * P₂)) ≤
        L * (2 * M / c + Real.sqrt M * Real.rpow B (α - 1 / 2))) ∧
    (∀ c t : ℝ, 0 < c → 1 ≤ t →
      c * Real.sqrt (M / B) / (n * t) ≤ P₁ * P₂ →
      Real.sqrt (M / B) * Real.sqrt (U₁ * U₂ / (P₁ * P₂)) ≤
        L * (2 * N * t / c + Real.sqrt M * Real.rpow B (α - 1 / 2))) ∧
    (∀ t : ℝ, 1 ≤ t →
      P₁ * P₂ ≤ t * N / Real.sqrt (B * M) →
      (n * M / N) * Real.sqrt ((P₁ * P₂) * U₁ * U₂) ≤
        L * (2 * M + n * t * (Real.sqrt M * Real.rpow B (α - 1 / 2)))) ∧
    (∀ t k : ℝ, 1 ≤ t → 0 ≤ k → k ≤ n * M / N →
      P₁ * P₂ ≤ t * N / Real.sqrt (B * M) →
      k * Real.sqrt ((P₁ * P₂) * U₁ * U₂) ≤
        L * (2 * M + n * t * (Real.sqrt M * Real.rpow B (α - 1 / 2)))) := by
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by linarith
  have hnpos : 0 < n := by linarith
  have hBpos : 0 < B := by linarith
  have hP₁1 : 1 ≤ P₁ := hP₁.1
  have hP₂1 : 1 ≤ P₂ := hP₂.1
  have hP₁le : P₁ ≤ 2*(N/n) := hP₁.2
  have hP₂le : P₂ ≤ 2*(N/n) := hP₂.2
  have hP₁pos : 0 < P₁ := by linarith
  have hP₂pos : 0 < P₂ := by linarith
  have hPpos : 0 < P₁*P₂ := mul_pos hP₁pos hP₂pos
  have hb : 0 ≤ Real.rpow B α := Real.rpow_nonneg hBpos.le α
  have hA : 0 < N/n := div_pos hNpos hnpos
  have henv : Real.sqrt (U₁*U₂) ≤ L*(2*(N/n) + Real.rpow B α*(P₁*P₂))/Real.sqrt (P₁*P₂) :=
    envelope (N/n) (Real.rpow B α) P₁ P₂ U₁ U₂ L hA hb hP₁1 hP₂1 hP₁le hP₂le hU₁ hU₂ hL hbound₁ hbound₂
  have hst : Real.sqrt (M/B)*Real.sqrt (B*M) = M := sqrt_div_mul_sqrt M B hMpos hBpos
  have hbs : Real.rpow B α * Real.sqrt (M/B) = Real.sqrt M * Real.rpow B (α - 1/2) :=
    rpow_mul_sqrt_div M B α hMpos hBpos
  have hbP : M * Real.rpow B α / Real.sqrt (B*M) = Real.sqrt M * Real.rpow B (α - 1/2) :=
    mul_rpow_div_sqrt M B α hMpos hBpos
  have hsplit : Real.sqrt (U₁*U₂/(P₁*P₂)) = Real.sqrt (U₁*U₂)/Real.sqrt (P₁*P₂) :=
    Real.sqrt_div (mul_nonneg hU₁ hU₂) (P₁*P₂)
  have hsqrtPpos : 0 < Real.sqrt (P₁*P₂) := Real.sqrt_pos.mpr hPpos
  have hboundU : Real.sqrt (U₁*U₂)/Real.sqrt (P₁*P₂)
      ≤ L*(2*(N/n)+Real.rpow B α*(P₁*P₂))/(P₁*P₂) := by
    have h := div_le_div_of_nonneg_right henv (Real.sqrt_nonneg (P₁*P₂))
    rw [div_div, Real.mul_self_sqrt hPpos.le] at h
    exact h
  have hsp : Real.sqrt ((P₁*P₂)*U₁*U₂) = Real.sqrt (P₁*P₂)*Real.sqrt (U₁*U₂) := by
    rw [show (P₁*P₂)*U₁*U₂ = (P₁*P₂)*(U₁*U₂) by ring, Real.sqrt_mul hPpos.le]
  have hterm2 : Real.sqrt (M/B)*Real.rpow B α ≤ Real.sqrt M*Real.rpow B (α - 1/2) := by
    rw [mul_comm (Real.sqrt (M/B)) (Real.rpow B α)]
    exact le_of_eq hbs
  have henvR : Real.sqrt (M/B)*(L*(2*(N/n)+Real.rpow B α*(P₁*P₂))/(P₁*P₂))
      = L*(Real.sqrt (M/B)*(2*(N/n)/(P₁*P₂) + Real.rpow B α)) := by
    field_simp <;> ring
  have hiii : ∀ t : ℝ, 1 ≤ t →
      P₁*P₂ ≤ t*N/Real.sqrt (B*M) →
      (n*M/N)*Real.sqrt ((P₁*P₂)*U₁*U₂) ≤
        L*(2*M + n*t*(Real.sqrt M*Real.rpow B (α - 1/2))) := by
    intro t ht hthr
    have henv3 : Real.sqrt (P₁*P₂)*Real.sqrt (U₁*U₂) ≤ L*(2*(N/n)+Real.rpow B α*(P₁*P₂)) := by
      have h := mul_le_mul_of_nonneg_left henv (Real.sqrt_nonneg (P₁*P₂))
      have heq : Real.sqrt (P₁*P₂)*(L*(2*(N/n)+Real.rpow B α*(P₁*P₂))/Real.sqrt (P₁*P₂))
          = L*(2*(N/n)+Real.rpow B α*(P₁*P₂)) := by
        rw [mul_div_assoc',
            mul_div_cancel_left₀ (L*(2*(N/n)+Real.rpow B α*(P₁*P₂))) (ne_of_gt hsqrtPpos)]
      rw [heq] at h
      exact h
    have hbP2 : (n*M/N)*Real.rpow B α*(P₁*P₂) ≤ n*t*(Real.sqrt M*Real.rpow B (α - 1/2)) := by
      have h1 : (n*M/N)*Real.rpow B α*(P₁*P₂)
          ≤ (n*M/N)*Real.rpow B α*(t*N/Real.sqrt (B*M)) :=
        mul_le_mul_of_nonneg_left hthr (by positivity)
      refine le_trans h1 ?_
      have heq : (n*M/N)*Real.rpow B α*(t*N/Real.sqrt (B*M))
          = n*t*(M*Real.rpow B α/Real.sqrt (B*M)) := by
        field_simp <;> ring
      rw [heq, hbP]
    have hfin3 : (n*M/N)*(2*(N/n)+Real.rpow B α*(P₁*P₂))
        ≤ 2*M + n*t*(Real.sqrt M*Real.rpow B (α - 1/2)) := by
      have heq : (n*M/N)*(2*(N/n)+Real.rpow B α*(P₁*P₂))
          = 2*M + (n*M/N)*Real.rpow B α*(P₁*P₂) := by
        field_simp <;> ring
      rw [heq]; linarith [hbP2]
    rw [hsp]
    refine le_trans (mul_le_mul_of_nonneg_left henv3 (by positivity : (0:ℝ) ≤ n*M/N)) ?_
    have heq : (n*M/N)*(L*(2*(N/n)+Real.rpow B α*(P₁*P₂)))
        = L*((n*M/N)*(2*(N/n)+Real.rpow B α*(P₁*P₂))) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hfin3 hL
  refine ⟨?_, ?_, hiii, ?_⟩
  · intro c hc hthr
    have hcN : c*N ≤ n*Real.sqrt (B*M)*(P₁*P₂) := by
      have h0 : 0 < n*Real.sqrt (B*M) := by positivity
      rw [div_le_iff₀ h0] at hthr
      linarith [hthr]
    have hstep : 2*(N/n)/(P₁*P₂) ≤ 2*Real.sqrt (B*M)/c := by
      have hL2 : 2*(N/n)/(P₁*P₂) = 2*N/(n*(P₁*P₂)) := by field_simp <;> ring
      rw [hL2, div_le_iff₀ (by positivity : (0:ℝ) < n*(P₁*P₂)),
          div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith [hcN]
    have hterm1 : Real.sqrt (M/B)*(2*(N/n)/(P₁*P₂)) ≤ 2*M/c := by
      refine le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)) ?_
      have heq : Real.sqrt (M/B)*(2*Real.sqrt (B*M)/c) = 2*M/c := by
        rw [show Real.sqrt (M/B)*(2*Real.sqrt (B*M)/c)
            = 2*(Real.sqrt (M/B)*Real.sqrt (B*M))/c by ring, hst]
      rw [heq]
    have hfin : Real.sqrt (M/B)*(2*(N/n)/(P₁*P₂) + Real.rpow B α)
        ≤ 2*M/c + Real.sqrt M*Real.rpow B (α - 1/2) := by
      rw [mul_add]; linarith [hterm1, hterm2]
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left hboundU (Real.sqrt_nonneg _)) ?_
    rw [henvR]
    exact mul_le_mul_of_nonneg_left hfin hL
  · intro c t hc ht hthr
    have hcs : c*Real.sqrt (M/B) ≤ n*t*(P₁*P₂) := by
      have h0 : 0 < n*t := by positivity
      rw [div_le_iff₀ h0] at hthr
      linarith [hthr]
    have hstep : 2*(N/n)/(P₁*P₂) ≤ 2*N*t/(c*Real.sqrt (M/B)) := by
      have hL2 : 2*(N/n)/(P₁*P₂) = 2*N/(n*(P₁*P₂)) := by field_simp <;> ring
      rw [hL2, div_le_iff₀ (by positivity : (0:ℝ) < n*(P₁*P₂)),
          div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < c*Real.sqrt (M/B))]
      have hmul : 2*N*(c*Real.sqrt (M/B)) ≤ 2*N*(n*t*(P₁*P₂)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 2*N)
      linarith [hmul]
    have hterm1 : Real.sqrt (M/B)*(2*(N/n)/(P₁*P₂)) ≤ 2*N*t/c := by
      refine le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)) ?_
      have heq : Real.sqrt (M/B)*(2*N*t/(c*Real.sqrt (M/B))) = 2*N*t/c := by
        field_simp <;> ring
      rw [heq]
    have hfin : Real.sqrt (M/B)*(2*(N/n)/(P₁*P₂) + Real.rpow B α)
        ≤ 2*N*t/c + Real.sqrt M*Real.rpow B (α - 1/2) := by
      rw [mul_add]; linarith [hterm1, hterm2]
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left hboundU (Real.sqrt_nonneg _)) ?_
    rw [henvR]
    exact mul_le_mul_of_nonneg_left hfin hL
  · intro t k ht hk0 hk hthr
    exact le_trans (mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg _)) (hiii t ht hthr)

end DedekindZetaZeroFree.LargeSieve.Sieve
