module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.SmoothThetaAndGramKernels
public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.Analysis.FiniteWeightedGramBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma gram_sum_eq (F : Type) [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (M : ℝ) (b d : Ideal (𝓞 F)) :
    (∑ a ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2 : ℝ) * M)).filter (fun I => I ≠ ⊥),
        ((DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm a : ℝ) / M) : ℂ) *
          (Q.χ b) a * (starRingEnd ℂ) ((Q.χ d) a)))
      = initialGram F Q M b d := by
  simp only [initialGram, initialTheta, mul_assoc]

theorem initial_conditional_sector
    (F : Type) [Field F] [NumberField F]
    (ε D H : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c),
        (∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
          ∀ b ∈ paperShell F c N, ‖initialGram F Q M b b‖ ≤ D * M) →
        (∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
          ∀ b1 ∈ paperShell F c N, ∀ b2 ∈ paperShell F c N,
            Q.cls b1 = Q.cls b2 → b1 ≠ b2 →
              ‖initialGram F Q M b1 b2‖ ≤ H * Real.rpow N (1 + ε)) →
        ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
          ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
            (∑ a ∈ paperShell F c M,
              ‖∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
                lam b * (Q.χ b) a‖ ^ 2) ≤
              C * (M + Real.rpow N (2 + ε)) *
                ∑ b ∈ (paperShell F c N).filter (fun b => Q.cls b = g),
                  ‖lam b‖ ^ 2 := by
  obtain ⟨CF, hCF1, -, hCF⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  refine ⟨max D (2 * CF * H), ?_, ?_⟩
  · exact le_trans hD (le_max_left _ _)
  intro c Q hdiag0 hoff0 M N hM hN g lam
  set R : Finset (Ideal (𝓞 F)) :=
    (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2 : ℝ) * M)).filter (fun I => I ≠ ⊥) with hR
  set w : Ideal (𝓞 F) → ℝ :=
    fun a => DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight ((Ideal.absNorm a : ℝ) / M) with hw
  set S : Finset (Ideal (𝓞 F)) := (paperShell F c N).filter (fun b => Q.cls b = g) with hS
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by linarith
  have hDM : 0 ≤ D * M := mul_nonneg hD (by linarith)
  have hrpow1 : 0 ≤ Real.rpow N (1 + ε) := Real.rpow_nonneg (by linarith) _
  have hHr : 0 ≤ H * Real.rpow N (1 + ε) := mul_nonneg hH hrpow1
  have hsub : paperShell F c M ⊆ R := by
    intro a ha
    rw [hR, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
      have hmem := (mem_paperShell F c M a).mp ha
      linarith [hmem.2.2.2]
    · intro hbot
      have hmem := (mem_paperShell F c M a).mp ha
      exact not_squarefree_zero (hbot ▸ hmem.1)
  have hw_nonneg : ∀ a ∈ R, 0 ≤ w a := by
    intro a _
    rw [hw]
    exact DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_nonneg _
  have hw0 : ∀ a ∈ paperShell F c M, 1 ≤ w a := by
    intro a ha
    rw [hw]
    have hmem := (mem_paperShell F c M a).mp ha
    have h1 : 1 ≤ (Ideal.absNorm a : ℝ) / M := by
      rw [one_le_div hMpos]; linarith [hmem.2.2.1]
    have h2 : (Ideal.absNorm a : ℝ) / M ≤ 2 := by
      rw [div_le_iff₀ hMpos]; linarith [hmem.2.2.2]
    exact le_of_eq (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_eq_one h1 h2).symm
  have gram_eq : ∀ b d : Ideal (𝓞 F),
      (∑ a ∈ R, (w a : ℂ) * (Q.χ b) a * (starRingEnd ℂ) ((Q.χ d) a))
        = initialGram F Q M b d := by
    intro b d
    rw [hR, hw]
    exact gram_sum_eq F Q M b d
  have hdiag : ∀ b ∈ S,
      ‖∑ a ∈ R, (w a : ℂ) * (Q.χ b) a * (starRingEnd ℂ) ((Q.χ b) a)‖ ≤ D * M := by
    intro b hb
    rw [hS, Finset.mem_filter] at hb
    rw [gram_eq b b]
    exact hdiag0 M N hM hN b hb.1
  have hoff : ∀ b ∈ S, ∀ d ∈ S, b ≠ d →
      ‖∑ a ∈ R, (w a : ℂ) * (Q.χ b) a * (starRingEnd ℂ) ((Q.χ d) a)‖
        ≤ H * Real.rpow N (1 + ε) := by
    intro b hb d hd hne
    rw [hS, Finset.mem_filter] at hb hd
    have hcls : Q.cls b = Q.cls d := by rw [hb.2, hd.2]
    rw [gram_eq b d]
    exact hoff0 M N hM hN b hb.1 d hd.1 hcls hne
  have key := DedekindZetaZeroFree.LargeSieve.Vendor.finite_weighted_gram_bound_subset
    (paperShell F c M) R S w (fun b a => (Q.χ b) a) lam
    (D * M) (H * Real.rpow N (1 + ε)) hDM hHr hw_nonneg hsub hw0 hdiag hoff
  have hSsub : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ 2 * N := by
    intro I hI
    rw [hS, Finset.mem_filter] at hI
    exact ((mem_paperShell F c N I).mp hI.1).2.2.2
  have hScard : (S.card : ℝ) ≤ CF * (2 * N) :=
    hCF (2 * N) (by linarith) S hSsub
  have hT : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hcoeff : D * M + (H * Real.rpow N (1 + ε)) * (S.card : ℝ)
      ≤ max D (2 * CF * H) * (M + Real.rpow N (2 + ε)) := by
    have step1 : (H * Real.rpow N (1 + ε)) * (S.card : ℝ)
        ≤ (H * Real.rpow N (1 + ε)) * (CF * (2 * N)) :=
      mul_le_mul_of_nonneg_left hScard hHr
    have hr : Real.rpow N (2 + ε) = Real.rpow N (1 + ε) * N := by
      rw [show (2 : ℝ) + ε = (1 + ε) + 1 by ring]
      change N ^ ((1 + ε) + 1) = N ^ (1 + ε) * N
      rw [Real.rpow_add hNpos, Real.rpow_one]
    have heq : (H * Real.rpow N (1 + ε)) * (CF * (2 * N))
        = 2 * CF * H * Real.rpow N (2 + ε) := by
      rw [hr]; ring
    have hDM' : D * M ≤ max D (2 * CF * H) * M :=
      mul_le_mul_of_nonneg_right (le_max_left D (2 * CF * H)) (by linarith)
    have h2 : 2 * CF * H * Real.rpow N (2 + ε)
        ≤ max D (2 * CF * H) * Real.rpow N (2 + ε) :=
      mul_le_mul_of_nonneg_right (le_max_right D (2 * CF * H))
        (Real.rpow_nonneg (by linarith) _)
    calc D * M + (H * Real.rpow N (1 + ε)) * (S.card : ℝ)
        ≤ D * M + 2 * CF * H * Real.rpow N (2 + ε) := by
          have := heq ▸ step1
          linarith
      _ ≤ max D (2 * CF * H) * M + max D (2 * CF * H) * Real.rpow N (2 + ε) := by
          linarith
      _ = max D (2 * CF * H) * (M + Real.rpow N (2 + ε)) := by ring
  calc ∑ a ∈ paperShell F c M, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
      ≤ (D * M + (H * Real.rpow N (1 + ε)) * (S.card : ℝ)) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
        key
    _ ≤ (max D (2 * CF * H) * (M + Real.rpow N (2 + ε))) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff hT

end DedekindZetaZeroFree.LargeSieve.Sieve
