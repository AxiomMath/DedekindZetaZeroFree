module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicWeights
public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def logIdealTerm {F : Type*} [Field F] [NumberField F]
    (a : Ideal (𝓞 F) → ℂ) (f : ℝ → ℂ) (X : ℝ) (I : Ideal (𝓞 F)) : ℂ :=
  if I = ⊥ then 0 else a I * f ((Ideal.absNorm I : ℝ) / X)

theorem logIdealTerm_summable_of_envelope {F : Type*} [Field F] [NumberField F]
    (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ‖a I‖ ≤ 1)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hdecay : ∃ A C : ℝ, 1 < A ∧ 0 ≤ C ∧
      ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C * Real.rpow x (-A))
    (X : ℝ) (hX : 0 < X) :
    Summable (fun I : Ideal (𝓞 F) => ‖logIdealTerm a f X I‖) ∧
      Summable (logIdealTerm a f X) := by
  classical
  obtain ⟨A, C, hA, hC0, hdec⟩ := hdecay

  set S : Set (Ideal (𝓞 F)) := {I | (Ideal.absNorm I : ℝ) ≤ max 1 X} with hSdef
  have hSfin : S.Finite := DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le F (max 1 X)
  have hSmem : ∀ I : Ideal (𝓞 F), I ∈ S ↔ (Ideal.absNorm I : ℝ) ≤ max 1 X :=
    fun I => Iff.rfl

  have hhead : Summable (fun I : Ideal (𝓞 F) =>
      if I ∈ S then ‖logIdealTerm a f X I‖ else 0) := by
    refine ((summable_subtype_iff_indicator (s := S)
      (f := fun I : Ideal (𝓞 F) => ‖logIdealTerm a f X I‖)).mp (hSfin.summable _)).congr ?_
    intro I
    rw [Set.indicator_apply]

  have henv : Summable (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-A)) :=
    DedekindZetaZeroFree.LargeSieve.summable_ideal_inverse_power F A hA
  have hg : Summable (fun I : Ideal (𝓞 F) =>
      (if I ∈ S then ‖logIdealTerm a f X I‖ else 0)
        + (C * X ^ A) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-A))) :=
    hhead.add (Summable.mul_left (C * X ^ A) henv)

  have hbound : ∀ I : Ideal (𝓞 F), ‖logIdealTerm a f X I‖ ≤
      (if I ∈ S then ‖logIdealTerm a f X I‖ else 0)
        + (C * X ^ A) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-A)) := by
    intro I
    by_cases hI : I ∈ S
    · have hnn : (0 : ℝ) ≤
          (C * X ^ A) * (if I = ⊥ then (0 : ℝ) else (Ideal.absNorm I : ℝ) ^ (-A)) := by
        refine mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (le_of_lt hX) A)) ?_
        split_ifs with h
        · exact le_rfl
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      rw [if_pos hI]
      linarith [norm_nonneg (logIdealTerm a f X I)]
    ·
      have hlt : max 1 X < (Ideal.absNorm I : ℝ) := by
        by_contra h
        push Not at h
        exact hI ((hSmem I).mpr h)
      have hNI1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) :=
        le_trans (le_max_left 1 X) (le_of_lt hlt)
      have hIne : I ≠ ⊥ := by
        intro hb
        rw [hb, Ideal.absNorm_bot, Nat.cast_zero] at hNI1
        linarith
      have hXlt : X < (Ideal.absNorm I : ℝ) := lt_of_le_of_lt (le_max_right 1 X) hlt
      have hratio : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) / X :=
        (one_le_div hX).mpr (le_of_lt hXlt)
      have henvI := hdec ((Ideal.absNorm I : ℝ) / X) hratio
      have hdiv : ((Ideal.absNorm I : ℝ) / X) ^ (-A)
          = (Ideal.absNorm I : ℝ) ^ (-A) * X ^ A := by
        rw [Real.div_rpow (Nat.cast_nonneg _) (le_of_lt hX) (-A),
          Real.rpow_neg (le_of_lt hX) A, div_eq_mul_inv, inv_inv]
      simp only [if_neg hI, zero_add, logIdealTerm, if_neg hIne, norm_mul]
      calc ‖a I‖ * ‖f ((Ideal.absNorm I : ℝ) / X)‖
          ≤ 1 * (C * ((Ideal.absNorm I : ℝ) / X) ^ (-A)) :=
            mul_le_mul (ha I hIne) henvI (norm_nonneg _) (by norm_num)
        _ = (C * X ^ A) * (Ideal.absNorm I : ℝ) ^ (-A) := by
            rw [one_mul, hdiv]; ring
  have hmain : Summable (logIdealTerm a f X) := Summable.of_norm_bounded hg hbound
  exact ⟨hmain.norm, hmain⟩

theorem logIdealTerm_summable {F : Type*} [Field F] [NumberField F]
    (a : Ideal (𝓞 F) → ℂ) (ha : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ‖a I‖ ≤ 1)
    {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} (hf : LogMellinPhysical f δ P)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun I : Ideal (𝓞 F) => ‖logIdealTerm a f X I‖) ∧
      Summable (logIdealTerm a f X) := by
  obtain ⟨C, hC0, hC⟩ := hf.rapid_decay 0 2
  refine logIdealTerm_summable_of_envelope a ha f hf.contDiffOn.continuousOn
    ⟨2, C, by norm_num, hC0, fun x hx => ?_⟩ X hX
  have h := hC x hx
  simpa using h

end DedekindZetaZeroFree.LargeSieve.Vendor

end
