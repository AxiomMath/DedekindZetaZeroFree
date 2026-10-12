module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.ExceptionalMasks
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MaskedCoreShellBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ExceptionalShellReindexing

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

local instance exceptionalShellSharpBoundsClassGroup (Q : QuadraticHeckeFamily F c) : Group Q.G := Q.instGroup

local instance exceptionalShellSharpBoundsClassFinite (Q : QuadraticHeckeFamily F c) : Finite Q.G := Q.instFinite
noncomputable local instance exceptionalShellSharpBoundsClassFintype (Q : QuadraticHeckeFamily F c) : Fintype Q.G :=
  Fintype.ofFinite Q.G

private lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  calc ‖∑ i ∈ s, z i‖ ^ 2
      ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s z) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

private lemma norm_sum_sq_nested_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (z : ι → κ → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ t, z i j‖ ^ 2 ≤
      (s.card : ℝ) * (t.card : ℝ) * ∑ i ∈ s, ∑ j ∈ t, ‖z i j‖ ^ 2 := by
  calc ‖∑ i ∈ s, ∑ j ∈ t, z i j‖ ^ 2
      ≤ (s.card : ℝ) * ∑ i ∈ s, ‖∑ j ∈ t, z i j‖ ^ 2 :=
        norm_sum_sq_le_card_mul_sum_norm_sq s (fun i => ∑ j ∈ t, z i j)
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ((t.card : ℝ) * ∑ j ∈ t, ‖z i j‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        exact norm_sum_sq_le_card_mul_sum_norm_sq t (z i)
    _ = (s.card : ℝ) * ((t.card : ℝ) * ∑ i ∈ s, ∑ j ∈ t, ‖z i j‖ ^ 2) := by
        congr 1
        exact (Finset.mul_sum s (fun i => ∑ j ∈ t, ‖z i j‖ ^ 2) (t.card : ℝ)).symm
    _ = (s.card : ℝ) * (t.card : ℝ) * ∑ i ∈ s, ∑ j ∈ t, ‖z i j‖ ^ 2 := by ring

private lemma sum_const_mul {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ℝ) (f : ι → ℝ) :
    (∑ i ∈ s, c * f i) = c * ∑ i ∈ s, f i :=
  (Finset.mul_sum s f c).symm

private lemma sum_swap_three {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (s : Finset ι) (t : Finset κ) (u : Finset ν) (f : ι → κ → ν → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) = ∑ j ∈ t, ∑ k ∈ u, ∑ i ∈ s, f i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

noncomputable def exceptionalMaskedShellForm (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ)
    (r t : Ideal (𝓞 F)) (g : Q.G) : ℝ :=
  ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
    ‖exceptionalRowMask Q t g v *
      (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
        lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2

theorem peeling_sharp_domination (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (lam : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ paperShell F c M,
      ‖∑ b ∈ paperShell F c N, lam b * (Q.χ b) a‖ ^ 2) ≤
      ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
        ∑ r ∈ exceptionalDivisors F c q,
          ∑ t ∈ exceptionalDivisors F c q,
            ∑ g : Q.G, exceptionalMaskedShellForm Q q M N lam r t g := by
  classical
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN

  have hreindex : (∑ a ∈ paperShell F c M,
        ‖∑ b ∈ paperShell F c N, lam b * (Q.χ b) a‖ ^ 2)
      = ∑ r ∈ exceptionalDivisors F c q,
          ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
            ‖∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              exceptionalRowMask Q t g v *
                (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2 := by
    rw [exceptional_shell_sum hq hcq M hM0]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun v hv => ?_
    have hv' := (mem_paperShell F q (M / (Ideal.absNorm r : ℝ)) v).mp hv
    rw [exceptional_shell_sum hq hcq N hN0 (fun b => lam b * (Q.χ b) (r * v))]
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
    refine Finset.sum_congr rfl fun t ht => ?_
    exact peeling_mask_transport_sum Q q hq hcq H r t v hr ht hv'.1 hv'.2.1
      (paperShell F q (N / (Ideal.absNorm t : ℝ)))
      (fun u hu =>
        let h := (mem_paperShell F q (N / (Ideal.absNorm t : ℝ)) u).mp hu
        ⟨h.1, h.2.1⟩) lam

  have hcs : (∑ r ∈ exceptionalDivisors F c q,
          ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
            ‖∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              exceptionalRowMask Q t g v *
                (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2)
      ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ∑ r ∈ exceptionalDivisors F c q,
            ∑ t ∈ exceptionalDivisors F c q,
              ∑ g : Q.G, exceptionalMaskedShellForm Q q M N lam r t g := by
    have hpt : ∀ r ∈ exceptionalDivisors F c q,
        ∀ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
        ‖∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              exceptionalRowMask Q t g v *
                (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2
        ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
            ‖exceptionalRowMask Q t g v *
                (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2 := by
      intro r hr v hv
      have h := norm_sum_sq_nested_le (exceptionalDivisors F c q) (Finset.univ : Finset Q.G)
        (fun t g => exceptionalRowMask Q t g v *
          (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
            lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v))
      simpa [Nat.card_eq_fintype_card] using h
    have hsum : (∑ r ∈ exceptionalDivisors F c q,
          ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
            ‖∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              exceptionalRowMask Q t g v *
                (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2)
        ≤ ∑ r ∈ exceptionalDivisors F c q,
            ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
              ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
                ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
                  ‖exceptionalRowMask Q t g v *
                    (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                      lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2 :=
      Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun v hv => hpt r hr v hv
    refine hsum.trans (le_of_eq ?_)

    simp only [exceptionalMaskedShellForm]
    refine (Finset.sum_congr rfl fun r _ =>
      sum_const_mul (paperShell F q (M / (Ideal.absNorm r : ℝ)))
        (((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ))
        (fun v => ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
          ‖exceptionalRowMask Q t g v *
            (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
              lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2)).trans ?_
    refine (sum_const_mul (exceptionalDivisors F c q)
        (((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ))
        (fun r => ∑ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
          ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
          ‖exceptionalRowMask Q t g v *
            (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
              lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2)).trans ?_
    congr 1
    exact Finset.sum_congr rfl fun r _ =>
      sum_swap_three (paperShell F q (M / (Ideal.absNorm r : ℝ)))
        (exceptionalDivisors F c q) (Finset.univ : Finset Q.G)
        (fun v t g => ‖exceptionalRowMask Q t g v *
          (∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
            lam (t * u) * exceptionalColumnMask Q r t g u * (Q.χ u) v)‖ ^ 2)
  calc (∑ a ∈ paperShell F c M,
        ‖∑ b ∈ paperShell F c N, lam b * (Q.χ b) a‖ ^ 2)
      = _ := hreindex
    _ ≤ _ := hcs

theorem peeling_sharp_domination_energy (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (N : ℝ) (hN : 1 ≤ N) (lam : Ideal (𝓞 F) → ℂ)
    (r : Ideal (𝓞 F)) (hr : r ∈ exceptionalDivisors F c q) :
    (∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
      ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
        ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2) ≤
      ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 := by
  classical
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN

  have hstep : ∀ t ∈ exceptionalDivisors F c q,
      ∀ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
      (∑ g : Q.G, ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2) ≤
        ‖lam (t * u)‖ ^ 2 := by
    intro t ht u hu
    obtain ⟨hu1, hu2, -, -⟩ :=
      (mem_paperShell F q (N / (Ideal.absNorm t : ℝ)) u).mp hu
    have hval : ‖(Q.χ (t * u)) r‖ ≤ 1 := by
      have h := norm_exceptionalColumnMask_le_one Q q hq hcq r t (Q.cls u) u hr ht hu1 hu2
      rwa [exceptionalColumnMask, if_pos rfl] at h
    have hcollapse : (∑ g : Q.G, ‖exceptionalColumnMask Q r t g u‖ ^ 2) ≤ 1 := by
      have hfun : ∀ g : Q.G,
          ‖exceptionalColumnMask Q r t g u‖ ^ 2 =
            if Q.cls u = g then ‖(Q.χ (t * u)) r‖ ^ 2 else 0 := by
        intro g
        by_cases h : Q.cls u = g <;> simp [exceptionalColumnMask, h]
      rw [Finset.sum_congr rfl fun g _ => hfun g, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      exact pow_le_one₀ (norm_nonneg _) hval
    calc ∑ g : Q.G, ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2
        = ∑ g : Q.G, ‖lam (t * u)‖ ^ 2 * ‖exceptionalColumnMask Q r t g u‖ ^ 2 := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [norm_mul, mul_pow]
      _ = ‖lam (t * u)‖ ^ 2 * ∑ g : Q.G, ‖exceptionalColumnMask Q r t g u‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ‖lam (t * u)‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hcollapse (sq_nonneg _)
      _ = ‖lam (t * u)‖ ^ 2 := mul_one _
  calc (∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
        ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
          ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)
      = ∑ t ∈ exceptionalDivisors F c q,
          ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
            ∑ g : Q.G, ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2 := by
        refine Finset.sum_congr rfl fun t ht => Finset.sum_comm
    _ ≤ ∑ t ∈ exceptionalDivisors F c q,
          ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)), ‖lam (t * u)‖ ^ 2 :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun u hu => hstep t ht u hu
    _ = ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 :=
        exceptional_shell_energy hq hcq N hN0 lam

noncomputable def peelingSharpConstant
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (C A : ℝ) : ℝ :=
  ((exceptionalDivisors F c q).card : ℝ) ^ 2 * (Nat.card Q.G : ℝ) * (C + 2 * A + 1)

theorem peelingSharpConstant_nonneg (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (C A : ℝ) (hC : 0 ≤ C) (hA : 1 ≤ A) :
    0 ≤ peelingSharpConstant F c Q q C A := by
  unfold peelingSharpConstant
  have h1 : (0 : ℝ) ≤ ((exceptionalDivisors F c q).card : ℝ) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ (Nat.card Q.G : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ C + 2 * A + 1 := by linarith
  exact mul_nonneg (mul_nonneg h1 h2) h3

theorem peeling_sharp_domination_bound (Q : QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (H : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    (ε C A : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (count : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (core : ∀ S T : ℝ, 1 ≤ S → 1 ≤ T → ∀ μ : Ideal (𝓞 F) → ℂ,
      (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2) ≤
        C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (lam : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ paperShell F c M,
      ‖∑ b ∈ paperShell F c N, lam b * (Q.χ b) a‖ ^ 2) ≤
      peelingSharpConstant F c Q q C A * (M * N) ^ ε * (M + N) *
        ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 := by
  classical
  have hdom := peeling_sharp_domination Q q hq hcq H M N hM hN lam
  have henergy : ∀ r ∈ exceptionalDivisors F c q,
      (∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
        ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
          ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2) ≤
        ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 :=
    fun r hr => peeling_sharp_domination_energy Q q hq hcq N hN lam r hr

  have hP : ∀ r ∈ exceptionalDivisors F c q, ∀ t ∈ exceptionalDivisors F c q, ∀ g : Q.G,
      exceptionalMaskedShellForm Q q M N lam r t g ≤
        (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
          ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
            ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2 := by
    intro r hr t ht g
    have hr1 : 1 ≤ (Ideal.absNorm r : ℝ) := (exceptionalDivisors_properties hq hr).2.2.2.2
    have ht1 : 1 ≤ (Ideal.absNorm t : ℝ) := (exceptionalDivisors_properties hq ht).2.2.2.2
    have hβ : ∀ v ∈ paperShell F q (M / (Ideal.absNorm r : ℝ)),
        ‖exceptionalRowMask Q t g v‖ ≤ 1 := by
      intro v hv
      obtain ⟨hv1, hv2, -, -⟩ :=
        (mem_paperShell F q (M / (Ideal.absNorm r : ℝ)) v).mp hv
      exact norm_exceptionalRowMask_le_one Q q hq hcq t g v ht hv1 hv2
    have h := peeling_masked_small_shells_rescaled F c Q q hq hcq ε C A hε hC hA count core
      M N (Ideal.absNorm r : ℝ) (Ideal.absNorm t : ℝ) hM hN hr1 ht1
      (fun u => lam (t * u) * exceptionalColumnMask Q r t g u) (fun _ => (1 : ℂ))
      (fun v => exceptionalRowMask Q t g v) (fun _ _ => by simp) hβ
    simpa only [exceptionalMaskedShellForm, mul_one] using h

  have hsumE : (∑ r ∈ exceptionalDivisors F c q,
        ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
          ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
            ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)
      ≤ ((exceptionalDivisors F c q).card : ℝ) * ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 := by
    have h1 : (∑ r ∈ exceptionalDivisors F c q,
          ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
            ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
              ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)
        ≤ ∑ _r ∈ exceptionalDivisors F c q, ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 :=
      Finset.sum_le_sum fun r hr => henergy r hr
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  have hK : 0 ≤ (C + 2 * A + 1) * (M * N) ^ ε * (M + N) := by
    have hMN : (0 : ℝ) < M * N := mul_pos (by linarith) (by linarith)
    have h1 : 0 ≤ (M * N) ^ ε := Real.rpow_nonneg hMN.le _
    have h2 : 0 ≤ C + 2 * A + 1 := by linarith
    have h3 : 0 ≤ M + N := by linarith
    exact mul_nonneg (mul_nonneg h2 h1) h3
  have hDk : 0 ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfactor : ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
        (∑ r ∈ exceptionalDivisors F c q,
          ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
            (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
              ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)
      = ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
        ((C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
          ∑ r ∈ exceptionalDivisors F c q,
            ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2) := by
    congr 1
    refine (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ =>
      sum_const_mul (Finset.univ : Finset Q.G)
        ((C + 2 * A + 1) * (M * N) ^ ε * (M + N))
        (fun g => ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
          ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)).trans ?_
    refine (Finset.sum_congr rfl fun r _ =>
      sum_const_mul (exceptionalDivisors F c q)
        ((C + 2 * A + 1) * (M * N) ^ ε * (M + N))
        (fun t => ∑ g : Q.G, ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
          ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)).trans ?_
    exact sum_const_mul (exceptionalDivisors F c q)
      ((C + 2 * A + 1) * (M * N) ^ ε * (M + N))
      (fun r => ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
        ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
          ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2)
  calc (∑ a ∈ paperShell F c M,
        ‖∑ b ∈ paperShell F c N, lam b * (Q.χ b) a‖ ^ 2)
      ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ∑ r ∈ exceptionalDivisors F c q,
            ∑ t ∈ exceptionalDivisors F c q,
              ∑ g : Q.G, exceptionalMaskedShellForm Q q M N lam r t g := hdom
    _ ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ∑ r ∈ exceptionalDivisors F c q,
            ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
              (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
                ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hDk
        refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun t ht =>
          Finset.sum_le_sum fun g _ => hP r hr t ht g
    _ = ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ((C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
            ∑ r ∈ exceptionalDivisors F c q,
              ∑ t ∈ exceptionalDivisors F c q, ∑ g : Q.G,
                ∑ u ∈ paperShell F q (N / (Ideal.absNorm t : ℝ)),
                  ‖lam (t * u) * exceptionalColumnMask Q r t g u‖ ^ 2) := hfactor
    _ ≤ ((exceptionalDivisors F c q).card : ℝ) * (Nat.card Q.G : ℝ) *
          ((C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
            (((exceptionalDivisors F c q).card : ℝ) *
              ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumE hK) hDk
    _ = peelingSharpConstant F c Q q C A * (M * N) ^ ε * (M + N) *
          ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2 := by
        unfold peelingSharpConstant
        ring

end DedekindZetaZeroFree.LargeSieve.Sieve
