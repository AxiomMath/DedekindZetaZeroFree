module

public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma paperShell_subset_boundedNormIdeals (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) :
    paperShell F c T ⊆ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * T) := by
  intro I hI
  rw [mem_paperShell] at hI
  rw [DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals]
  exact hI.2.2.2

private lemma card_paperShell_le (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) {A : ℝ}
    (count : ∀ X : ℝ, 1 ≤ X → ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (hT : 1 ≤ 2 * T) :
    ((paperShell F c T).card : ℝ) ≤ A * (2 * T) := by
  have h1 : (paperShell F c T).card ≤ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * T)).card :=
    Finset.card_le_card (paperShell_subset_boundedNormIdeals F c T)
  have h2 : ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * T)).card : ℝ) ≤ A * (2 * T) := count (2 * T) hT
  exact le_trans (by exact_mod_cast h1) h2

private lemma paperShell_subset_singleton_top (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) (hT : T < 1) :
    paperShell F c T ⊆ {⊤} := by
  intro I hI
  rw [Finset.mem_singleton]
  rw [mem_paperShell] at hI
  obtain ⟨hsf, hcop, -, hle⟩ := hI
  have hmem : I ∈ idealAdmissibleFinset F c (2 * T) :=
    (mem_idealAdmissibleFinset F c (2 * T) I).mpr ⟨hsf, hcop, hle⟩
  have hne : I ≠ ⊥ := fun h => bot_not_mem_idealAdmissibleFinset F c (2 * T) (h ▸ hmem)
  have hne' : Ideal.absNorm I ≠ 0 := fun h0 =>
    hne ((Ideal.absNorm_eq_zero_iff).mp h0)
  have hpos : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr hne'
  have hlt2 : Ideal.absNorm I < 2 := by
    have h : (Ideal.absNorm I : ℝ) < 2 := lt_of_le_of_lt hle (by linarith)
    exact_mod_cast h
  exact Ideal.absNorm_eq_one_iff.mp (le_antisymm (by omega) hpos)

private lemma card_paperShell_le_one (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) (hT : T < 1) : (paperShell F c T).card ≤ 1 := by
  have := Finset.card_le_card (paperShell_subset_singleton_top F c T hT)
  simpa using this

private lemma paperShell_chi_norm_le_one
    {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    {q : Ideal (𝓞 F)} (hcq : c ∣ q) {T : ℝ}
    {u : Ideal (𝓞 F)} (hu : u ∈ paperShell F q T) (v : Ideal (𝓞 F)) :
    ‖(Q.χ u) v‖ ≤ 1 := by
  rw [mem_paperShell] at hu
  obtain ⟨hsf, hcop, -, -⟩ := hu
  have hqc : q ≤ c := by
    obtain ⟨d, rfl⟩ := hcq
    exact Ideal.mul_le_left
  have hc : u ⊔ c = ⊤ :=
    top_le_iff.mp (le_trans (le_of_eq hcop.symm) (sup_le_sup_left hqc u))
  exact DedekindZetaZeroFree.LargeSieve.quadraticFamily_norm_le_one Q hsf hc v

private lemma inner_paperShell_sq_le
    {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    {q : Ideal (𝓞 F)} (hcq : c ∣ q) (T : ℝ)
    (μ α : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1) (v : Ideal (𝓞 F)) :
    ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 ≤
      ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
  have hterm : ∀ u ∈ paperShell F q T, ‖μ u * α u * (Q.χ u) v‖ ≤ ‖μ u‖ := by
    intro u hu
    rw [norm_mul, norm_mul]
    have h1 := hα u hu
    have h2 := paperShell_chi_norm_le_one Q hcq hu v
    have hprod : ‖α u‖ * ‖(Q.χ u) v‖ ≤ 1 := by
      simpa using mul_le_mul h1 h2 (norm_nonneg ((Q.χ u) v)) zero_le_one
    calc ‖μ u‖ * ‖α u‖ * ‖(Q.χ u) v‖ = ‖μ u‖ * (‖α u‖ * ‖(Q.χ u) v‖) := by ring
      _ ≤ ‖μ u‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖μ u‖ := by ring
  have hsum : ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ≤
      ∑ u ∈ paperShell F q T, ‖μ u‖ :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (paperShell F q T)
      (fun u => ‖μ u‖) (fun _ => (1 : ℝ))
  have hCS' : (∑ u ∈ paperShell F q T, ‖μ u‖) ^ 2 ≤
      (∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) * ((paperShell F q T).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hCS
  calc ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2
      ≤ (∑ u ∈ paperShell F q T, ‖μ u‖) ^ 2 := by
        nlinarith [hsum, norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v),
          Finset.sum_nonneg (fun u (_ : u ∈ paperShell F q T) => norm_nonneg (μ u))]
    _ ≤ (∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) * ((paperShell F q T).card : ℝ) := hCS'
    _ = ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by ring

private lemma masked_sum_le_card_mul
    {F : Type} [Field F] [NumberField F]
    {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    {q : Ideal (𝓞 F)} (hcq : c ∣ q) (S T : ℝ)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q S, ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q S, ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ ((paperShell F q S).card : ℝ) *
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) := by
  have hstep : ∀ v ∈ paperShell F q S,
      ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2 ≤
        ((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
    intro v hv
    have hb := hβ v hv
    have hin := inner_paperShell_sq_le Q hcq T μ α hα v
    have hX : ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ≤
        ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ := by
      rw [norm_mul]
      calc ‖β v‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = _ := one_mul _
    calc ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2
        ≤ ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 := by
          nlinarith [hX,
            norm_nonneg (β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)),
            norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)]
      _ ≤ _ := hin
  calc (∑ v ∈ paperShell F q S, ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ ∑ v ∈ paperShell F q S,
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) :=
        Finset.sum_le_sum hstep
    _ = ((paperShell F q S).card : ℝ) *
          (((paperShell F q T).card : ℝ) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

private lemma two_A_scale_le {A C ε x E : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hx : 1 ≤ x) (hE : 0 ≤ E) :
    2 * A * x * E ≤ (C + 2 * A + 1) * x ^ ε * (x + 1) * E := by
  have hr : 1 ≤ x ^ ε := Real.one_le_rpow hx hε
  have hx0 : 0 ≤ x := by linarith
  have hCA0 : 0 ≤ C + 2 * A + 1 := by linarith
  have hCA : 2 * A ≤ C + 2 * A + 1 := by linarith
  have step1 : 2 * A * x ≤ (C + 2 * A + 1) * x := mul_le_mul_of_nonneg_right hCA hx0
  have hxl : x ≤ x ^ ε * (x + 1) := by
    calc x = 1 * x := by ring
      _ ≤ x ^ ε * x := mul_le_mul_of_nonneg_right hr hx0
      _ ≤ x ^ ε * (x + 1) := mul_le_mul_of_nonneg_left (by linarith) (le_trans zero_le_one hr)
  calc 2 * A * x * E ≤ (C + 2 * A + 1) * x * E := mul_le_mul_of_nonneg_right step1 hE
    _ ≤ (C + 2 * A + 1) * x ^ ε * (x + 1) * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        calc (C + 2 * A + 1) * x ≤ (C + 2 * A + 1) * (x ^ ε * (x + 1)) :=
              mul_le_mul_of_nonneg_left hxl hCA0
          _ = (C + 2 * A + 1) * x ^ ε * (x + 1) := by ring

theorem peeling_masked_small_shells
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (ε C A : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (count : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (core : ∀ S T : ℝ, 1 ≤ S → 1 ≤ T → ∀ μ : Ideal (𝓞 F) → ℂ,
      (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2) ≤
        C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2)
    (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q T, ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q S, ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q S,
      ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2) ≤
      (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) *
        ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 := by
  set E := ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg (fun u _ => sq_nonneg _)
  rcases le_or_gt 1 S with hS1 | hS1
  · rcases le_or_gt 1 T with hT1 | hT1
    ·
      have hcore' := core S T hS1 hT1 (fun u => μ u * α u)
      have hinner : ∑ u ∈ paperShell F q T, ‖μ u * α u‖ ^ 2 ≤ E := by
        rw [hE]
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul, mul_pow]
        have h := hα u hu
        have h2 : ‖α u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h
        calc ‖μ u‖ ^ 2 * ‖α u‖ ^ 2 ≤ ‖μ u‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = ‖μ u‖ ^ 2 := by ring
      have hstep1 : (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ∑ v ∈ paperShell F q S,
            ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        have hb := hβ v hv
        have hX : ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ≤
            ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ := by
          rw [norm_mul]
          calc ‖β v‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
            _ = _ := one_mul _
        nlinarith [hX,
          norm_nonneg (β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)),
          norm_nonneg (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)]
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ (∑ v ∈ paperShell F q S,
              ‖∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v‖ ^ 2) := hstep1
        _ ≤ C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u * α u‖ ^ 2 := hcore'
        _ ≤ C * (S * T) ^ ε * (S + T) * E :=
              mul_le_mul_of_nonneg_left hinner (by
                have h1 : 0 ≤ (S * T) ^ ε := Real.rpow_nonneg (by positivity) ε
                positivity)
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
              rw [max_eq_right hS1, max_eq_right hT1]
              have hP : 0 ≤ (S * T) ^ ε * (S + T) * E := by
                have h1 : 0 ≤ (S * T) ^ ε := Real.rpow_nonneg (by positivity) ε
                positivity
              nlinarith [hP, hA, hC, hE0]
    ·
      have hcrude := masked_sum_le_card_mul Q hcq S T μ α β hα hβ
      have hcardT : ((paperShell F q T).card : ℝ) ≤ 1 := by
        exact_mod_cast card_paperShell_le_one F q T hT1
      have hcardS : ((paperShell F q S).card : ℝ) ≤ A * (2 * S) :=
        card_paperShell_le F q S count (by linarith)
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
          ≤ (2 * A * S) * E := by
        have h1 : ((paperShell F q T).card : ℝ) * E ≤ 1 * E :=
          mul_le_mul_of_nonneg_right hcardT hE0
        have h2 : ((paperShell F q S).card : ℝ) ≤ 2 * A * S := by nlinarith [hcardS]
        calc ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
            ≤ ((paperShell F q S).card : ℝ) * (1 * E) :=
              mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
          _ = ((paperShell F q S).card : ℝ) * E := by ring
          _ ≤ (2 * A * S) * E := mul_le_mul_of_nonneg_right h2 hE0
      have htarget : (2 * A * S) * E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_right hS1, max_eq_left (le_of_lt hT1), mul_one]
        exact two_A_scale_le hA hC hε hS1 hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := hcrude
        _ ≤ (2 * A * S) * E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget
  · rcases le_or_gt 1 T with hT1 | hT1
    ·
      have hcrude := masked_sum_le_card_mul Q hcq S T μ α β hα hβ
      have hcardS : ((paperShell F q S).card : ℝ) ≤ 1 := by
        exact_mod_cast card_paperShell_le_one F q S hS1
      have hcardT : ((paperShell F q T).card : ℝ) ≤ A * (2 * T) :=
        card_paperShell_le F q T count (by linarith)
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
          ≤ (2 * A * T) * E := by
        have h1 : ((paperShell F q S).card : ℝ) ≤ 1 := hcardS
        have h2 : ((paperShell F q T).card : ℝ) ≤ 2 * A * T := by nlinarith [hcardT]
        have hnn : 0 ≤ ((paperShell F q T).card : ℝ) * E := by positivity
        calc ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
            ≤ 1 * (((paperShell F q T).card : ℝ) * E) := mul_le_mul_of_nonneg_right h1 hnn
          _ = ((paperShell F q T).card : ℝ) * E := by ring
          _ ≤ (2 * A * T) * E := mul_le_mul_of_nonneg_right h2 hE0
      have htarget : (2 * A * T) * E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_left (le_of_lt hS1), max_eq_right hT1, one_mul, show (1 : ℝ) + T = T + 1 by ring]
        exact two_A_scale_le hA hC hε hT1 hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := hcrude
        _ ≤ (2 * A * T) * E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget
    ·
      have hcrude := masked_sum_le_card_mul Q hcq S T μ α β hα hβ
      have hcardS : ((paperShell F q S).card : ℝ) ≤ 1 := by
        exact_mod_cast card_paperShell_le_one F q S hS1
      have hcardT : ((paperShell F q T).card : ℝ) ≤ 1 := by
        exact_mod_cast card_paperShell_le_one F q T hT1
      have hmid : ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) ≤ E := by
        have h1 : ((paperShell F q S).card : ℝ) ≤ 1 := hcardS
        have h2 : ((paperShell F q T).card : ℝ) * E ≤ 1 * E :=
          mul_le_mul_of_nonneg_right hcardT hE0
        have hnn : 0 ≤ ((paperShell F q T).card : ℝ) * E := by positivity
        calc ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E)
            ≤ 1 * (1 * E) := mul_le_mul h1 h2 hnn zero_le_one
          _ = E := by ring
      have htarget : E ≤
          (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := by
        rw [max_eq_left (le_of_lt hS1), max_eq_left (le_of_lt hT1)]
        have hr : (1 : ℝ) ≤ ((1 : ℝ) * 1) ^ ε := by
          rw [mul_one]; exact Real.one_le_rpow le_rfl hε
        have hK0 : 0 ≤ C + 2 * A + 1 := by linarith
        have h1 : (1 : ℝ) ≤ C + 2 * A + 1 := by linarith
        have h2 : (1 : ℝ) ≤ (1 + 1 : ℝ) := by norm_num
        have hmain : (1 : ℝ) ≤ (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) := by
          have hinner : (1 : ℝ) * 1 ≤ (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε :=
            mul_le_mul h1 hr zero_le_one hK0
          have houter : ((1 : ℝ) * 1) * 1 ≤
              ((C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε) * (1 + 1) :=
            mul_le_mul hinner h2 (by norm_num) (by positivity)
          calc (1 : ℝ) = (1 * 1) * 1 := by ring
            _ ≤ ((C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε) * (1 + 1) := houter
            _ = (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) := by ring
        calc E = 1 * E := by ring
          _ ≤ (C + 2 * A + 1) * ((1 : ℝ) * 1) ^ ε * (1 + 1) * E :=
              mul_le_mul_of_nonneg_right hmain hE0
      calc (∑ v ∈ paperShell F q S,
            ‖β v * (∑ u ∈ paperShell F q T, μ u * α u * (Q.χ u) v)‖ ^ 2)
          ≤ ((paperShell F q S).card : ℝ) * (((paperShell F q T).card : ℝ) * E) := hcrude
        _ ≤ E := hmid
        _ ≤ (C + 2 * A + 1) * (max 1 S * max 1 T) ^ ε * (max 1 S + max 1 T) * E := htarget

theorem peeling_masked_small_shells_rescaled
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (ε C A : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : 1 ≤ A)
    (count : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (core : ∀ S T : ℝ, 1 ≤ S → 1 ≤ T → ∀ μ : Ideal (𝓞 F) → ℂ,
      (∑ v ∈ paperShell F q S, ‖∑ u ∈ paperShell F q T, μ u * (Q.χ u) v‖ ^ 2) ≤
        C * (S * T) ^ ε * (S + T) * ∑ u ∈ paperShell F q T, ‖μ u‖ ^ 2)
    (M N R T0 : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hR : 1 ≤ R) (hT0 : 1 ≤ T0)
    (μ α β : Ideal (𝓞 F) → ℂ)
    (hα : ∀ u ∈ paperShell F q (N / T0), ‖α u‖ ≤ 1)
    (hβ : ∀ v ∈ paperShell F q (M / R), ‖β v‖ ≤ 1) :
    (∑ v ∈ paperShell F q (M / R),
      ‖β v * (∑ u ∈ paperShell F q (N / T0), μ u * α u * (Q.χ u) v)‖ ^ 2) ≤
      (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
        ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hT0pos : (0 : ℝ) < T0 := by linarith
  have hMpos : 0 < M / R := div_pos (by linarith) hRpos
  have hNpos : 0 < N / T0 := div_pos (by linarith) hT0pos
  have hmain := peeling_masked_small_shells F c Q q hq hcq ε C A hε hC hA count core
      (M / R) (N / T0) hMpos hNpos μ α β hα hβ
  have hSle : max 1 (M / R) ≤ M := by
    apply max_le (by linarith)
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hTle : max 1 (N / T0) ≤ N := by
    apply max_le (by linarith)
    rw [div_le_iff₀ hT0pos]
    nlinarith
  have hS0 : 0 ≤ max 1 (M / R) := le_trans zero_le_one (le_max_left _ _)
  have hT0' : 0 ≤ max 1 (N / T0) := le_trans zero_le_one (le_max_left _ _)
  have hK : 0 ≤ C + 2 * A + 1 := by linarith
  have hE : 0 ≤ ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 :=
    Finset.sum_nonneg (fun u _ => sq_nonneg _)
  have hprod : max 1 (M / R) * max 1 (N / T0) ≤ M * N :=
    mul_le_mul hSle hTle hT0' (by linarith)
  have hrpow : (max 1 (M / R) * max 1 (N / T0)) ^ ε ≤ (M * N) ^ ε :=
    Real.rpow_le_rpow (mul_nonneg hS0 hT0') hprod hε
  have hsum : max 1 (M / R) + max 1 (N / T0) ≤ M + N := by linarith
  calc (∑ v ∈ paperShell F q (M / R),
        ‖β v * (∑ u ∈ paperShell F q (N / T0), μ u * α u * (Q.χ u) v)‖ ^ 2)
      ≤ (C + 2 * A + 1) * (max 1 (M / R) * max 1 (N / T0)) ^ ε *
          (max 1 (M / R) + max 1 (N / T0)) * ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := hmain
    _ ≤ (C + 2 * A + 1) * (M * N) ^ ε * (M + N) *
          ∑ u ∈ paperShell F q (N / T0), ‖μ u‖ ^ 2 := by
        gcongr

end DedekindZetaZeroFree.LargeSieve.Sieve
