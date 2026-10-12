module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterUniqueness
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.SmoothAnnularWeight
public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

theorem primitive_product_not_principal
    (u v : Ideal (𝓞 F)) (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (huv : u ⊔ v = ⊤) (hne : u * v ≠ ⊤)
    (ψ : RayClassCharacter F (u * v)) (hψ : ψ.IsPrimitive) :
    ¬ ψ.IsPrincipal := by
  intro hp
  exact hne (RayOperations.modulus_eq_top_of_primitive_principal ψ hψ hp)

theorem annular_diagonal_restricted_bound (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℝ) (hWcont : Continuous W) (hWnonneg : ∀ x, 0 ≤ W x)
    (hWsupp : ∀ x, x < 1 / 2 ∨ 5 / 2 < x → W x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : QuadraticHeckeFamily F c)
        (M : ℝ) (d : Ideal (𝓞 F)) (z : ℂ) (P : Ideal (𝓞 F) → Prop),
        1 ≤ M → Squarefree d → d ⊔ c = ⊤ →
        (∑ᶠ a : Ideal (𝓞 F),
          if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
            W ((Ideal.absNorm a : ℝ) / M) * ‖z * (Q.χ d) a‖ ^ 2
          else 0) ≤ C * M * ‖z‖ ^ 2 := by
  obtain ⟨x₀, -, hx₀max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2)) hWcont.continuousOn
  set B : ℝ := W x₀ with hBdef
  have hB0 : 0 ≤ B := hBdef ▸ hWnonneg x₀
  have hBW : ∀ t : ℝ, W t ≤ B := by
    intro t
    by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) (5 / 2)
    · exact hx₀max ht
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rw [hWsupp t ht]
      exact hB0
  obtain ⟨A, hA1, hA⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound F
  refine ⟨B * A * (5 / 2), by nlinarith [hB0, hA1], ?_⟩
  intro c Q M d z P hM hdsq hdc
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hz0 : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
  have hterm : ∀ a : Ideal (𝓞 F),
      (if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
        W ((Ideal.absNorm a : ℝ) / M) * ‖z * (Q.χ d) a‖ ^ 2 else 0) ≤ B * ‖z‖ ^ 2 := by
    intro a
    by_cases h : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a
    · rw [if_pos h]
      have hχ : ‖(Q.χ d) a‖ ≤ 1 := quadraticFamily_norm_le_one Q hdsq hdc a
      have hz : ‖z * (Q.χ d) a‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        have h1 : ‖z * (Q.χ d) a‖ ≤ ‖z‖ := by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left hχ (norm_nonneg z)).trans_eq (mul_one _)
        nlinarith [norm_nonneg (z * (Q.χ d) a), norm_nonneg z]
      exact mul_le_mul (hBW _) hz (by positivity) hB0
    · rw [if_neg h]
      exact mul_nonneg hB0 hz0
  have hsupp : Function.support (fun a : Ideal (𝓞 F) =>
      if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
        W ((Ideal.absNorm a : ℝ) / M) * ‖z * (Q.χ d) a‖ ^ 2 else 0)
      ⊆ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M) : Set (Ideal (𝓞 F))) := by
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    by_cases h : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a
    · rw [if_pos h] at ha
      have hWne : W ((Ideal.absNorm a : ℝ) / M) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at ha
        exact ha rfl
      have hlt : (Ideal.absNorm a : ℝ) / M ≤ 5 / 2 := by
        by_contra hcon
        exact hWne (hWsupp _ (Or.inr (not_le.mp hcon)))
      have : (Ideal.absNorm a : ℝ) ≤ (5 / 2) * M := by
        rw [div_le_iff₀ hMpos] at hlt
        linarith
      simpa using this
    · rw [if_neg h] at ha
      exact absurd rfl ha
  calc ∑ᶠ a : Ideal (𝓞 F),
        (if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
          W ((Ideal.absNorm a : ℝ) / M) * ‖z * (Q.χ d) a‖ ^ 2 else 0)
      = ∑ a ∈ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M),
          (if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
            W ((Ideal.absNorm a : ℝ) / M) * ‖z * (Q.χ d) a‖ ^ 2 else 0) :=
        finsum_eq_finsetSum_of_support_subset _ hsupp
    _ ≤ ∑ _a ∈ DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M), B * ‖z‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F ((5 / 2) * M)).card : ℝ) * (B * ‖z‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * ((5 / 2) * M)) * (B * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hA ((5 / 2) * M) (by nlinarith)) (mul_nonneg hB0 hz0)
    _ = B * A * (5 / 2) * M * ‖z‖ ^ 2 := by ring

noncomputable def diagonalContribution
    {c : Ideal (𝓞 F)} (Q : QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) (P : Ideal (𝓞 F) → Prop) : ℝ :=
  if d ∈ Sieve.paperShell F c N ∧ Q.cls d = g then
    ∑ᶠ a : Ideal (𝓞 F), if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
      W ((Ideal.absNorm a : ℝ) / M) * ‖lam d * (Q.χ d) a‖ ^ 2
    else 0
  else 0

theorem diagonalContribution_bound (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : QuadraticHeckeFamily F c)
        (M N : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
        (lam : Ideal (𝓞 F) → ℂ) (P : Ideal (𝓞 F) → Prop),
        1 ≤ M → 1 ≤ N →
        diagonalContribution Q W M N d g lam P ≤ C * M * ‖lam d‖ ^ 2 ∧
        diagonalContribution Q W M N d g lam P ≤
          C * M * ∑ b ∈ Sieve.paperShell F c N, ‖lam b‖ ^ 2 := by
  have hsupp : ∀ x : ℝ, x < 1 / 2 ∨ 5 / 2 < x → W x = 0 := by
    intro x hx
    refine hW.zero_outside x (fun hmem => ?_)
    exact hx.elim (fun h1 => absurd hmem.1 (not_le.mpr h1))
      (fun h2 => absurd hmem.2 (not_le.mpr h2))
  obtain ⟨C, hC0, hC⟩ := annular_diagonal_restricted_bound F W hW.smooth.continuous hW.nonneg hsupp
  refine ⟨C, hC0, ?_⟩
  intro c Q M N d g lam P hM hN
  have hCM : 0 ≤ C * M := mul_nonneg hC0 (by linarith)
  by_cases hd : d ∈ Sieve.paperShell F c N ∧ Q.cls d = g
  · obtain ⟨hdmem, hdcls⟩ := hd
    obtain ⟨hdsq, hdc, -, -⟩ := (Sieve.mem_paperShell F c N d).mp hdmem
    have hbound := hC c Q M d (lam d) P hM hdsq hdc
    have hval : diagonalContribution Q W M N d g lam P =
        ∑ᶠ a : Ideal (𝓞 F),
          if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ P a then
            W ((Ideal.absNorm a : ℝ) / M) * ‖lam d * (Q.χ d) a‖ ^ 2
          else 0 := by
      unfold diagonalContribution
      rw [if_pos ⟨hdmem, hdcls⟩]
    constructor
    · rw [hval]; exact hbound
    · rw [hval]
      have henergy : ‖lam d‖ ^ 2 ≤ Sieve.energy F c N lam := by
        unfold Sieve.energy
        exact Finset.single_le_sum (f := fun b => ‖lam b‖ ^ 2) (fun b _ => by positivity) hdmem
      exact hbound.trans (mul_le_mul_of_nonneg_left henergy hCM)
  · have h0 : diagonalContribution Q W M N d g lam P = 0 := by
      unfold diagonalContribution
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hd ⟨h1, h2⟩
    have hrhs : 0 ≤ C * M * ∑ b ∈ Sieve.paperShell F c N, ‖lam b‖ ^ 2 :=
      mul_nonneg hCM (Finset.sum_nonneg (fun b _ => by positivity))
    exact ⟨by rw [h0]; exact mul_nonneg hCM (by positivity), by rw [h0]; exact hrhs⟩

noncomputable def offDiagonalT3
    {c : Ideal (𝓞 F)} (Q : QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ b1 ∈ Sieve.paperShell F c N, ∑ b2 ∈ Sieve.paperShell F c N,
    if b1 ≠ b2 ∧ b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
      lam b1 * (starRingEnd ℂ) (lam b2) *
        (∑ a ∈ Sieve.kernelRows F c M K,
          (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
            (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a))
    else 0

noncomputable def t3Term {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : QuadraticHeckeFamily F c) (W : ℝ → ℝ) (M K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) (b1 b2 : Ideal (𝓞 F)) : ℂ :=
  if b1 ⊔ b2 = d ∧ Q.cls b1 = g ∧ Q.cls b2 = g then
    lam b1 * (starRingEnd ℂ) (lam b2) *
      (∑ a ∈ Sieve.kernelRows F c M K,
        (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
          (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a))
  else 0

noncomputable def t3Diag {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : QuadraticHeckeFamily F c) (W : ℝ → ℝ) (M K : ℝ)
    (lam : Ideal (𝓞 F) → ℂ) (b : Ideal (𝓞 F)) : ℂ :=
  lam b * (starRingEnd ℂ) (lam b) *
    (∑ a ∈ Sieve.kernelRows F c M K,
      (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
        (Q.χ b) a * (starRingEnd ℂ) ((Q.χ b) a))

private theorem sum_diagonal_split {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → α → ℂ) :
    (∑ x ∈ s, ∑ y ∈ s, f x y) =
      (∑ x ∈ s, ∑ y ∈ s, if x = y then f x y else 0) +
      (∑ x ∈ s, ∑ y ∈ s, if x ≠ y then f x y else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : x = y <;> simp [h]

theorem T3_eq_diagonal_add_offDiagonal
    {c : Ideal (𝓞 F)} (Q : QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : Sieve.SieveWeight W)
    (M N K : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hK : 0 < K)
    (d : Ideal (𝓞 F)) (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) :
    Sieve.T3 F c Q W M N K d g lam =
      (diagonalContribution Q W M N d g lam (fun a => K < Sieve.s a) : ℂ) +
        offDiagonalT3 Q W M N K d g lam := by
  have hT3 : Sieve.T3 F c Q W M N K d g lam =
      ∑ b1 ∈ Sieve.paperShell F c N, ∑ b2 ∈ Sieve.paperShell F c N,
        t3Term Q W M K d g lam b1 b2 := rfl
  rw [hT3, sum_diagonal_split (Sieve.paperShell F c N) (t3Term Q W M K d g lam)]
  have hdiag : (∑ b1 ∈ Sieve.paperShell F c N, ∑ b2 ∈ Sieve.paperShell F c N,
        if b1 = b2 then t3Term Q W M K d g lam b1 b2 else 0) =
      (diagonalContribution Q W M N d g lam (fun a => K < Sieve.s a) : ℂ) := by
    have hcollapse : ∀ b1 : Ideal (𝓞 F),
        (∑ b2 ∈ Sieve.paperShell F c N,
            if b1 = b2 then t3Term Q W M K d g lam b1 b2 else 0) =
          if b1 ∈ Sieve.paperShell F c N then t3Term Q W M K d g lam b1 b1 else 0 :=
      fun b1 => Finset.sum_ite_eq _ b1 (fun b2 => t3Term Q W M K d g lam b1 b2)
    have h1 : (∑ b1 ∈ Sieve.paperShell F c N, ∑ b2 ∈ Sieve.paperShell F c N,
          if b1 = b2 then t3Term Q W M K d g lam b1 b2 else 0) =
        ∑ b1 ∈ Sieve.paperShell F c N,
          (if b1 ∈ Sieve.paperShell F c N then t3Term Q W M K d g lam b1 b1 else 0) :=
      Finset.sum_congr rfl (fun b1 _ => hcollapse b1)
    have h2 : (∑ b1 ∈ Sieve.paperShell F c N,
          (if b1 ∈ Sieve.paperShell F c N then t3Term Q W M K d g lam b1 b1 else 0)) =
        ∑ b1 ∈ Sieve.paperShell F c N, t3Term Q W M K d g lam b1 b1 :=
      Finset.sum_congr rfl (fun b1 hb1 => by rw [if_pos hb1])
    have h3 : ∀ b : Ideal (𝓞 F), t3Term Q W M K d g lam b b =
        (if b = d ∧ Q.cls b = g then t3Diag Q W M K lam b else 0) := by
      intro b
      unfold t3Term t3Diag
      rw [sup_idem]
      by_cases h : b = d ∧ Q.cls b = g <;> simp [h]
    have h4 : (∑ b1 ∈ Sieve.paperShell F c N, t3Term Q W M K d g lam b1 b1) =
        ∑ b ∈ Sieve.paperShell F c N,
          (if b = d ∧ Q.cls b = g then t3Diag Q W M K lam b else 0) :=
      Finset.sum_congr rfl (fun b _ => h3 b)
    have hcongr : (∑ b ∈ Sieve.paperShell F c N,
          (if b = d ∧ Q.cls b = g then t3Diag Q W M K lam b else 0)) =
        ∑ b ∈ Sieve.paperShell F c N,
          (if b = d then (if Q.cls b = g then t3Diag Q W M K lam b else 0) else 0) :=
      Finset.sum_congr rfl (fun b _ => by by_cases h : b = d <;> simp [h])
    have h5 : (∑ b ∈ Sieve.paperShell F c N,
          (if b = d then (if Q.cls b = g then t3Diag Q W M K lam b else 0) else 0)) =
        (if d ∈ Sieve.paperShell F c N ∧ Q.cls d = g then t3Diag Q W M K lam d else 0) := by
      rw [Finset.sum_ite_eq' (Sieve.paperShell F c N) d
        (fun b => if Q.cls b = g then t3Diag Q W M K lam b else 0)]
      by_cases hd : d ∈ Sieve.paperShell F c N <;> by_cases hg : Q.cls d = g <;>
        simp [hd, hg]
    rw [h1, h2, h4, hcongr, h5]
    have hAd : t3Diag Q W M K lam d =
        ((∑ᶠ a : Ideal (𝓞 F), if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < Sieve.s a then
            W ((Ideal.absNorm a : ℝ) / M) * ‖lam d * (Q.χ d) a‖ ^ 2 else 0 : ℝ) : ℂ) := by
      unfold t3Diag
      have hsupp : Function.support (fun a : Ideal (𝓞 F) =>
          if a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < Sieve.s a then
            W ((Ideal.absNorm a : ℝ) / M) * ‖lam d * (Q.χ d) a‖ ^ 2 else 0)
          ⊆ (Sieve.kernelRows F c M K : Set (Ideal (𝓞 F))) := by
        intro a ha
        simp only [Function.mem_support, ne_eq] at ha
        by_cases h : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < Sieve.s a
        · rw [if_pos h] at ha
          have hWne : W ((Ideal.absNorm a : ℝ) / M) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at ha
            exact ha rfl
          have hle : (Ideal.absNorm a : ℝ) ≤ (5 / 2) * M := by
            have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
            have hlt : (Ideal.absNorm a : ℝ) / M ≤ 5 / 2 := by
              by_contra hcon
              exact hWne (hW.zero_outside _ (fun hmem =>
                absurd hmem.2 (not_le.mpr (not_le.mp hcon))))
            rw [div_le_iff₀ hMpos] at hlt
            linarith
          unfold Sieve.kernelRows
          exact Finset.mem_filter.mpr ⟨DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr hle, h⟩
        · rw [if_neg h] at ha
          exact absurd rfl ha
      rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have hCa : a ≠ ⊥ ∧ a ⊔ c = ⊤ ∧ K < Sieve.s a := by
        unfold Sieve.kernelRows at ha
        exact (Finset.mem_filter.mp ha).2
      rw [if_pos hCa]
      have h1 : ‖lam d * (Q.χ d) a‖ ^ 2 = ‖lam d‖ ^ 2 * ‖(Q.χ d) a‖ ^ 2 := by
        rw [norm_mul]; ring
      have hx : ((‖lam d‖ ^ 2 : ℝ) : ℂ) = lam d * (starRingEnd ℂ) (lam d) := by
        push_cast; rw [← Complex.mul_conj']
      have hy : ((‖(Q.χ d) a‖ ^ 2 : ℝ) : ℂ) =
          (Q.χ d) a * (starRingEnd ℂ) ((Q.χ d) a) := by
        push_cast; rw [← Complex.mul_conj']
      rw [h1, Complex.ofReal_mul, Complex.ofReal_mul, hx, hy]
      ring
    by_cases hd : d ∈ Sieve.paperShell F c N ∧ Q.cls d = g
    · rw [if_pos hd, hAd]
      unfold diagonalContribution
      rw [if_pos hd]
    · rw [if_neg hd]
      unfold diagonalContribution
      rw [if_neg hd]
      norm_num
  have hoff : (∑ b1 ∈ Sieve.paperShell F c N, ∑ b2 ∈ Sieve.paperShell F c N,
        if b1 ≠ b2 then t3Term Q W M K d g lam b1 b2 else 0) =
      offDiagonalT3 Q W M N K d g lam := by
    unfold offDiagonalT3
    refine Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => ?_))
    by_cases h : b1 = b2
    · simp [h]
    · unfold t3Term
      simp [h]
  rw [hdiag, hoff]

end DedekindZetaZeroFree.LargeSieve
