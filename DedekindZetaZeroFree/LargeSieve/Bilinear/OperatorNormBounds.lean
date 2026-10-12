module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeKernelNorm

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

private lemma row_bound {ι : Type*} (L : Finset ι) (A x : ι → ℂ) :
    ‖∑ i ∈ L, x i * A i‖ ^ 2 ≤ (∑ i ∈ L, ‖x i‖ ^ 2) * ∑ i ∈ L, ‖A i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ L, ‖x i * A i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ = (∑ i ∈ L, ‖x i‖ * ‖A i‖) ^ 2 := by simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq L _ _
private lemma weighted_bound {ι ρ : Type*} (L : Finset ι) (R : Finset ρ)
    (w : ρ → ℝ) (A : ρ → ι → ℂ) (x : ι → ℂ) :
    (∑ r ∈ R, w r * ‖∑ i ∈ L, x i * A r i‖ ^ 2) ≤
      (∑ r ∈ R, |w r| * ∑ i ∈ L, ‖A r i‖ ^ 2) * (∑ i ∈ L, ‖x i‖ ^ 2) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  calc
    _ ≤ |w r| * ‖∑ i ∈ L, x i * A r i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    _ ≤ |w r| * ((∑ i ∈ L, ‖x i‖ ^ 2) * ∑ i ∈ L, ‖A r i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (row_bound L _ _) (abs_nonneg _)
    _ = _ := by ring
private lemma weighted_scale {ι ρ : Type*} (L : Finset ι) (R : Finset ρ)
    (w : ρ → ℝ) (A : ρ → ι → ℂ) (x : ι → ℂ) (t : ℝ) :
    (∑ r ∈ R, w r * ‖∑ i ∈ L, ((t : ℂ) * x i) * A r i‖ ^ 2) =
      t ^ 2 * (∑ r ∈ R, w r * ‖∑ i ∈ L, x i * A r i‖ ^ 2) := by
  simp only [mul_assoc, ← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring
private lemma homogeneous_domination {ι : Type*} (E H : (ι → ℂ) → ℝ)
    (hE : ∀ x, 0 ≤ E x)
    (hEs : ∀ x (t : ℝ), E (fun i => (t : ℂ) * x i) = t ^ 2 * E x)
    (hHs : ∀ x (t : ℝ), H (fun i => (t : ℂ) * x i) = t ^ 2 * H x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, H x ≤ C * E x) (x : ι → ℂ) :
    H x ≤ sSup ({0} ∪ {y : ℝ | ∃ z, E z ≤ 1 ∧ y = H z}) * E x := by
  let S : Set ℝ := {0} ∪ {y : ℝ | ∃ z, E z ≤ 1 ∧ y = H z}
  have hS : BddAbove S := by
    refine ⟨C, ?_⟩
    rintro y (hy | ⟨z, hz, rfl⟩)
    · have : y = 0 := hy
      subst y
      exact hC
    · exact (hbound z).trans (mul_le_of_le_one_right hC hz)
  by_cases he : E x = 0
  · simpa [he] using hbound x
  have hepos : 0 < E x := lt_of_le_of_ne (hE x) (Ne.symm he)
  let t : ℝ := (Real.sqrt (E x))⁻¹
  have ht : t ^ 2 * E x = 1 := by
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt (hE x), inv_mul_cancel₀ he]
  have hm : H (fun i => (t : ℂ) * x i) ≤ sSup S := by
    apply le_csSup hS
    exact Or.inr ⟨_, (hEs x t).trans_le (by rw [ht]), rfl⟩
  have hm' := mul_le_mul_of_nonneg_right hm (hE x)
  rw [hHs] at hm'
  simpa only [mul_assoc, ht, mul_left_comm, mul_one] using hm'
private lemma weighted_domination {ι ρ : Type*} (L : Finset ι) (R : Finset ρ)
    (w : ρ → ℝ) (A : ρ → ι → ℂ) (x : ι → ℂ) :
    let E := fun z : ι → ℂ => ∑ i ∈ L, ‖z i‖ ^ 2
    let H := fun z : ι → ℂ => ∑ r ∈ R, w r * ‖∑ i ∈ L, z i * A r i‖ ^ 2
    H x ≤ sSup ({0} ∪ {y : ℝ | ∃ z, E z ≤ 1 ∧ y = H z}) * E x := by
  dsimp only
  refine homogeneous_domination (fun z => ∑ i ∈ L, ‖z i‖ ^ 2)
    (fun z => ∑ r ∈ R, w r * ‖∑ i ∈ L, z i * A r i‖ ^ 2) ?_ ?_ ?_
    (∑ r ∈ R, |w r| * ∑ i ∈ L, ‖A r i‖ ^ 2) ?_ ?_ x
  · intro z; positivity
  · intro z t
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Finset.mul_sum]
  · exact weighted_scale L R w A
  · positivity
  · exact weighted_bound L R w A

private lemma pair_bound {ι : Type*} (L : Finset ι) (x : ι → ℂ) {i j : ι}
    (hi : i ∈ L) (hj : j ∈ L) : ‖x i‖ * ‖x j‖ ≤ ∑ k ∈ L, ‖x k‖ ^ 2 := by
  have hE : 0 ≤ ∑ k ∈ L, ‖x k‖ ^ 2 := by positivity
  have hi' := Finset.single_le_sum (fun k _ => sq_nonneg ‖x k‖) hi
  have hj' := Finset.single_le_sum (fun k _ => sq_nonneg ‖x k‖) hj
  nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
private lemma bilinear_bound {ι : Type*} (L : Finset ι) (P : ι → ι → Prop)
    [DecidableRel P] (A : ι → ι → ℂ) (x : ι → ℂ) :
    ‖∑ i ∈ L, ∑ j ∈ L, if P i j then x i * (starRingEnd ℂ) (x j) * A i j else 0‖ ≤
      (∑ i ∈ L, ∑ j ∈ L, ‖A i j‖) * (∑ k ∈ L, ‖x k‖ ^ 2) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · simp only [norm_mul, starRingEnd_apply, norm_star]
    calc
      _ ≤ (∑ k ∈ L, ‖x k‖ ^ 2) * ‖A i j‖ :=
        mul_le_mul_of_nonneg_right (pair_bound L x hi hj) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · simp only [norm_zero]
    positivity
private lemma bilinear_scale {ι : Type*} (L : Finset ι) (P : ι → ι → Prop)
    [DecidableRel P] (A : ι → ι → ℂ) (x : ι → ℂ) (t : ℝ) :
    ‖∑ i ∈ L, ∑ j ∈ L, if P i j then ((t : ℂ) * x i) *
      (starRingEnd ℂ) ((t : ℂ) * x j) * A i j else 0‖ =
    t ^ 2 * ‖∑ i ∈ L, ∑ j ∈ L, if P i j then x i * (starRingEnd ℂ) (x j) * A i j else 0‖ := by
  have ht : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
    exact Complex.conj_ofReal t
  have hh : (∑ i ∈ L, ∑ j ∈ L, if P i j then ((t : ℂ) * x i) *
      (starRingEnd ℂ) ((t : ℂ) * x j) * A i j else 0) =
      (t : ℂ) ^ 2 * (∑ i ∈ L, ∑ j ∈ L, if P i j then x i * (starRingEnd ℂ) (x j) * A i j else 0) := by
    simp only [map_mul, ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [hh, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma indexed_domination {ι γ : Type*} (E : (ι → ℂ) → ℝ) (H : γ → (ι → ℂ) → ℝ)
    (hE : ∀ x, 0 ≤ E x)
    (hEs : ∀ x (t : ℝ), E (fun i => (t : ℂ) * x i) = t ^ 2 * E x)
    (hHs : ∀ g x (t : ℝ), H g (fun i => (t : ℂ) * x i) = t ^ 2 * H g x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ g x, H g x ≤ C * E x) (g : γ) (x : ι → ℂ) :
    H g x ≤ sSup ({0} ∪ {y : ℝ | ∃ (g : γ) (z : ι → ℂ), E z ≤ 1 ∧ y = H g z}) * E x := by
  let S : Set ℝ := {0} ∪ {y : ℝ | ∃ (g : γ) (z : ι → ℂ), E z ≤ 1 ∧ y = H g z}
  have hS : BddAbove S := by
    refine ⟨C, ?_⟩
    rintro y (hy | ⟨j, z, hz, rfl⟩)
    · have : y = 0 := hy
      subst y
      exact hC
    · exact (hbound j z).trans (mul_le_of_le_one_right hC hz)
  by_cases he : E x = 0
  · simpa [he] using hbound g x
  have hepos : 0 < E x := lt_of_le_of_ne (hE x) (Ne.symm he)
  let t : ℝ := (Real.sqrt (E x))⁻¹
  have ht : t ^ 2 * E x = 1 := by
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt (hE x), inv_mul_cancel₀ he]
  have hm : H g (fun i => (t : ℂ) * x i) ≤ sSup S := by
    apply le_csSup hS
    exact Or.inr ⟨g, _, (hEs x t).trans_le (by rw [ht]), rfl⟩
  have hm' := mul_le_mul_of_nonneg_right hm (hE x)
  rw [hHs] at hm'
  simpa only [mul_assoc, ht, mul_left_comm, mul_one] using hm'

variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)

theorem B1_nonneg (M N : ℝ) :
    0 ≤ B1 F c Q M N := by
  exact Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

theorem B2_nonneg (W : ℝ → ℝ) (M N K : ℝ) :
    0 ≤ B2 F c Q W M N K := by
  exact Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

theorem B3_nonneg (W : ℝ → ℝ) (M N K : ℝ) (d : Ideal (𝓞 F)) :
    0 ≤ B3 F c Q W M N K d := by
  exact Real.sSup_nonneg' ⟨0, Or.inl rfl, le_rfl⟩

theorem Q1_le_B1_mul_energy (M N : ℝ) (lam : Ideal (𝓞 F) → ℂ) :
    Q1 F c Q M N lam ≤ B1 F c Q M N * energy F c N lam := by
  simpa only [Q1, B1, energy, rowSum, one_mul] using
    weighted_domination (paperShell F c N) (paperShell F c M) (fun _ => 1)
      (fun a b => (Q.χ b) a) lam

theorem Q2_le_B2_mul_energy (W : ℝ → ℝ) (M N K : ℝ)
    (lam : Ideal (𝓞 F) → ℂ) :
    Q2 F c Q W M N K lam ≤ B2 F c Q W M N K * energy F c N lam := by
  exact weighted_domination (paperShell F c N) (kernelRows F c M K)
    (fun a => W ((Ideal.absNorm a : ℝ) / M)) (fun a b => (Q.χ b) a) lam

theorem norm_T3_le_B3_mul_energy (W : ℝ → ℝ) (M N K : ℝ)
    (d : Ideal (𝓞 F)) (g : Q.G) (lam : Ideal (𝓞 F) → ℂ) :
    ‖T3 F c Q W M N K d g lam‖ ≤
      B3 F c Q W M N K d * energy F c N lam := by
  let A := fun b1 b2 : Ideal (𝓞 F) =>
    ∑ a ∈ kernelRows F c M K, (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
      (Q.χ b1) a * (starRingEnd ℂ) ((Q.χ b2) a)
  refine indexed_domination (energy F c N) (fun g lam => ‖T3 F c Q W M N K d g lam‖)
    ?_ ?_ ?_ (∑ b1 ∈ paperShell F c N, ∑ b2 ∈ paperShell F c N, ‖A b1 b2‖) ?_ ?_ g lam
  · intro x; unfold energy; positivity
  · intro x t
    simp only [energy, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Finset.mul_sum]
  · intro j x t
    exact bilinear_scale (paperShell F c N)
      (fun b1 b2 => b1 ⊔ b2 = d ∧ Q.cls b1 = j ∧ Q.cls b2 = j) A x t
  · positivity
  · intro j x
    exact bilinear_bound (paperShell F c N)
      (fun b1 b2 => b1 ⊔ b2 = d ∧ Q.cls b1 = j ∧ Q.cls b2 = j) A x

theorem B1_le_B2 (W : ℝ → ℝ) (hW : SieveWeight W)
    (M N K : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) (hK : 0 < K) (hKM : K < M) :
    B1 F c Q M N ≤ B2 F c Q W M N K := by
  have hM0 : 0 < M := by linarith
  have hsub : paperShell F c M ⊆ kernelRows F c M K := by
    intro a ha
    have hh := (mem_paperShell F c M a).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨mem_boundedNormIdeals.mpr (by linarith [hh.2.2.2]), ?_, hh.2.1, ?_⟩
    · intro he
      simp [he, Ideal.absNorm_bot] at hh
      linarith [hh.2.2.1]
    · rw [s_eq_absNorm_of_squarefree hh.1]
      linarith [hh.2.2.1]
  have hform : ∀ x, Q1 F c Q M N x ≤ Q2 F c Q W M N K x := by
    intro x
    calc
      _ ≤ ∑ a ∈ paperShell F c M, W ((Ideal.absNorm a : ℝ) / M) *
          ‖rowSum Q N x a‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hh := (mem_paperShell F c M a).mp ha
        have hw : 1 ≤ W ((Ideal.absNorm a : ℝ) / M) := by
          apply hW.one_le
          exact ⟨(le_div_iff₀ hM0).mpr (by linarith [hh.2.2.1]),
            (div_le_iff₀ hM0).mpr hh.2.2.2⟩
        exact le_mul_of_one_le_left (sq_nonneg _) hw
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a ha _ => mul_nonneg (hW.nonneg _) (sq_nonneg _))
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · rintro z (hz | ⟨x, hx, rfl⟩)
    · have : z = 0 := hz
      subst z
      exact B2_nonneg Q W M N K
    · exact (hform x).trans ((Q2_le_B2_mul_energy Q W M N K x).trans
        (mul_le_of_le_one_right (B2_nonneg Q W M N K) hx))

theorem B2_trivial_bound (F : Type) [Field F] [NumberField F]
    (W : ℝ → ℝ) (hW : SieveWeight W) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
        (M N K : ℝ), 1 ≤ M → 1 ≤ N → 0 < K →
          B2 F c Q W M N K ≤ C * M * N := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hW.smooth.continuous.continuousOn
    (K := Set.Icc (1 / 2 : ℝ) (5 / 2))
  let U := max 0 B
  have hU : 0 ≤ U := le_max_left _ _
  have hWU : ∀ t, W t ≤ U := by
    intro t
    by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) (5 / 2)
    · exact (hB (Set.mem_image_of_mem W ht)).trans (le_max_right _ _)
    · rw [hW.zero_outside t ht]; exact hU
  obtain ⟨A, hA, hcount, hfin⟩ := exists_ideal_count_bound_finset F
  refine ⟨max 1 (5 * U * A ^ 2), le_max_left _ _, ?_⟩
  intro c Q M N K hM hN hK
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hrows : ((kernelRows F c M K).card : ℝ) ≤ A * ((5 / 2) * M) := by
    apply hfin _ (by linarith) _
    intro a ha
    exact mem_boundedNormIdeals.mp (Finset.mem_filter.mp ha).1
  have hcols : ((paperShell F c N).card : ℝ) ≤ A * (2 * N) := by
    apply hfin _ (by linarith) _
    intro a ha
    exact (mem_paperShell F c N a).mp ha |>.2.2.2
  have hrow : ∀ (x : Ideal (𝓞 F) → ℂ) a,
      ‖rowSum Q N x a‖ ^ 2 ≤ (paperShell F c N).card * energy F c N x := by
    intro x a
    have hn : ‖rowSum Q N x a‖ ≤ ∑ b ∈ paperShell F c N, ‖x b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      have hh := (mem_paperShell F c N b).mp hb
      exact quadraticFamily_norm_le_one Q hh.1 hh.2.1 a
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans sq_sum_le_card_mul_sum_sq
  have hform : ∀ x, energy F c N x ≤ 1 → Q2 F c Q W M N K x ≤
      U * (kernelRows F c M K).card * (paperShell F c N).card := by
    intro x hx
    have hE : 0 ≤ energy F c N x := by unfold energy; positivity
    calc
      _ ≤ ∑ a ∈ kernelRows F c M K,
          U * ((paperShell F c N).card * energy F c N x) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul (hWU _) (hrow x a) (sq_nonneg _) hU
      _ ≤ ∑ _a ∈ kernelRows F c M K, U * (paperShell F c N).card := by
        apply Finset.sum_le_sum
        intro a ha
        rw [← mul_assoc]
        exact mul_le_of_le_one_right (by positivity) hx
      _ = _ := by simp; ring
  have hb : B2 F c Q W M N K ≤ U * (kernelRows F c M K).card * (paperShell F c N).card := by
    apply csSup_le
    · exact ⟨0, Or.inl rfl⟩
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · have : z = 0 := hz; subst z; positivity
      · exact hform x hx
  calc
    _ ≤ U * (kernelRows F c M K).card * (paperShell F c N).card := hb
    _ ≤ U * (A * ((5 / 2) * M)) * (A * (2 * N)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrows hU) hcols (by positivity) (by positivity)
    _ = (5 * U * A ^ 2) * M * N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hM0) hN0

end DedekindZetaZeroFree.LargeSieve.Sieve

end
