module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges
public import DedekindZetaZeroFree.Arithmetic.Ideals.ExceptionalSquarefreeDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {c q : Ideal (𝓞 F)}

private lemma absNorm_mul_cast (a b : Ideal (𝓞 F)) :
    (Ideal.absNorm (a * b) : ℝ) = (Ideal.absNorm a : ℝ) * (Ideal.absNorm b : ℝ) := by
  rw [map_mul, Nat.cast_mul]

private lemma lt_mul_of_div_lt {A B X : ℝ} (hA : 0 < A) (h : X / A < B) : X < A * B :=
  (div_lt_iff₀' hA).mp h

private lemma mul_le_two_mul_of_le_div {A B X : ℝ} (hA : 0 < A)
    (h : B ≤ 2 * (X / A)) : A * B ≤ 2 * X := by
  have h' : B * A ≤ (2 * (X / A)) * A := mul_le_mul_of_nonneg_right h hA.le
  have h2 : (2 * (X / A)) * A = 2 * X := by
    rw [mul_assoc, div_mul_cancel₀ X hA.ne']
  linarith [mul_comm B A]

private lemma div_lt_of_lt_mul {A B X : ℝ} (hA : 0 < A) (h : X < A * B) : X / A < B :=
  (div_lt_iff₀' hA).mpr h

private lemma le_div_of_mul_le {A B X : ℝ} (hA : 0 < A) (h : A * B ≤ 2 * X) :
    B ≤ 2 * (X / A) := by
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hA).mpr (by linarith [mul_comm A B])

theorem exceptionalShell_norm_pos (hq : q ≠ ⊥)
    {t : Ideal (𝓞 F)} (ht : t ∈ exceptionalDivisors F c q) :
    0 < (Ideal.absNorm t : ℝ) := by
  exact lt_of_lt_of_le zero_lt_one (exceptionalDivisors_properties hq ht).2.2.2.2

theorem mem_shellMul (hq : q ≠ ⊥) (hcq : c ∣ q) (X : ℝ) (hX : 0 < X)
    {t u : Ideal (𝓞 F)} (ht : t ∈ exceptionalDivisors F c q)
    (hu : u ∈ paperShell F q (X / (Ideal.absNorm t : ℝ))) :
    t * u ∈ paperShell F c X := by
  obtain ⟨hsf, hsupq, hlt, hle⟩ := (mem_paperShell F q (X / (Ideal.absNorm t : ℝ)) u).mp hu
  have hNt : 0 < (Ideal.absNorm t : ℝ) := exceptionalShell_norm_pos hq ht
  obtain ⟨hsfb, hsupb⟩ := exceptional_decomposition_converse hq hcq ht hsf hsupq
  rw [mem_paperShell F c X (t * u)]
  refine ⟨hsfb, hsupb, ?_, ?_⟩
  · rw [absNorm_mul_cast]
    exact lt_mul_of_div_lt hNt hlt
  · rw [absNorm_mul_cast]
    exact mul_le_two_mul_of_le_div hNt hle

private theorem shellMul_mem_sigma (hq : q ≠ ⊥) (hcq : c ∣ q) (X : ℝ) (hX : 0 < X)
    {x : Σ _ : Ideal (𝓞 F), Ideal (𝓞 F)}
    (hx : x ∈ (exceptionalDivisors F c q).sigma
      (fun t => paperShell F q (X / (Ideal.absNorm t : ℝ)))) :
    x.1 * x.2 ∈ paperShell F c X := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
  exact mem_shellMul hq hcq X hX hx1 hx2

private theorem shellMul_inj_sigma (hq : q ≠ ⊥) (hcq : c ∣ q) (X : ℝ) (hX : 0 < X)
    {x₁ x₂ : Σ _ : Ideal (𝓞 F), Ideal (𝓞 F)}
    (hx₁ : x₁ ∈ (exceptionalDivisors F c q).sigma
      (fun t => paperShell F q (X / (Ideal.absNorm t : ℝ))))
    (hx₂ : x₂ ∈ (exceptionalDivisors F c q).sigma
      (fun t => paperShell F q (X / (Ideal.absNorm t : ℝ))))
    (heq : x₁.1 * x₁.2 = x₂.1 * x₂.2) : x₁ = x₂ := by
  rcases x₁ with ⟨a₁, b₁⟩
  rcases x₂ with ⟨a₂, b₂⟩
  obtain ⟨hx11, hx12⟩ := Finset.mem_sigma.mp hx₁
  obtain ⟨hx21, hx22⟩ := Finset.mem_sigma.mp hx₂
  have hmem : a₁ * b₁ ∈ paperShell F c X := mem_shellMul hq hcq X hX hx11 hx12
  obtain ⟨hsf, hsupc, -, -⟩ := (mem_paperShell F c X (a₁ * b₁)).mp hmem
  obtain ⟨w, hw, huniq⟩ := existsUnique_exceptional_decomposition hq hcq hsf hsupc
  have hP₁ : (a₁, b₁) = w :=
    huniq _ ⟨hx11, (mem_paperShell F q _ b₁).mp hx12 |>.1,
      (mem_paperShell F q _ b₁).mp hx12 |>.2.1, rfl⟩
  have hP₂ : (a₂, b₂) = w :=
    huniq _ ⟨hx21, (mem_paperShell F q _ b₂).mp hx22 |>.1,
      (mem_paperShell F q _ b₂).mp hx22 |>.2.1, heq⟩
  have hpair : (a₁, b₁) = (a₂, b₂) := hP₁.trans hP₂.symm
  have h1 : a₁ = a₂ := congrArg Prod.fst hpair
  have h2 : b₁ = b₂ := congrArg Prod.snd hpair
  subst h1
  subst h2
  rfl

private theorem shellMul_surj_sigma (hq : q ≠ ⊥) (hcq : c ∣ q) (X : ℝ) (hX : 0 < X)
    {b : Ideal (𝓞 F)} (hb : b ∈ paperShell F c X) :
    ∃ x ∈ (exceptionalDivisors F c q).sigma
      (fun t => paperShell F q (X / (Ideal.absNorm t : ℝ))), x.1 * x.2 = b := by
  obtain ⟨hsf, hsupc, hlt, hle⟩ := (mem_paperShell F c X b).mp hb
  obtain ⟨w, hw, -⟩ := existsUnique_exceptional_decomposition hq hcq hsf hsupc
  have hNt : 0 < (Ideal.absNorm w.1 : ℝ) := exceptionalShell_norm_pos hq hw.1
  have hnorm : (Ideal.absNorm b : ℝ) =
      (Ideal.absNorm w.1 : ℝ) * (Ideal.absNorm w.2 : ℝ) := by
    rw [hw.2.2.2, absNorm_mul_cast]
  refine ⟨⟨w.1, w.2⟩, Finset.mem_sigma.mpr ⟨hw.1, ?_⟩, hw.2.2.2.symm⟩
  rw [mem_paperShell F q (X / (Ideal.absNorm w.1 : ℝ)) w.2]
  exact ⟨hw.2.1, hw.2.2.1,
    div_lt_of_lt_mul hNt (hnorm ▸ hlt), le_div_of_mul_le hNt (hnorm ▸ hle)⟩

theorem exceptional_shell_sum {Z : Type} [AddCommMonoid Z]
    (hq : q ≠ ⊥) (hcq : c ∣ q) (X : ℝ) (hX : 0 < X)
    (f : Ideal (𝓞 F) → Z) :
    (∑ b ∈ paperShell F c X, f b) =
      ∑ t ∈ exceptionalDivisors F c q,
        ∑ u ∈ paperShell F q (X / (Ideal.absNorm t : ℝ)), f (t * u) := by
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij
    (s := (exceptionalDivisors F c q).sigma
      (fun t => paperShell F q (X / (Ideal.absNorm t : ℝ))))
    (t := paperShell F c X)
    (f := fun x : Σ _ : Ideal (𝓞 F), Ideal (𝓞 F) => f (x.1 * x.2))
    (g := f) (i := fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_).symm
  · exact fun x hx => shellMul_mem_sigma hq hcq X hX hx
  · exact fun x₁ hx₁ x₂ hx₂ heq => shellMul_inj_sigma hq hcq X hX hx₁ hx₂ heq
  · exact fun b hb => by
      obtain ⟨x, hx, hprod⟩ := shellMul_surj_sigma hq hcq X hX hb
      exact ⟨x, hx, hprod⟩
  · exact fun x _ => rfl

theorem exceptional_shell_energy (hq : q ≠ ⊥) (hcq : c ∣ q)
    (X : ℝ) (hX : 0 < X) (lam : Ideal (𝓞 F) → ℂ) :
    (∑ t ∈ exceptionalDivisors F c q,
      ∑ u ∈ paperShell F q (X / (Ideal.absNorm t : ℝ)), ‖lam (t * u)‖ ^ 2) =
      ∑ b ∈ paperShell F c X, ‖lam b‖ ^ 2 := by
  exact (exceptional_shell_sum hq hcq X hX (fun b => ‖lam b‖ ^ 2)).symm

end DedekindZetaZeroFree.LargeSieve.Sieve
