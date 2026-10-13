module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree
open scoped NumberField

theorem convex_normalized (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 10 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (𝔪 : Ideal (𝓞 F)) (_ : 𝔪 ≠ ⊥) (ω : RayClassCharacter F 𝔪),
          ω.IsPrimitive → ¬ ω.IsPrincipal →
          ∀ D : NonprincipalRayHeckeData F 𝔪 ω, ∀ s : ℂ,
            -d ≤ s.re → s.re ≤ 1 + d →
            ‖nonprincipalHeckeEntireContinuation F 𝔪 ω D s‖ ≤
              C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 + d - s.re) / 2) *
                (2 + |s.im|) ^ A_F := by
  refine ⟨((2 * NumberField.InfinitePlace.nrComplexPlaces F + 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro d hd hd1
  obtain ⟨C, hC, hnpB, -⟩ := heckeEntireRegularizations_uniform_boundaries F hF d hd hd1
  have hB : 0 < idealAbsoluteSum F (1 + d) :=
    (idealAbsoluteSum_converges F (1 + d) (by linarith)).2.2.1
  refine ⟨6 ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1) *
    (C + idealAbsoluteSum F (1 + d)), mul_pos (by positivity) (by linarith), ?_⟩
  intro 𝔪 hm ω hprim hnp D s hs1 hs2
  obtain ⟨hedge, hright⟩ := hnpB 𝔪 hm ω hprim hnp D
  obtain ⟨M, Bg, hM, hBg, hgrowth⟩ :=
    nonprincipalHeckeEntireContinuation_quadratic_strip_growth F hF 𝔪 hm ω D (-d) (1 + d)
      (by linarith)
  set Q : ℝ := 1 + (Ideal.absNorm 𝔪 : ℝ) with hQdef
  have hQ1 : 1 ≤ Q := by
    have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm 𝔪)
    linarith
  have hQpos : 0 < Q := by linarith
  have hQc : ((Q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  set f := nonprincipalHeckeEntireContinuation F 𝔪 ω D with hf
  set w : ℂ → ℂ := fun z => ((Q : ℝ) : ℂ) ^ ((z - (1 + (d : ℂ))) / 2) with hw
  have hwnorm : ∀ z : ℂ, ‖w z‖ = Q ^ ((z.re - (1 + d)) / 2) := by
    intro z
    simp only [hw]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    congr 1
    simp
  have hwd : Differentiable ℂ w := by
    intro z
    apply DifferentiableAt.const_cpow _ (Or.inl hQc)
    fun_prop
  have hfd : Differentiable ℂ f :=
    nonprincipalHeckeEntireContinuation_differentiable F hF 𝔪 hm ω D
  set k : ℕ := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1 with hk
  set B := idealAbsoluteSum F (1 + d) with hBdef
  have hg_diff : Differentiable ℂ (fun z => w z * f z) := hwd.mul hfd
  have hgrowth' : ∃ M' B' : ℝ, 0 ≤ M' ∧ 0 ≤ B' ∧
      ∀ z : ℂ, -d < z.re ∧ z.re < 1 + d →
        ‖(fun z => w z * f z) z‖ ≤ M' * Real.exp (B' * (1 + |z.im|) ^ 2) := by
    refine ⟨M, Bg, hM, hBg, fun z hz => ?_⟩
    dsimp only
    rw [norm_mul, hwnorm]
    have h1 : Q ^ ((z.re - (1 + d)) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith [hz.2])
    have h2 := hgrowth z (by linarith [hz.1]) (by linarith [hz.2])
    calc Q ^ ((z.re - (1 + d)) / 2) * ‖f z‖ ≤ 1 * ‖f z‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ M * Real.exp (Bg * (1 + |z.im|) ^ 2) := by rw [one_mul]; exact h2
  have hbound : ∀ z : ℂ, (z.re = -d ∨ z.re = 1 + d) →
      ‖(fun z => w z * f z) z‖ ≤ (C + B) * (2 + |z.im|) ^ k := by
    intro z hz
    dsimp only
    rw [norm_mul, hwnorm]
    have hX : (1 : ℝ) ≤ 2 + |z.im| := by linarith [abs_nonneg z.im]
    have hXk : 0 ≤ (2 + |z.im|) ^ k := by positivity
    rcases hz with hz | hz
    · have h1 := hedge z (Or.inl hz)
      have hexp : (z.re - (1 + d)) / 2 + ((1:ℝ) / 2 + d) = 0 := by rw [hz]; ring
      have hmul : Q ^ ((z.re - (1 + d)) / 2) * Q ^ ((1:ℝ) / 2 + d) = 1 := by
        rw [← Real.rpow_add hQpos, hexp, Real.rpow_zero]
      calc Q ^ ((z.re - (1 + d)) / 2) * ‖f z‖
          ≤ Q ^ ((z.re - (1 + d)) / 2) * (C * Q ^ ((1:ℝ) / 2 + d) * (2 + |z.im|) ^ k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C * (2 + |z.im|) ^ k * (Q ^ ((z.re - (1 + d)) / 2) * Q ^ ((1:ℝ) / 2 + d)) := by ring
        _ = C * (2 + |z.im|) ^ k := by rw [hmul, mul_one]
        _ ≤ (C + B) * (2 + |z.im|) ^ k :=
            mul_le_mul_of_nonneg_right (by linarith) hXk
    · have hr := hright z (by linarith) (by linarith)
      have h0 : (z.re - (1 + d)) / 2 = 0 := by rw [hz]; ring
      rw [h0, Real.rpow_zero, one_mul]
      have hX1 : (1 : ℝ) ≤ (2 + |z.im|) ^ k := one_le_pow₀ hX
      calc ‖f z‖ ≤ B := hr
        _ = B * 1 := (mul_one _).symm
        _ ≤ B * (2 + |z.im|) ^ k := mul_le_mul_of_nonneg_left hX1 hB.le
        _ ≤ (C + B) * (2 + |z.im|) ^ k :=
            mul_le_mul_of_nonneg_right (by linarith) hXk
  have hPL := norm_le_on_closed_strip_of_polynomial_boundary d hd hd1 k (C + B)
    (by linarith) (fun z => w z * f z) hg_diff.diffContOnCl hgrowth' hbound s ⟨hs1, hs2⟩
  have hfs : ‖f s‖ = Q ^ ((1 + d - s.re) / 2) * ‖(fun z => w z * f z) s‖ := by
    dsimp only
    rw [norm_mul, hwnorm, ← mul_assoc, ← Real.rpow_add hQpos]
    have hz0 : (1 + d - s.re) / 2 + (s.re - (1 + d)) / 2 = 0 := by ring
    rw [hz0, Real.rpow_zero, one_mul]
  have hXA : (2 + |s.im|) ^ ((2 * NumberField.InfinitePlace.nrComplexPlaces F + 1 : ℕ) : ℝ)
      = (2 + |s.im|) ^ k := Real.rpow_natCast _ _
  rw [hXA]
  calc ‖f s‖ = Q ^ ((1 + d - s.re) / 2) * ‖(fun z => w z * f z) s‖ := hfs
    _ ≤ Q ^ ((1 + d - s.re) / 2) * (6 ^ k * (C + B) * (2 + |s.im|) ^ k) :=
        mul_le_mul_of_nonneg_left hPL (by positivity)
    _ = 6 ^ k * (C + B) * Q ^ ((1 + d - s.re) / 2) * (2 + |s.im|) ^ k := by ring

end DedekindZetaZeroFree.Quantitative
