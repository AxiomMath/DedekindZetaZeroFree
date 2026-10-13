module

public import DedekindZetaZeroFree.Moments.Principal.Contour.ZetaStripGrowth

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalSeparatedStripBounds

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem sep_dist (a b : ℝ) (hab : a ≤ b) (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Icc a b, r ≤ |x - 1| := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_refl a, hab⟩
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (f := fun x : ℝ => |x - 1|) (by fun_prop)
  refine ⟨|x0 - 1|, abs_pos.mpr (sub_ne_zero.mpr (hsep x0 hx0)), fun x hx => hmin hx⟩

theorem zeta_on_real_interval (D : FixedData S η) (a b : ℝ) (ha : 0 < a)
    (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := by
  by_cases hab : a ≤ b
  · obtain ⟨r, hr, hd⟩ := sep_dist a b hab hsep
    obtain ⟨C, k, hC, hk, h⟩ :=
      PrincipalZetaStripGrowth.zetaSCont_strip_polynomial_bound D a b r ha hab hr
    refine ⟨C, k, hC, hk, fun s h1 h2 => h s h1 h2 ?_⟩
    calc r ≤ |s.re - 1| := hd _ ⟨h1, h2⟩
      _ ≤ ‖s - 1‖ := by
        have := Complex.abs_re_le_norm (s - 1)
        simpa using this
  · exact ⟨1, 0, one_pos, le_rfl, fun s h1 h2 => absurd (h1.trans h2) hab⟩

theorem Lpsi_principal_on_real_interval (D : FixedData S η) (u : D.Row)
    (hu : u.u = 1) (a b : ℝ) (ha : 0 < a)
    (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖D.Lpsi u s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ := zeta_on_real_interval D a b ha hsep
  refine ⟨C, k, hC, hk, fun s h1 h2 => ?_⟩
  have hs1 : s ≠ 1 := by
    intro h; apply hsep s.re ⟨h1, h2⟩; rw [h]; simp
  rw [PrincipalResidueFormulas.Lpsi_principal_eq D u hu s (lt_of_lt_of_le ha h1) hs1]
  exact h s h1 h2
