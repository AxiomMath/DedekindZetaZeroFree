module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.AxisIdentity
public import DedekindZetaZeroFree.Nonvanishing.Mellin.HolomorphicZeroTransfer

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RecipeZeroFree

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem zetaSCont_analytic :
    AnalyticOnNhd ℂ D.zetaSCont {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := by
  have h1 : IsOpen {s : ℂ | 31 / 32 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hopen : IsOpen {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := h1.inter h2
  have hsub : {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} ⊆ {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨lt_trans (by norm_num) hs1, hs2⟩
  have hL : DifferentiableOn ℂ D.recipe.continuation.L {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    D.recipe.continuation.L_holo
  have hE : Differentiable ℂ (fun s : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) := by
    apply Differentiable.fun_finsetProd
    intro v _
    unfold comparisonRealPower
    fun_prop
  have hfun : D.zetaSCont = fun s : ℂ => D.recipe.continuation.L s *
      ∏ v ∈ D.recipe.A.Sf,
        (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)) := rfl
  have hd : DifferentiableOn ℂ D.zetaSCont {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := by
    rw [hfun]
    exact (hL.mono hsub).mul hE.differentiableOn
  exact hd.analyticOnNhd hopen

theorem recipe_zero_free (s : ℂ) (hs : 31 / 32 < s.re) (hs1 : s ≠ 1) :
    D.zetaSCont s ≠ 0 := by
  have h1 : IsOpen {s : ℂ | 31 / 32 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hU : IsOpen {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := h1.inter h2
  have hT : AnalyticOnNhd ℂ (DedekindZetaZeroFree.Quantitative.MellinTransform.T D)
      {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} :=
    ((DedekindZetaZeroFree.Quantitative.MellinHolomorphic.T_differentiableOn D).mono
      (fun z hz => hz.1)).analyticOnNhd hU
  have hN : AnalyticOnNhd ℂ
      (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2) * DedekindZetaZeroFree.Quantitative.Spectral.H D s)
      {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} :=
    ((DedekindZetaZeroFree.Quantitative.SpectralData.numerator_differentiableOn D).mono
      (fun z hz => hz.1)).analyticOnNhd hU
  have key := DedekindZetaZeroFree.mellin_holomorphic_zero_transfer (31 / 32) (by norm_num)
    D.zetaSCont (DedekindZetaZeroFree.Quantitative.MellinTransform.T D)
    (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2) * DedekindZetaZeroFree.Quantitative.Spectral.H D s)
    (zetaSCont_analytic D) hT hN
    (fun t : ℝ => DedekindZetaZeroFree.Quantitative.MellinAxis.zetaS_mul_T_axis D t)
    (fun s hs => DedekindZetaZeroFree.Quantitative.SpectralData.numerator_ne_zero D s hs.1)
  have hmem : s ∈ {s : ℂ | 31 / 32 < s.re ∧ s ≠ 1} := ⟨hs, hs1⟩
  exact key s hmem

end

end DedekindZetaZeroFree.Quantitative.RecipeZeroFree
