module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.Holomorphy
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.MellinConverseAxisInversion

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.MellinAxis

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem T_eq_G_axis (t : ℝ) :
    MellinTransform.T D (2 + (t : ℂ) * Complex.I) = Spectral.G D (2 + (t : ℂ) * Complex.I) := by
  have hg_cont : ContinuousOn (MellinTransform.g D) (Set.Ioi (0 : ℝ)) := by
    refine (TransformFlat.g_continuousOn D).congr ?_
    intro Z hZ
    have hZ' : (0 : ℝ) < Z := hZ
    have h1 : ((Z ^ (61 / 100 : ℝ) : ℝ) : ℂ) = (Z : ℂ) ^ (61 / 100 : ℂ) := by
      rw [Complex.ofReal_cpow hZ'.le]
      congr 1
      norm_num
    simp only [MellinTransform.g, TransformFlat.g, if_pos hZ']
    rw [h1]
  have hg_mellin : MellinConvergent (MellinTransform.g D) (-((2 : ℝ) : ℂ)) := by
    simpa using MellinHolomorphic.T_mellinConvergent D 2 (by norm_num)
  have hG_cont : Continuous (fun t : ℝ => Spectral.G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    apply (SpectralData.G_differentiableOn D).continuousOn.comp_continuous
    · fun_prop
    · intro t; simp
  have hG_int : Integrable (fun t : ℝ => Spectral.G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using
      SpectralData.f_integrable D 1 one_pos
  have hg_inv : ∀ x : ℝ, 0 < x → MellinTransform.g D x =
      mellinInv (-2) (fun z : ℂ => Spectral.G D (-z)) x := by
    intro x hx
    have hx' : MellinTransform.g D x = (x : ℂ) ^ (61 / 100 : ℂ) * Spectral.f D x := by
      simp [MellinTransform.g, hx]
    rw [hx', SpectralData.rpow_mul_f D x hx]
    have hint : (∫ t : ℝ, (x : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Spectral.G D (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        ∫ y : ℝ, (x : ℂ) ^ (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          Spectral.G D (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
      rw [← integral_neg_eq_self (fun y : ℝ => (x : ℂ) ^ (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          Spectral.G D (-(((-2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)))]
      congr 1
      funext t
      push_cast
      ring_nf
    unfold mellinInv comparisonVerticalIntegral
    beta_reduce
    rw [hint]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  have h := mellin_converse_axis_inversion 2 (MellinTransform.g D) (Spectral.G D) (by norm_num)
    hg_cont hg_mellin hG_int hG_cont hg_inv
  simpa [MellinTransform.T] using h t

theorem zetaS_mul_T_axis (t : ℝ) :
    D.zetaSCont (2 + (t : ℂ) * Complex.I) * MellinTransform.T D (2 + (t : ℂ) * Complex.I) =
      Complex.exp ((2 + (t : ℂ) * Complex.I - 5 / 6) ^ 2) *
        Spectral.H D (2 + (t : ℂ) * Complex.I) := by
  have hre : 1 < (2 + (t : ℂ) * Complex.I).re := by simp
  have hL : D.zetaSCont (2 + (t : ℂ) * Complex.I) ≠ 0 :=
    (PrincipalMellin.actual_principal_spectral_properties S η D.recipe).2.2.2.2 _ hre
  rw [T_eq_G_axis D t]
  unfold Spectral.G
  field_simp

end

end DedekindZetaZeroFree.Quantitative.MellinAxis
