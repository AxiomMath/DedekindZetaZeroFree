module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem norm_realLogPower (r : ℝ) (hr : 0 < r) (u : ℂ) :
    ‖KPGlobalExceptionalParameter.realLogPower r u‖ = r ^ u.re := by
  rw [KPGlobalExceptionalParameter.realLogPower, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_def_of_pos hr]
  ring_nf

theorem lambdaR_norm_eq (r : KPGlobalCenterRationalCharacter.R F ζ hζ) :
    ‖((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂˣ) : ℂ)‖ =
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) ^ ((1 : ℝ) / 6) := by
  rw [KPGlobalCenterRationalCharacter.lambdaR_norm,
    KPGlobalCenterRationalCharacter.nu_formula]
  simp only [KPGlobalTorusFunctionData.delta, MonoidHom.comp_apply]

private theorem delta_pos (r : KPGlobalCenterRationalCharacter.R F ζ hζ) :
    (0 : ℝ) < ((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
    (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ r.val)))

theorem norm_val_covariance (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ)
    (r : KPGlobalCenterRationalCharacter.R F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    ‖f.val s ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g)‖ =
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) ^
        ((2 : ℝ) / 3 + s.re) * ‖f.val s g‖ := by
  rw [(f.property.1 s).2 r x g, norm_mul, norm_mul,
    norm_realLogPower _ (delta_pos F ζ hζ r) _, lambdaR_norm_eq F ζ hζ r]
  rw [← Real.rpow_add (delta_pos F ζ hζ r)]
  have hexp : ((1 / 2 + s).re + 1 / 6 : ℝ) = 2 / 3 + s.re := by
    rw [Complex.add_re]; norm_num; ring
  rw [hexp]

theorem val_N_invariant (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ)
    (x : KPAdeles F) (g : G F ζ hζ) :
    f.val s (KPGlobalTorusFunctionData.N F ζ hζ x * g) = f.val s g := by
  have h := (f.property.1 s).2 (1 : KPGlobalCenterRationalCharacter.R F ζ hζ) x g
  simpa [KPGlobalExceptionalParameter.realLogPower] using h

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
