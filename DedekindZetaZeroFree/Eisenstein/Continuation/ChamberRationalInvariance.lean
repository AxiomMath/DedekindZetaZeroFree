module

public import DedekindZetaZeroFree.Theta.Profiles.IdelicDilation
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
namespace DedekindZetaZeroFree.EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 theorem rightRel_mul (a : Matrix.ProjGenLinGroup (Fin 2) F)
    {x y : Matrix.ProjGenLinGroup (Fin 2) F}
    (h : QuotientGroup.rightRel (KPChamberBruhatTwoCells.rationalBorel F) x y) :
    QuotientGroup.rightRel (KPChamberBruhatTwoCells.rationalBorel F) (x * a) (y * a) := by
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h

def rationalCosetRightMul (a : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPChamberBruhatTwoCells.RationalQuotient F ≃ KPChamberBruhatTwoCells.RationalQuotient F where
  toFun := Quotient.map (fun x => x * a) (fun _ _ h => rightRel_mul a h)
  invFun := Quotient.map (fun x => x * a⁻¹) (fun _ _ h => rightRel_mul a⁻¹ h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp only [Quotient.map_mk, mul_inv_cancel_right]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp only [Quotient.map_mk, inv_mul_cancel_right]

theorem literal_summand_right_mul {K : Subgroup (KPLiteralRaw.G F ζ hζ)}
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ)
    (a : Matrix.ProjGenLinGroup (Fin 2) F)
    (q : KPChamberBruhatTwoCells.RationalQuotient F) (g : KPLiteralRaw.G F ζ hζ) :
    f.val s (KPLiteralRaw.rationalLift F ζ hζ
      (Quotient.out (rationalCosetRightMul a q)) * g) =
    f.val s (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) *
      (KPLiteralRaw.rationalLift F ζ hζ a * g)) := by
  have hq : rationalCosetRightMul a q =
      KPChamberBruhatTwoCells.rationalCoset F (Quotient.out q * a) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, KPLiteralExceptionalResidue.val_rationalCoset_out_eq,
    KPLiteralExceptionalResidue.rationalLift_mul, mul_assoc]

theorem literal_rational_invariant {K : Subgroup (KPLiteralRaw.G F ζ hζ)}
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ)
    (a : Matrix.ProjGenLinGroup (Fin 2) F) (g : KPLiteralRaw.G F ζ hζ) :
    KPLiteralRaw.eisenstein F ζ hζ K f s (KPLiteralRaw.rationalLift F ζ hζ a * g) =
      KPLiteralRaw.eisenstein F ζ hζ K f s g := by
  unfold KPLiteralRaw.eisenstein
  simp_rw [← literal_summand_right_mul f s a]
  exact (rationalCosetRightMul a).tsum_eq
    (fun q : KPChamberBruhatTwoCells.RationalQuotient F =>
      f.val s (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) * g))
end DedekindZetaZeroFree.EisensteinSmoothGerms

end
