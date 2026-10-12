module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def cosetRight (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPChamberBruhatTwoCells.RationalQuotient F ≃
      KPChamberBruhatTwoCells.RationalQuotient F :=
  Quotient.congr (Equiv.mulRight γ) (by
    intro a b
    simp only [QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F ↔
      (b * γ) * (a * γ)⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left])

theorem eisenstein_rational (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ) :
    eisenstein F ζ hζ K f s (rationalLift F ζ hζ γ * g) =
      eisenstein F ζ hζ K f s g := by
  let e := cosetRight F γ
  unfold eisenstein
  rw [← e.tsum_eq (fun c => f.val s (rationalLift F ζ hζ (Quotient.out c) * g))]
  apply tsum_congr
  intro c
  have he : e c = KPChamberBruhatTwoCells.rationalCoset F (Quotient.out c * γ) := by
    change (cosetRight F γ) c = _
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [he, val_rationalCoset_out_eq, rationalLift_mul, mul_assoc]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy

end
