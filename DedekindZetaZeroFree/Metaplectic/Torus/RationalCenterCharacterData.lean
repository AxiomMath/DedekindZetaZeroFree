module

public import DedekindZetaZeroFree.Adeles.Characters.PrincipalCubicLagrangian
public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev E := KPGlobalTorusFunctionData.E F ζ hζ
abbrev Z := KPGlobalTorusFunctionData.Z F ζ hζ
abbrev Ideles := KPGlobalTorusFunctionData.Ideles F
abbrev Raw := KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ

def localAbs (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) : ℝ≥0 := by
  cases v with
  | inl w => exact ‖(y : w.Completion)‖₊ ^ 2
  | inr q => exact ‖(y : q.adicCompletion F)‖₊

theorem localAbs_pos (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    0 < localAbs F v y := by
  cases v with
  | inl w => exact pow_pos (by exact_mod_cast norm_pos_iff.mpr (Units.ne_zero y)) 2
  | inr q => exact_mod_cast norm_pos_iff.mpr (Units.ne_zero y)

def positiveComplex : (ℝ≥0)ˣ →* ℂˣ :=
  Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)

def sixthPower : (ℝ≥0)ˣ →* (ℝ≥0)ˣ := Units.map (NNReal.rpowMonoidHom (1 / 6))

def localValue (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F ζ hζ v) : ℂˣ :=
  if h : IsUnit (g.g 0 0) ∧ IsUnit (g.g 1 1) then
    KPGlobalTorusFunctionData.iota F ζ hζ g.epsilon *
      positiveComplex (sixthPower (Units.mk0
        (localAbs F v (h.1.unit * h.2.unit⁻¹)) (ne_of_gt (localAbs_pos F v _))))
  else 1

def rawCenter : Subgroup (Raw F ζ hζ) :=
  ((Z F ζ hζ).map (E F ζ hζ).subtype).comap
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

def rawProduct (x : rawCenter F ζ hζ) : ℂˣ :=
  ∏ᶠ v, localValue F ζ hζ v (x.val v)

def rationalCenterSubgroup : Subgroup (E F ζ hζ) :=
  (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
