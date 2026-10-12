module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.ProjectiveGroupAction

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem projectiveSlot_commute_of_projection_one (w : InfinitePlace F)
    (g : MomentSources.Group R)
    (hg : PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12 g w = 1)
    (a : KPCplxCharacterHaar.ComplexPGL2) : Commute g (projectiveSlot R w a) := by
  obtain ⟨E,hE,hp,_⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F R.A.zeta12 R.A.primitive_zeta12
  have he : E (Function.update (1 : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) w a,1) = projectiveSlot R w a := by
    rw [hE]
    exact mul_one _
  have hw : (E.symm g).1 w = 1 := (congrFun (hp g) w).trans hg
  have hc : Commute (E.symm g) (Function.update (1 : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) w a,1) := by
    change (E.symm g) * (Function.update (1 : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) w a,1) = (Function.update (1 : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) w a,1) * (E.symm g)
    apply Prod.ext
    · funext u
      by_cases hu : u = w
      · subst u
        simp [hw]
      · simp [hu]
    · simp
  have hh := hc.map E.toMonoidHom
  change Commute (E (E.symm g)) (E (Function.update (1 : InfinitePlace F → KPCplxCharacterHaar.ComplexPGL2) w a,1)) at hh
  rw [E.apply_symm_apply,he] at hh
  exact hh

theorem raw_arch_projection_one
    (a : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (w : InfinitePlace F) (ha : a (Sum.inl w) = 1) :
    PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 a)) w = 1 := by
  rw [PGLComplex.AdelicSlicesRaw.archProjection_restricted_eval,ha]
  simp

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
