module

public import DedekindZetaZeroFree.Eisenstein.Induction.UnitaryModelEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open _root_.DedekindZetaZeroFree.KPLocalStoneVonNeumann renaming inducedCosetEquiv → inducedCosetEquiv
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

abbrev InducingCoordinate : KPHilbert.Place F → Type
  | .inl _ => Unit
  | .inr q => actualTorus F R.A.zeta12 R.A.primitive_zeta12 q ⧸
      (C.polarization q).L.comap (C.canonical q).heisenberg.π
instance inducingCoordinateFinite (p : KPHilbert.Place F) : Finite (InducingCoordinate R P C p) := by
  cases p <;> infer_instance
instance inducingCoordinateFintype (p : KPHilbert.Place F) : Fintype (InducingCoordinate R P C p) := Fintype.ofFinite _
instance inducingCoordinateDecidableEq (p : KPHilbert.Place F) : DecidableEq (InducingCoordinate R P C p) := Classical.decEq _

def inducingCoordinates : ∀ p, Fiber R P C p ≃ₗ[ℂ] (InducingCoordinate R P C p → ℂ)
  | .inl _ => (LinearEquiv.piUnique ℂ (fun _ : Unit => ℂ)).symm
  | .inr q => inducedCosetEquiv ((C.polarization q).L.comap (C.canonical q).heisenberg.π)
      (C.polarization q).ωL.toMonoidHom

def localMinusValue : ∀ p, KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p →
    actualLocal R (imageData R N P C) p →ₗ[ℂ] Fiber R P C p
  | .inl w, a =>
    { toFun f := (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 a.epsilon : ℂ) * f.val.val (complexMatrix R w a)
      map_add' _ _ := mul_add _ _ _
      map_smul' _ _ := mul_left_comm _ _ _ }
  | .inr q, a =>
    { toFun f := f.val.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

def localSignedIntegrand : ∀ p, KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p →
    RootPoint R p → Plus R N P C p →ₗ[ℂ] Fiber R P C p
  | .inl w, a, x =>
    { toFun f := (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 a.epsilon : ℂ) * f.val.val
          (KPCplxCharacterHaar.weyl * KPCplxCharacterHaar.upperUnipotent x * complexMatrix R w a)
      map_add' _ _ := mul_add _ _ _
      map_smul' _ _ := mul_left_comm _ _ _ }
  | .inr q, a, x =>
    { toFun f := f.val ((imageData R N P C q).inducing.borel.liftedW⁻¹ *
        (imageData R N P C q).inducing.borel.upperRoot (Multiplicative.ofAdd x) *
        KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (.inr q) a)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

def arithmeticQuotient (p : KPHilbert.Place F) : Plus R N P C p →ₗ[ℂ] actualLocal R (imageData R N P C) p :=
  (arithmeticRootScale R p : ℂ) • sourceQuotient R (imageData R N P C) p

def reflectedStage (s : RestrictedTensorSimple.Level (bad R P C)) (a : Raw R) :
    RestrictedTensorSimple.Stage (actualLocal R (imageData R N P C)) s.val →ₗ[ℂ]
      KPGlobalResidualConstruction.smoothRationalFiber F R.A.zeta12 R.A.primitive_zeta12 :=
  (comparisonSmooth R P C).comp
    ((RestrictedTensorSimple.stageInclusion (Fiber R P C) (reference R P C) (bad R P C) s).comp
      (PiTensorProduct.map (fun j : s.val => localMinusValue R N P C j (a j))))

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
