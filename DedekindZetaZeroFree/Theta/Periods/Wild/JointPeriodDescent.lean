module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.PlaceReindexing
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.CoinvariantDescent

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentJointPeriod
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option quotPrecheck false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)

def fullFiller : ∀ p, actualLocal R D.finiteData p :=
  fun p => if hp : p ∈ s.val then x ⟨p,hp⟩ else D.references p

def placeTuple (y : ∀ q : W, fiber D W q) :
    ∀ p : places W, actualLocal R D.finiteData p :=
  Equiv.piCongrLeft (fun p : places W => actualLocal R D.finiteData p) (placeEquiv W) y

def stageTuple (y : ∀ q : W, fiber D W q) :
    ∀ p : s.val, actualLocal R D.finiteData p :=
  fun p => if hp : p.val ∈ places W then placeTuple D W y ⟨p.val,hp⟩ else x p

def period : AmbientTensor F W (fiber D W) →ₗ[ℂ] ℂ :=
  (D.toTensorHC.literalPeriod 1).comp
    ((RestrictedTensorSimple.stageInclusion _ D.references D.bad s).comp
      ((RestrictedTensorSimple.insert _ (fullFiller D s x)
        (places W) s.val hW).comp (reindex D W).toLinearMap))

theorem period_pure (y : ∀ q : W, fiber D W q) :
    period D W s hW x (PiTensorProduct.tprod ℂ y) =
      coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s
        (stageTuple D W s x y) := by
  have hr := reindex_pure_of D W y (placeTuple D W y)
    (fun q => Equiv.piCongrLeft_apply_apply (fun p : places W => actualLocal R D.finiteData p) (placeEquiv W) y q)
  change D.toTensorHC.literalPeriod 1
    (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (RestrictedTensorSimple.insert _ (fullFiller D s x)
        (places W) s.val hW (reindex D W (PiTensorProduct.tprod ℂ y)))) =
    D.toTensorHC.literalPeriod 1 (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (stageTuple D W s x y)))
  rw [hr,RestrictedTensorSimple.insert_pure]
  apply congrArg (D.toTensorHC.literalPeriod 1)
  apply congrArg (RestrictedTensorSimple.stageInclusion _ D.references D.bad s)
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext p
  by_cases hp : p.val ∈ places W
  · simp [stageTuple,hp]
  · simp [stageTuple,hp,fullFiller,p.property]

theorem stageTuple_at (y : ∀ q : W, fiber D W q) (q : W) :
    stageTuple D W s x y ⟨Sum.inr q.val,hW (placeEquiv W q).property⟩ = y q := by
  have hm : Sum.inr q.val ∈ places W := (placeEquiv W q).property
  dsimp only [stageTuple]
  split_ifs with hp
  · exact Equiv.piCongrLeft_apply_apply
      (fun p : places W => actualLocal R D.finiteData p) (placeEquiv W) y q
  · exact (hp hm).elim

theorem stageTuple_update (y : ∀ q : W, fiber D W q)
    (q : W) (v : fiber D W q) :
    stageTuple D W s x (Function.update y q v) =
      Function.update (stageTuple D W s x y)
        ⟨Sum.inr q.val,hW (placeEquiv W q).property⟩ v := by
  funext p
  by_cases hp : p = ⟨Sum.inr q.val,hW (placeEquiv W q).property⟩
  · subst p
    exact (stageTuple_at D W s hW x (Function.update y q v) q).trans
      (by simp only [Function.update_self])
  · rw [Function.update_of_ne hp]
    by_cases hin : p.val ∈ places W
    · obtain ⟨r,hr⟩ := (placeEquiv W).surjective ⟨p.val,hin⟩
      have hpr : p = ⟨Sum.inr r.val,hW (placeEquiv W r).property⟩ :=
        Subtype.ext (congrArg Subtype.val hr).symm
      subst p
      have hne : r ≠ q := by
        intro he
        subst r
        exact hp rfl
      calc
        _ = Function.update y q v r := stageTuple_at D W s hW x _ r
        _ = y r := Function.update_of_ne hne _ _
        _ = _ := (stageTuple_at D W s hW x y r).symm
    · simp only [stageTuple,dite_eq_right hin]

theorem period_root (y : ∀ q : W, fiber D W q) (q : W)
    (t : Multiplicative (KPKirillovGenuineSectionCharts.K F q.val))
    (v : fiber D W q) :
    period D W s hW x (PiTensorProduct.tprod ℂ
      (Function.update y q ((action D W q)
        (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val t) v))) =
      (character W q t : ℂ) * period D W s hW x
        (PiTensorProduct.tprod ℂ (Function.update y q v)) := by
  have ha := period_pure D W s hW x (Function.update y q
    ((action D W q)
      (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val t) v))
  have hb := period_pure D W s hW x (Function.update y q v)
  have hua := stageTuple_update D W s hW x y q
    ((action D W q)
      (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val t) v)
  have hub := stageTuple_update D W s hW x y q v
  have hh := D.finite_slice_root s (stageTuple D W s x y) q.val
    (hW (placeEquiv W q).property) t.toAdd v

  calc
    _ = coreStageMultilinear _ D.references D.bad (D.toTensorHC.literalPeriod 1) s
      (Function.update (stageTuple D W s x y)
        ⟨Sum.inr q.val,hW (placeEquiv W q).property⟩
        ((action D W q)
          (KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val t) v)) :=
      ha.trans (congrArg (coreStageMultilinear _ D.references D.bad
        (D.toTensorHC.literalPeriod 1) s) hua)
    _ = (character W q t : ℂ) * coreStageMultilinear _ D.references D.bad
        (D.toTensorHC.literalPeriod 1) s
        (Function.update (stageTuple D W s x y)
          ⟨Sum.inr q.val,hW (placeEquiv W q).property⟩ v) := by
      simpa [action,WildActualMirabolic.rho,KPLocalSmoothRepresentation.upperRoot,
        character,KPKirillovOrbitMapFaithful.ψ,KPKirillovProjectorGerms.frequencyCharacter,
        one_mul,smul_eq_mul] using hh
    _ = _ := congrArg (fun z : ℂ => (character W q t : ℂ) * z)
      (hb.trans (congrArg (coreStageMultilinear _ D.references D.bad
        (D.toTensorHC.literalPeriod 1) s) hub)).symm

set_option backward.isDefEq.respectTransparency false in
theorem exists_joint_descent :
    ∃ l : JacquetTensor F R.A.zeta12 R.A.primitive_zeta12 W (character W)
        (fiber D W) (action D W) →ₗ[ℂ] ℂ,
      l.comp (tensorQuotient F R.A.zeta12 R.A.primitive_zeta12 W (character W)
        (fiber D W) (action D W)) = period D W s hW x := by
  exact WildJointCoinvariantDescent.exists_descent
    (I := W)
    (G := fun q => KPKirillovGenuineSectionCharts.G F R.A.zeta12 R.A.primitive_zeta12 q.val)
    (H := fun q => Multiplicative (KPKirillovGenuineSectionCharts.K F q.val))
    (V := fiber D W) (action D W)
    (fun q => KPLocalSmoothRepresentation.upperRoot F R.A.zeta12 R.A.primitive_zeta12 q.val)
    (character W) (period D W s hW x) (by
      intro y q t v
      have hu (b : fiber D W q) :
          @Function.update W (fiber D W) (inferInstance : DecidableEq W) y q b =
          @Function.update W (fiber D W) (Classical.decEq W) y q b :=
        congrArg (fun d : DecidableEq W => @Function.update W (fiber D W) d y q b)
          (Subsingleton.elim _ _)
      simpa only [hu] using period_root D W s hW x y q t v)

end DedekindZetaZeroFree.FourierContinuation.WildCurrentJointPeriod

end
