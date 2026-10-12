module

public import DedekindZetaZeroFree.Theta.Periods.Wild.InjectiveTensorInsertion
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.CharacterTensorFibers

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentReindex
open MomentSources KPKirillovFiniteTensor KPKirillovGenuineSectionCharts WildCurrentTensor
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option quotPrecheck false
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

def places (W : Finset (KPFinitePlace F)) : Finset (KPHilbert.Place F) := W.image Sum.inr

def placeEquiv (W : Finset (KPFinitePlace F)) : W ≃ places W where
  toFun q := ⟨Sum.inr q.val,Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩⟩
  invFun p := ⟨Classical.choose (Finset.mem_image.mp p.property),
    (Classical.choose_spec (Finset.mem_image.mp p.property)).1⟩
  left_inv q := by
    apply Subtype.ext
    exact Sum.inr_injective (Classical.choose_spec
      (Finset.mem_image.mp (show Sum.inr q.val ∈ places W from
        Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩))).2
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp p.property)).2

def reindex (D : TensorActions R N) (W : Finset (KPFinitePlace F)) :
    AmbientTensor F W (fiber D W) ≃ₗ[ℂ]
      RestrictedTensorSimple.Stage (actualLocal R D.finiteData) (places W) :=
  (PiTensorProduct.reindex ℂ (fun p : places W => actualLocal R D.finiteData p)
    (placeEquiv W).symm).symm

theorem reindex_inverse_pure (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (z : ∀ p : places W, actualLocal R D.finiteData p) :
    (reindex D W).symm (PiTensorProduct.tprod ℂ z) =
      PiTensorProduct.tprod ℂ (fun q : W => z (placeEquiv W q)) := by
  exact PiTensorProduct.reindex_tprod ((placeEquiv W).symm) z

theorem reindex_pure_of (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (y : ∀ v : W, fiber D W v)
    (z : ∀ p : places W, actualLocal R D.finiteData p)
    (hz : ∀ q : W, z (placeEquiv W q) = y q) :
    reindex D W (PiTensorProduct.tprod ℂ y) = PiTensorProduct.tprod ℂ z := by
  apply (reindex D W).symm.injective
  rw [LinearEquiv.symm_apply_apply,reindex_inverse_pure]
  congr 1
  funext q
  exact (hz q).symm
end DedekindZetaZeroFree.FourierContinuation.WildCurrentReindex

end
