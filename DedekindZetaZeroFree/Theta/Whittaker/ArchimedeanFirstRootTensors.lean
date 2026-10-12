module

public import DedekindZetaZeroFree.Eisenstein.Residues.LieActionComparison

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources ThetaExpansion FourierContinuation.HCGeneration CurrentFirstRoot
open KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local notation "W" => actualLocal R D.finiteData

def nativeArchSlot (s : RestrictedTensorSimple.Level D.bad) (w : InfinitePlace F) : s.val :=
  ⟨Sum.inl w,s.property ((D.bad_exact _).mpr (Or.inl ⟨w,rfl⟩))⟩

theorem native_upper_pure (hNative : SourceNativeLie R D)
    (s : RestrictedTensorSimple.Level D.bad) (w : InfinitePlace F)
    (x : ∀ j : s.val, W j.val) (b : Bool) :
    tensorFunction R D s (Function.update x (nativeArchSlot R D s w)
      (complexGenerator (.inr (upperBasis b)) (x (nativeArchSlot R D s w)))) =
    upperLieDerivative R w b (tensorFunction R D s x) := by
  have hh := hNative s w (nativeArchSlot R D s w).property (upperBasis b)
    (PiTensorProduct.tprod ℂ x)
  rw [tensorSlot_tprod] at hh
  have hi : (actualLieIndexEquiv (F := F)).symm (w,upperBasis b) = upperIndex w b := by
    rw [← upper_index w b, Equiv.symm_apply_apply]
  rw [hi] at hh
  rw [upperLieDerivative_actualRight]
  exact hh

def nativeRootTuple (s : RestrictedTensorSimple.Level D.bad) (w : InfinitePlace F)
    (i : ℤ) (x : ∀ j : s.val, W j.val) : ∀ j : s.val, W j.val :=
  Function.update x (nativeArchSlot R D s w) (rootLocal i (x (nativeArchSlot R D s w)))

theorem native_firstRoot_pure (hNative : SourceNativeLie R D)
    (s : RestrictedTensorSimple.Level D.bad) (w : InfinitePlace F)
    (i : ℤ) (x : ∀ j : s.val, W j.val) :
    tensorFunction R D s (nativeRootTuple R D s w i x) =
      firstRootLocalDerivative R w i (tensorFunction R D s x) := by
  unfold nativeRootTuple rootLocal
  simp only [LinearMap.smul_apply,LinearMap.add_apply]
  unfold tensorFunction
  rw [(PiTensorProduct.tprod ℂ).map_update_smul,
    (PiTensorProduct.tprod ℂ).map_update_add,
    (PiTensorProduct.tprod ℂ).map_update_smul]
  simp only [map_add,map_smul]
  change _ = firstRootLocalDerivative R w i (tensorFunction R D s x)
  have h0 := native_upper_pure R D hNative s w x false
  have h1 := native_upper_pure R D hNative s w x true
  unfold tensorFunction at h0 h1
  rw [h0,h1]
  rfl

def nativeRootTupleList (s : RestrictedTensorSimple.Level D.bad) (B : FirstRootCutoffs R)
    (l : List (InfinitePlace F)) (x : ∀ j : s.val, W j.val) : ∀ j : s.val, W j.val :=
  l.foldr (fun w y => nativeRootTuple R D s w (B.exponent w) y) x

theorem native_firstRoots_list (hNative : SourceNativeLie R D)
    (s : RestrictedTensorSimple.Level D.bad) (B : FirstRootCutoffs R)
    (l : List (InfinitePlace F)) (x : ∀ j : s.val, W j.val) :
    tensorFunction R D s (nativeRootTupleList R D s B l x) =
    l.foldr (fun w f => firstRootLocalDerivative R w (B.exponent w) f)
      (tensorFunction R D s x) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change tensorFunction R D s
      (nativeRootTuple R D s w (B.exponent w) (nativeRootTupleList R D s B l x)) = _
    rw [native_firstRoot_pure R D hNative, ih]
    rfl

theorem native_firstRoots_pure (hNative : SourceNativeLie R D)
    (s : RestrictedTensorSimple.Level D.bad) (B : FirstRootCutoffs R)
    (x : ∀ j : s.val, W j.val) :
    tensorFunction R D s (nativeRootTupleList R D s B
      (Finset.univ : Finset (InfinitePlace F)).toList x) =
    firstRootDerivatives R B (tensorFunction R D s x) :=
  native_firstRoots_list R D hNative s B _ x
end DedekindZetaZeroFree.RootDerivatives

end
