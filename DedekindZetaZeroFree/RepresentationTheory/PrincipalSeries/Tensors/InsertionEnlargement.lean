module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Tensors.HarishChandraTailInvariance

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.CurrentInsertionEnlargement
open KPLiteralScalarHCFiniteProduct KPLiteralScalarHCFiniteInsertion
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (T U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hTU : T ⊆ U)

def extendCover : FiniteProductCover F ζ hζ T →* FiniteProductCover F ζ hζ U where
  toFun a q := if h : q.val ∈ T then a ⟨q.val, h⟩ else 1
  map_one' := by funext q; by_cases hq : q.val ∈ T <;> simp [hq]
  map_mul' a b := by funext q; by_cases hq : q.val ∈ T <;> simp [hq]

include hTU in

theorem finiteProductInsertion_extend (a : FiniteProductCover F ζ hζ T) :
    finiteProductInsertion F ζ hζ U (extendCover F ζ hζ T U a) =
      finiteProductInsertion F ζ hζ T a := by
  have he : (finiteProductInsertion F ζ hζ U).comp (extendCover F ζ hζ T U) =
      finiteProductInsertion F ζ hζ T := by
    apply MonoidHom.pi_ext
    intro q b
    have hs : extendCover F ζ hζ T U (Pi.mulSingle q b) =
        Pi.mulSingle (⟨q.val, hTU q.property⟩ : U) b := by
      funext j
      by_cases hj : j.val = q.val
      · have hmem : j.val ∈ T := hj.symm ▸ q.property
        have heT : (⟨j.val, hmem⟩ : T) = q := Subtype.ext hj
        have heU : j = (⟨q.val, hTU q.property⟩ : U) := Subtype.ext hj
        subst j
        simp [extendCover, q.property]
      · have heU : j ≠ (⟨q.val, hTU q.property⟩ : U) := fun h => hj (congrArg Subtype.val h)
        by_cases hmem : j.val ∈ T
        · have heT : (⟨j.val, hmem⟩ : T) ≠ q := fun h => hj (congrArg Subtype.val h)
          simp [extendCover, hmem, Pi.mulSingle_eq_of_ne heT, Pi.mulSingle_eq_of_ne heU]
        · simp [extendCover, hmem, Pi.mulSingle_eq_of_ne heU]
    rw [MonoidHom.comp_apply, hs, finiteProductInsertion_single, finiteProductInsertion_single]
  exact DFunLike.congr_fun he a
end DedekindZetaZeroFree.FourierContinuation.CurrentInsertionEnlargement

end
