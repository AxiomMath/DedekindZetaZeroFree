module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.FiniteRootInsertionAndProductFamilies

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.KPLiteralScalarHCFiniteDecomposition
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralScalarHCFiniteInsertion
open KPLiteralScalarHCFiniteProduct KPLiteralScalarHCFiniteOutside
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
abbrev RawStage := ∀ q : T, KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q.val)

def stageRawInsertion : RawStage F ζ hζ T →* RestrictedCover F ζ hζ where
  toFun a := ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => if h : q ∈ T then a ⟨q, h⟩ else 1, by
      have he : ∀ᶠ v : KPHilbert.Place F in Filter.cofinite, v ∉ T.image Sum.inr :=
        (T.image Sum.inr).finite_toSet.compl_mem_cofinite
      filter_upwards [he] with v hv
      cases v with
      | inl w => exact Subgroup.one_mem _
      | inr q =>
        have hq : q ∉ T := by intro h; apply hv; exact Finset.mem_image.mpr ⟨q, h, rfl⟩
        simp only [dite_eq_right hq]
        exact Subgroup.one_mem _⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w => rfl
    | inr q => by_cases hq : q ∈ T <;> simp [hq]
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w => simp
    | inr q => by_cases hq : q ∈ T <;> simp [hq]

@[simp] theorem stageRawInsertion_here (a : RawStage F ζ hζ T) (q : T) :
    stageRawInsertion F ζ hζ T a (Sum.inr q.val) = a q := by
  change (if h : q.val ∈ T then a ⟨q.val, h⟩ else 1) = a q
  simp only [dite_eq_left q.property]

@[simp] theorem stageRawInsertion_arch (a : RawStage F ζ hζ T) (w : InfinitePlace F) :
    stageRawInsertion F ζ hζ T a (Sum.inl w) = 1 := rfl

@[simp] theorem stageRawInsertion_outside (a : RawStage F ζ hζ T)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hq : q ∉ T) :
    stageRawInsertion F ζ hζ T a (Sum.inr q) = 1 := by
  change (if h : q ∈ T then a ⟨q, h⟩ else (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) = 1
  rw [dite_eq_right hq]

theorem stageRawInsertion_single (q : T)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q.val)) :
    stageRawInsertion F ζ hζ T (Pi.mulSingle q a) = localToRestricted F ζ hζ (Sum.inr q.val) a := by
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl w => simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply]
  | inr r =>
    by_cases hr : r ∈ T
    · rw [stageRawInsertion_here F ζ hζ T _ ⟨r, hr⟩]
      by_cases he : r = q.val
      · subst r; simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply]
      · have hn : (⟨r, hr⟩ : T) ≠ q := fun h => he (congrArg Subtype.val h)
        simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, he, Pi.mulSingle_eq_of_ne hn]
    · rw [stageRawInsertion_outside F ζ hζ T _ r hr]
      have hn : r ≠ q.val := by intro h; subst r; exact hr q.property
      simp [localToRestricted, RestrictedProduct.coe_mulSingle_apply, hn]

def stageLocalQuotients : RawStage F ζ hζ T →* FiniteProductCover F ζ hζ T where
  toFun a q := KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (a q)
  map_one' := by funext q; exact map_one _
  map_mul' a b := by funext q; exact map_mul _ _ _

theorem stageRawInsertion_quotient (a : RawStage F ζ hζ T) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ (stageRawInsertion F ζ hζ T a)) =
      (finiteProductInsertion F ζ hζ T (stageLocalQuotients F ζ hζ T a)).val := by
  have he : ((scalarQuotient F ζ hζ).comp (amalgamation F ζ hζ)).comp
      (stageRawInsertion F ζ hζ T) =
      (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype.comp
        ((finiteProductInsertion F ζ hζ T).comp (stageLocalQuotients F ζ hζ T)) := by
    apply MonoidHom.pi_ext
    intro q b
    rw [MonoidHom.comp_apply, stageRawInsertion_single]
    change scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q.val) b) =
      (finiteProductInsertion F ζ hζ T (stageLocalQuotients F ζ hζ T (Pi.mulSingle q b))).val
    have hq : stageLocalQuotients F ζ hζ T (Pi.mulSingle q b) = Pi.mulSingle q
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) b) := by
      funext j
      by_cases hj : j = q
      · subst j; simp [stageLocalQuotients]
      · simp [stageLocalQuotients, Pi.mulSingle_eq_of_ne hj]
    rw [hq, finiteProductInsertion_single, finiteInsertion_value, finiteGroupInsertion_raw]
  exact DFunLike.congr_fun he a

def rawOutside (r : RestrictedCover F ζ hζ) : RestrictedCover F ζ hζ :=
  r * (stageRawInsertion F ζ hζ T (fun q => r (Sum.inr q.val)))⁻¹

theorem rawOutside_mem (r : RestrictedCover F ζ hζ)
    (hr : ∀ w : InfinitePlace F, r (Sum.inl w) = 1) :
    rawOutside F ζ hζ T r ∈ rawOutsideStage F ζ hζ T := by
  constructor
  · apply Subgroup.mem_iInf.mpr
    intro w
    change r (Sum.inl w) * (stageRawInsertion F ζ hζ T _ (Sum.inl w))⁻¹ = 1
    rw [hr, stageRawInsertion_arch]; simp
  · apply Subgroup.mem_iInf.mpr
    intro q
    change r (Sum.inr q.val) * (stageRawInsertion F ζ hζ T _ (Sum.inr q.val))⁻¹ = 1
    rw [stageRawInsertion_here]; exact mul_inv_cancel _

end DedekindZetaZeroFree.KPLiteralScalarHCFiniteDecomposition

end
