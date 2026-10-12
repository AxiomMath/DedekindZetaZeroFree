module

public import DedekindZetaZeroFree.Eisenstein.Residues.ScalarSections.FinitePlaceActions
public import DedekindZetaZeroFree.Theta.Whittaker.UnitDiagonalCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages ThetaExpansion KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem localMaxAction_one (v : KPHilbert.Place F) (f : Plus R.A P C v) :
    localMaxAction R P C v 1 f = f := by
  cases v with
  | inr q => exact congrArg (fun a => a f) (map_one (finiteMaxAction R P C q))
  | inl w =>
    apply Subtype.ext
    apply Subtype.ext
    funext m
    simp [localMaxAction, archMaxAction, KPCplxPrincipalSeriesCharts.pi_one,
      KPLiteralScalarArchTensor.compactAction]

theorem coreFlatInsertion_initial_exterior_spherical
    (hC : C.exceptional = R.A.Sf)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) (bad R.A P C))
    (z : ℂ) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr p))
    (hk : k ∈ compact F ζ hζ (Sum.inr p)) (g : KPLiteralRaw.G F ζ hζ) :
    (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion
      (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
      ⟨bad R.A P C,le_rfl⟩ x)).val z
      (g * scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr p) k)) =
    (coreFlatInsertion R P C (RestrictedTensorSimple.stageInclusion
      (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)
      ⟨bad R.A P C,le_rfl⟩ x)).val z g := by
  classical
  let kr := localToRestricted F ζ hζ (Sum.inr p) k
  have kr_other (v : KPHilbert.Place F) (hv : v ≠ Sum.inr p) : kr v = 1 := by
    simp [kr,localToRestricted,RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply,Pi.mulSingle_eq_of_ne hv]
  have kr_same : kr (Sum.inr p) = k := by
    simp [kr,localToRestricted,RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply]
  have hkr : kr ∈ fullProductCompactPreimage R := by
    intro v
    by_cases hv : v = Sum.inr p
    · subst v; rw [kr_same]; exact finite_compact_le_iwasawa_compact_factor R p hk
    · rw [kr_other v hv]; exact (iwasawaCompactFactor R v).one_mem
  let K : fullProductCompactPreimage R := ⟨kr,hkr⟩
  have hpbad : Sum.inr p ∉ bad R.A P C := by
    simpa [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad,hC] using hp
  have hfix : ∀ v, v ∉ bad R.A P C →
      localMaxAction R P C v ⟨K.val v,K.property v⟩ (plusReference R.A P C v) =
        plusReference R.A P C v := by
    intro v hv
    by_cases he : v = Sum.inr p
    · subst v
      apply finiteMax_reference R P C p
      · simpa [hC] using hp
      · exact ExteriorWhittakerValues.exterior_not_bad ⟨p,hp⟩
    · have hh : (⟨K.val v,K.property v⟩ : iwasawaCompactFactor R v) = 1 :=
        Subtype.ext (kr_other v he)
      rw [hh,localMaxAction_one]
  let s : RestrictedTensorSimple.Level (bad R.A P C) := ⟨bad R.A P C,le_rfl⟩
  have hact : stageMaxAction R P C s (fun j => ⟨K.val j.val,K.property j.val⟩) x = x := by
    have hi : ∀ j : s.val, localMaxAction R P C j.val ⟨K.val j.val,K.property j.val⟩ =
        LinearMap.id := by
      intro j; ext f
      have hj : j.val ≠ Sum.inr p := fun he => hpbad (he ▸ j.property)
      have hh : (⟨K.val j.val,K.property j.val⟩ : iwasawaCompactFactor R j.val) = 1 :=
        Subtype.ext (kr_other j.val hj)
      rw [hh,localMaxAction_one]; rfl
    simp only [stageMaxAction,hi,PiTensorProduct.map_id,LinearMap.id_apply]
  have hf := congrFun (stageScalarInsertion_maxAction R P C s K hfix x) g
  rw [hact] at hf
  have hm : scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr p) k) ∈ fullProductCompact R :=
    Subgroup.mem_map.mpr ⟨kr,hkr,rfl⟩
  change Complex.exp _ * quotientCoreEvaluator R.A P C _ _ =
    Complex.exp _ * quotientCoreEvaluator R.A P C _ _
  rw [height_compact R g ⟨_,hm⟩]
  exact congrArg (fun a : ℂ => Complex.exp (z * (iwasawaLogHeight R g : ℂ)) * a) hf
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
