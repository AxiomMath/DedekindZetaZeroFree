module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorLiftProducts

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma rawToGroup_local_center (w : KPHilbert.Place F) (e : rootsOfUnity 3 F) :
    rawToGroup R (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 w
      (KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 w e)) =
      pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 e := by
  exact congrArg (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
    (localInjection_central F R.A.zeta12 R.A.primitive_zeta12 w e)

lemma fourier_center {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (e : rootsOfUnity 3 F) (g : Group R) :
    fourier R Q.dq (T.theta v) (pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 e * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 e : ℂ) *
        fourier R Q.dq (T.theta v) g := by
  unfold MomentSources.fourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  have hc := Subgroup.mem_center_iff.mp
    (pglCentralInjection_central F R.A.zeta12 R.A.primitive_zeta12 ⟨e, rfl⟩)
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q))
  rw [← mul_assoc, hc, mul_assoc]
  exact (congrArg (fun z : ℂ => z * star (adelicTraceQuotientCharacter F q : ℂ))
    ((T.automorphic v).2.2 e _)).trans (mul_assoc _ _ _)

lemma rawToGroup_central_tuple (e : CentralTuples F) :
    rawToGroup R (centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e) =
      pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 (centralProduct F e) := by
  let w := distinguishedPlace F
  let s : CentralTuples F := RestrictedProduct.mulSingle
    (fun _ => (⊥ : Subgroup (rootsOfUnity 3 F))) w (centralProduct F e)
  have hs : centralProduct F s = centralProduct F e := by
    change (∏ᶠ v, s v) = _
    rw [finprod_eq_single _ w]
    · exact RestrictedProduct.mulSingle_eq_same _ _ _
    · intro v hv
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ hv
  have hker : e / s ∈ (centralProduct F).ker := by
    rw [MonoidHom.mem_ker, map_div, hs]
    exact div_self' _
  have hm : centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e /
      centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 s ∈ KPAdelicCoverRestrictedProduct.M F R.A.zeta12 R.A.primitive_zeta12 := by
    rw [← map_div]
    exact ⟨e / s, hker, rfl⟩
  have he : amalgamation F R.A.zeta12 R.A.primitive_zeta12
      (centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e) =
      amalgamation F R.A.zeta12 R.A.primitive_zeta12
        (centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 s) :=
    QuotientGroup.eq_iff_div_mem.mpr hm
  have ht : centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 s =
      localToRestricted F R.A.zeta12 R.A.primitive_zeta12 w
        (KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 w (centralProduct F e)) := by
    apply RestrictedProduct.ext
    intro v
    by_cases hv : v = w
    · subst v
      simp [centralTupleMap, s, localToRestricted, RestrictedProduct.mulSingleMonoidHom]
    · simp [centralTupleMap, s, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
        RestrictedProduct.mulSingle_eq_of_ne, hv]
  exact (congrArg (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12) he).trans
    ((congrArg (rawToGroup R) ht).trans (rawToGroup_local_center R w _))

end DedekindZetaZeroFree.OrbitExpansion

end
