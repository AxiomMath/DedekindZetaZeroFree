module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.CanonicalFlat
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FlatRootWord

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources KPAdelicCoverRestrictedProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def finiteInjection (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) : Group R :=
  scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)

theorem finiteInjection_commute (q p : KPFinitePlace F) (hpq : p ≠ q)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    Commute (finiteInjection R q a) (finiteInjection R p b) := by
  have hc : Commute (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
      (localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) b) := by
    change _ * _ = _ * _
    ext v
    by_cases hv : v = Sum.inr q
    · subst v
      simp [localToRestricted, Sum.inr_injective.ne hpq.symm]
    · by_cases hvp : v = Sum.inr p
      · subst v
        simp [localToRestricted, Sum.inr_injective.ne hpq]
      · simp [localToRestricted, hv, hvp]
  exact (hc.map (amalgamation F R.A.zeta12 R.A.primitive_zeta12)).map
    (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)

theorem finiteInjection_compact_mem (p : KPFinitePlace F)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hb : b ∈ compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    finiteInjection R p b ∈ (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K := by
  apply Subgroup.mem_map.mpr
  refine ⟨localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) b, ?_, rfl⟩
  intro v
  by_cases hv : v = Sum.inr p
  · subst v
    simp only [localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
      RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_same]
    exact PrincipalOfKP.localCompactFactor_le_max F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) hb
  · have he : localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) b v = 1 := by
      simp [localToRestricted, hv]
    rw [he]
    exact (PrincipalOfKP.localCompactFactorMax F R.A.zeta12 R.A.primitive_zeta12 v).one_mem

theorem rootProjectorWord_right_fixed
    (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
    (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)
    (l : List R.A.Sf) (f : Functions R) (b : Group R)
    (hb : ∀ g, f (g * b) = f g)
    (hcomm : ∀ q i, Commute b (finiteRoot R q.val (t q i))) :
    ∀ g, rootProjectorWord R I c t l f (g * b) = rootProjectorWord R I c t l f g := by
  induction l with
  | nil => exact hb
  | cons q l ih =>
    intro g
    simp only [rootProjectorWord, List.foldr_cons, LinearMap.comp_apply,
      rightTranslateSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [mul_assoc, (hcomm q i).eq, ← mul_assoc]
    exact ih _

theorem rootProjectorWord_exterior {Q : AdmissibleFlatSources R}
    (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
    (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)
    (l : List R.A.Sf) (v : R.A.UnitQuotient) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hb : b ∈ compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    ∀ g, rootProjectorWord R I c t l ((Q.flat v).val 0) (g * finiteInjection R p b) =
      rootProjectorWord R I c t l ((Q.flat v).val 0) g := by
  apply rootProjectorWord_right_fixed
  · exact Q.exterior_spherical v 0 p hp b hb
  · intro q i
    unfold finiteRoot
    rw [← ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R]
    exact finiteInjection_commute R q.val p (fun h => hp (h ▸ q.property)) _ b |>.symm

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
