module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FiniteSourceGeometry

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPAdelicCoverRestrictedProduct
set_option backward.isDefEq.respectTransparency false
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

 theorem finiteInjection_mem_finitePart (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    finiteInjection R q a ∈ KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 := by
  refine Subgroup.mem_map.mpr ⟨localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a, ?_, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro w
  change localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a (Sum.inl w) = 1
  simp [localToRestricted]

 def ExteriorFixed (f : Functions R) : Prop :=
  ∀ (p : KPFinitePlace F), p ∉ R.A.Sf →
    ∀ (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)),
    a ∈ compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
    ∀ g, f (g * finiteInjection R p a) = f g

end DedekindZetaZeroFree.RootDerivatives

end
