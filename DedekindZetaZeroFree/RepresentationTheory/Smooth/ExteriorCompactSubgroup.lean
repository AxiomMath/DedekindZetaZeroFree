module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.CompactTranslation
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.TensorFiniteRecovery

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance : T2Space (Group R) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).1
local instance : IsTopologicalGroup (Group R) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1

 def exteriorCompactGenerators : Subgroup (Group R) :=
  Subgroup.closure {a | ∃ (q : KPFinitePlace F), q ∉ R.A.Sf ∧
    ∃ b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q),
      b ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) ∧
      a = finiteInjection R q b}

 def exteriorCompact : Subgroup (Group R) := (exteriorCompactGenerators R).topologicalClosure

 theorem exteriorCompact_le_K : exteriorCompact R ≤
    (KPContFlatSourceRecipe.D F R.A.zeta12 R.A.primitive_zeta12).K := by
  apply Subgroup.topologicalClosure_minimal
  · apply (Subgroup.closure_le _).mpr
    rintro a ⟨q,hq,b,hb,rfl⟩
    exact finiteInjection_compact_mem R q b hb
  · exact (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12).1.isClosed

 theorem exteriorCompact_le_finite : exteriorCompact R ≤
    KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 := by
  apply Subgroup.topologicalClosure_minimal
  · apply (Subgroup.closure_le _).mpr
    rintro a ⟨q,hq,b,hb,rfl⟩
    exact finiteInjection_mem_finitePart R q b
  · rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure]
    exact Subgroup.isClosed_topologicalClosure _

 theorem exteriorCompact_compact : IsCompact (exteriorCompact R : Set (Group R)) :=
  ((PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F R.A.zeta12 R.A.primitive_zeta12).1).of_isClosed_subset
    (Subgroup.isClosed_topologicalClosure _) (exteriorCompact_le_K R)

 theorem finiteInjection_mem_exteriorCompact (q : KPFinitePlace F) (hq : q ∉ R.A.Sf)
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (hb : b ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    finiteInjection R q b ∈ exteriorCompact R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨q,hq,b,hb,rfl⟩)

 theorem exteriorCompact_fixed (u : Functions R) (hc : Continuous u) (hu : ExteriorFixed R u) :
    ∀ a : exteriorCompact R, rightAction F R.A.zeta12 R.A.primitive_zeta12 a.val u = u := by
  let J : Subgroup (Group R) := {
    carrier := {a | ∀ g, u (g*a) = u g}
    one_mem' := by simp
    mul_mem' := by intro a b ha hb g; rw [← mul_assoc,hb,ha]
    inv_mem' := by intro a ha g; have h := ha (g*a⁻¹); simpa using h.symm }
  have hJ : IsClosed (J : Set (Group R)) := by
    change IsClosed {a | ∀ g, u (g*a) = u g}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro g
    exact isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const
  have hle : exteriorCompact R ≤ J := by
    apply Subgroup.topologicalClosure_minimal _ _ hJ
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨q,hq,b,hb,rfl⟩
    exact hu q hq b hb
  intro a
  ext g
  exact hle a.property g

end DedekindZetaZeroFree.RootDerivatives

end
