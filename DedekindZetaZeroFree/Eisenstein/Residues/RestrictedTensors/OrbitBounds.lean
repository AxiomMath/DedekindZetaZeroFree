module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactTranslationBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

open _root_.DedekindZetaZeroFree.TorusChartTransport renaming compact_lift_of_open_surjective → TorusChartTransport.compact_lift_of_open_surjective

include N in
theorem restrictedSlot_actual_orbit_bound

    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (g : MomentSources.Group R) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore,
      ∀q : KPAdditiveQuotient F,
      ‖LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)
        (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)‖ ≤
        B*(orders.sup coreSeminorm) v := by
  letI : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let p : KPAdeles F → KPAdditiveQuotient F := QuotientAddGroup.mk
  obtain ⟨A,hA,hp⟩ := TorusChartTransport.compact_lift_of_open_surjective p
    QuotientAddGroup.continuous_mk QuotientAddGroup.isOpenMap_coe
    QuotientAddGroup.mk_surjective Set.univ isCompact_univ
  let ng : KPAdeles F → MomentSources.Group R := fun a => KPGlobalTorusFunctionData.N F ζ hζ a*g
  have hn : Continuous ng :=
    (KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ).mul continuous_const
  obtain ⟨orders,B,hB,hbound⟩ := restrictedSlot_actual_compact_bound R N P C  s x w hw
    (ng '' A) (hA.image hn)
  refine ⟨orders,B,hB,?_⟩
  intro v q
  let f := LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v)
  have hnorm (q : KPAdditiveQuotient F) :
      ‖f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)‖ ≤
        B*(orders.sup coreSeminorm) v := by
    have hq : q∈p '' A := by rw [hp]; trivial
    obtain ⟨a,ha,rfl⟩ := hq
    obtain ⟨r,he⟩ := QuotientAddGroup.mk_out_eq_add (AdeleRing.principalSubgroup (𝓞 F) F) a
    obtain ⟨t,ht⟩ := r.property
    have hauto := LiteralSource.coreResidue_raw_automorphic R P C (restrictedSlotTensor R.A P C s x w hw v)
    change ‖f (KPGlobalTorusFunctionData.N F ζ hζ
      (Quotient.out (QuotientAddGroup.mk a : KPAdditiveQuotient F))*g)‖ ≤ _
    rw [he,←ht,add_comm,KPGlobalTorusFunctionData.N_add,mul_assoc,
      ←KPLiteralExceptionalResidue.rationalLift_unipotent]
    change ‖LiteralSource.coreResidue R P C _ (_ * _)‖ ≤ _
    rw [hauto.2.1]
    exact hbound v (ng a) ⟨a,ha,rfl⟩
  exact hnorm q
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
