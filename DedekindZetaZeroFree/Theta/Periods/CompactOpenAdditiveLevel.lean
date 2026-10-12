module

public import DedekindZetaZeroFree.Theta.Periods.RationalPeriodContinuity
public import DedekindZetaZeroFree.Adeles.Quotients.UniformSmoothLevelFamilies

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory IsDedekindDomain
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming finitePart_normal → finitePart_normal

theorem thetaFiber_hasSmoothAdditiveLevel_of_root_containment
    {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hK : ∀ k ∈ K,
      g⁻¹ * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (finiteLevelFiniteInclusion F k) * g ∈
          KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 Q.level) :
    HasSmoothAdditiveLevel K (thetaFiber R T v g) := by
  intro q h
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨k, hk, he⟩ := h.property
  change (QuotientAddGroup.mk (finiteLevelFiniteInclusion F k) : KPAdditiveQuotient F) = h.val at he
  rw [← he, ← QuotientAddGroup.mk_add, thetaFiber_mk, thetaFiber_mk,
    KPGlobalTorusFunctionData.N_add]
  have hmul : (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (finiteLevelFiniteInclusion F k)) * g =
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) *
        (g⁻¹ * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F k) * g) := by group
  rw [hmul]
  exact T.common_cleared_level v 0 (Metric.mem_ball_self T.radius_pos) _ _ (hK k hk)

theorem finiteRoot_mem_finitePart (k : FiniteAdeleRing (𝓞 F) F) :
    KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (finiteLevelFiniteInclusion F k) ∈
        KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 := by
  refine ⟨KPGlobalTorusFunctionData.rootTuple F R.A.zeta12 R.A.primitive_zeta12
    (finiteLevelFiniteInclusion F k), ?_, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro w
  change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
    (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)
      (finiteLevelFiniteInclusion F k)) = 1
  change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) 0 = 1
  exact KPStandardLocalRootLifts.N_zero F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)

theorem thetaFiber_exists_compact_open_level
    {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    ∃ K : AddSubgroup (FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      HasSmoothAdditiveLevel K (thetaFiber R T v g) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  letI := finitePart_normal F R.A.zeta12 R.A.primitive_zeta12
  let n : Multiplicative (FiniteAdeleRing (𝓞 F) F) →*
      KPGlobalTorusFunctionData.finitePart F R.A.zeta12 R.A.primitive_zeta12 :=
    { toFun k := ⟨KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (finiteLevelFiniteInclusion F k.toAdd), finiteRoot_mem_finitePart R k.toAdd⟩
      map_one' := by
        apply Subtype.ext
        change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F 0) = 1
        rw [map_zero]
        exact (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
      map_mul' a b := by
        apply Subtype.ext
        change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          (finiteLevelFiniteInclusion F (a.toAdd + b.toAdd)) = _
        rw [map_add]
        exact KPGlobalTorusFunctionData.N_add F R.A.zeta12 R.A.primitive_zeta12 _ _ }
  let c := (MulAut.conjNormal (H := KPGlobalTorusFunctionData.finitePart
    F R.A.zeta12 R.A.primitive_zeta12) g⁻¹).toMonoidHom.comp n
  let K₀ : AddSubgroup (FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {k | c (Multiplicative.ofAdd k) ∈ Q.level.toOpenSubgroup}
      zero_mem' := by exact (Q.level.toOpenSubgroup.toSubgroup.comap c).one_mem
      add_mem' := by
        intro a b ha hb
        exact (Q.level.toOpenSubgroup.toSubgroup.comap c).mul_mem ha hb
      neg_mem' := by
        intro a ha
        exact (Q.level.toOpenSubgroup.toSubgroup.comap c).inv_mem ha }
  let K := K₀ ⊓ KPAdelicTopology.integralAdeles F
  have hn : Continuous n := by
    apply Continuous.subtype_mk
    exact (KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
      F R.A.zeta12 R.A.primitive_zeta12).comp
        (continuous_const.prodMk continuous_id)
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    change Continuous (fun k : Multiplicative (FiniteAdeleRing (𝓞 F) F) =>
      g⁻¹ * (n k).val * (g⁻¹)⁻¹)
    exact (continuous_const.mul (continuous_subtype_val.comp hn)).mul continuous_const
  have hKo : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Q.level.toOpenSubgroup.isOpen.preimage hc).inter
      (KPAdelicTopology.integralAdeles_isOpen F)
  have hKc : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (KPAdelicTopology.integralAdeles_isCompact F).of_isClosed_subset
      (K.isClosed_of_isOpen hKo) (fun _ h => h.2)
  refine ⟨K, hKc, hKo, thetaFiber_hasSmoothAdditiveLevel_of_root_containment R T v g K ?_⟩
  intro k hk
  refine ⟨c (Multiplicative.ofAdd k), hk.1, ?_⟩
  change g⁻¹ * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (finiteLevelFiniteInclusion F k) * (g⁻¹)⁻¹ = _
  rw [inv_inv]

end DedekindZetaZeroFree.OrbitExpansion

end
