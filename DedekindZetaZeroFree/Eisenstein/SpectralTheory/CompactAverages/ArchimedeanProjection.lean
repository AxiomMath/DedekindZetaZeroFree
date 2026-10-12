module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.BalancedArchimedeanFibers

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection
open KPContSectorCoveredQuotientVocabulary KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv → productEquiv
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming productEquiv_apply → productEquiv_apply
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_eq → K_U_eq
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar renaming compactSubgroup_eq_origin_stabilizer → compactSubgroup_eq_origin_stabilizer
open _root_.DedekindZetaZeroFree.KPContSectorArchSphericalFibers renaming mem_KInfinity_iff_stab → mem_KInfinity_iff_stab
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : CompactOpenLevel (FiniteCover F ζ hζ))
local instance : MeasurableSpace (K_U F ζ hζ U) := borel _
local instance : BorelSpace (K_U F ζ hζ U) := ⟨rfl⟩
local instance : CompactSpace (K_U F ζ hζ U) := isCompact_iff_compactSpace.mp (K_U_compact F ζ hζ U)
local instance : CompactSpace KPCplxPrincipalSeriesCharts.compactSubgroup :=
  isCompact_iff_compactSpace.mp KPCplxPrincipalSeriesCharts.compactSubgroup_isCompact

theorem split_mem (k : K_U F ζ hζ U) :
    ((productEquiv F ζ hζ).symm k.val).1 ∈ KPContSectorArchSphericalFibers.KInfinity F ∧
    ((productEquiv F ζ hζ).symm k.val).2 ∈ U.toOpenSubgroup := by
  rcases k with ⟨k,hk⟩
  rw [K_U_eq] at hk
  obtain ⟨p,hp,he⟩ := hk
  change productEquiv F ζ hζ p = k at he
  subst k
  change ((productEquiv F ζ hζ).symm (productEquiv F ζ hζ p)).1 ∈ _ ∧
    ((productEquiv F ζ hζ).symm (productEquiv F ζ hζ p)).2 ∈ _
  rw [ContinuousMulEquiv.symm_apply_apply]
  exact hp

def archProjection : K_U F ζ hζ U →* K F where
  toFun k w := ⟨((productEquiv F ζ hζ).symm k.val).1 w, by
    rw [compactSubgroup_eq_origin_stabilizer]
    have hw := (mem_KInfinity_iff_stab F _).mp (split_mem F ζ hζ U k).1
    have he : KPCusp.complexPlace F (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w) = w :=
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ).left_inv w
    simpa only [he] using hw (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)⟩
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp

theorem archProjection_continuous : Continuous (archProjection F ζ hζ U) := by
  apply continuous_pi
  intro w
  apply Continuous.subtype_mk
  exact (continuous_apply w).comp (continuous_fst.comp
    ((productEquiv F ζ hζ).symm.continuous.comp continuous_subtype_val))

theorem archProjection_surjective : Function.Surjective (archProjection F ζ hζ U) := by
  intro k
  let a : KPSmoothActualFlowData.GInfinity F := fun w => (k w).val
  have ha : a ∈ KPContSectorArchSphericalFibers.KInfinity F := by
    rw [mem_KInfinity_iff_stab]
    intro i
    rw [←compactSubgroup_eq_origin_stabilizer]
    exact (k (KPCusp.complexPlace F i)).property
  have hg : productEquiv F ζ hζ (a,1) ∈ K_U F ζ hζ U := by
    rw [K_U_eq]
    exact ⟨(a,1),⟨ha,U.toOpenSubgroup.one_mem⟩,rfl⟩
  refine ⟨⟨_,hg⟩,?_⟩
  ext w
  change ((productEquiv F ζ hζ).symm (productEquiv F ζ hζ (a,1))).1 w = _
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem archProjection_measurePreserving
    (μ : Measure (K_U F ζ hζ U)) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (ν : Measure (K F)) [IsProbabilityMeasure ν] [ν.IsHaarMeasure] :
    MeasurePreserving (archProjection F ζ hζ U) μ ν :=
  MonoidHom.measurePreserving (archProjection_continuous F ζ hζ U)
    (archProjection_surjective F ζ hζ U) (by simp)

end DedekindZetaZeroFree.FourierContinuation.ResidualCompactAverageProjection

end
