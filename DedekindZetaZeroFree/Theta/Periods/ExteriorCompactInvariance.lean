module

public import DedekindZetaZeroFree.Metaplectic.Torus.SixthPowerDiagonalLifts
public import DedekindZetaZeroFree.Geometry.RestrictedProductCoordinateDensity
public import DedekindZetaZeroFree.Metaplectic.Kubota.ClosedLocalCompactSubgroups

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources NumberField IsDedekindDomain
open scoped Classical Topology
open _root_.DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw renaming char_mem → char_mem
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem exterior_not_bad (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    ¬ KPAdelicCoverRestrictedProduct.Bad F p := by
  intro h
  apply hp
  apply R.A.above_six
  rcases h with h2 | h3
  · have hm := char_mem F p 2 h2
    convert p.asIdeal.mul_mem_left 3 hm using 1 <;> norm_num
  · have hm := char_mem F p 3 h3
    convert p.asIdeal.mul_mem_left 2 hm using 1 <;> norm_num

def exteriorFactor (w : KPHilbert.Place F) :
    Subgroup (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 w) :=
  match w with
  | Sum.inl _ => ⊥
  | Sum.inr p => if hp : p ∉ R.A.Sf then
      (KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 p
        (fun h3 => exterior_not_bad R p hp (Or.inr h3))).range
    else ⊥

theorem exteriorFactor_le_compact (w : KPHilbert.Place F) :
    exteriorFactor R w ≤ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 w := by
  cases w with
  | inl w => exact bot_le
  | inr p =>
    by_cases hp : p ∉ R.A.Sf
    · simp only [exteriorFactor, dif_pos hp, KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg (exterior_not_bad R p hp)]
      exact le_rfl
    · simp only [exteriorFactor, dif_neg hp]
      exact bot_le

theorem exteriorFactor_closed (w : KPHilbert.Place F) :
    letI := KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12 w
    IsClosed (exteriorFactor R w : Set (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 w)) := by
  letI := KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12 w
  cases w with
  | inl w =>
    exact ThetaForwardQuotientMeasurability.FullSplitProduct.RestrictedDensity.isClosed_bot_localCover
      R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
  | inr p =>
    by_cases hp : p ∉ R.A.Sf
    · simp only [exteriorFactor, dif_pos hp]
      exact ThetaForwardQuotientMeasurability.FullSplitProduct.RestrictedDensity.isClosed_range_kStar
        R.A.zeta12 R.A.primitive_zeta12 p _
    · simp only [exteriorFactor, dif_neg hp]
      exact ThetaForwardQuotientMeasurability.FullSplitProduct.RestrictedDensity.isClosed_bot_localCover
        R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)

theorem theta_full_exterior {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient)
    (k : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hk : ∀ w, k w ∈ exteriorFactor R w) (g : Group R) :
    T.theta v (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 k)) = T.theta v g := by
  letI : ∀ w : KPHilbert.Place F,
      TopologicalSpace (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 w) :=
    KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  let H := ((KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12))
  let C := KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12
  let J : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12) :=
    { carrier := {a | ∀ h : Group R, T.theta v (h * H a) = T.theta v h}
      one_mem' := by intro h; simp
      mul_mem' := by
        intro a b ha hb h
        rw [map_mul, ← mul_assoc, hb, ha]
      inv_mem' := by
        intro a ha h
        have he := ha (h * H a⁻¹)
        simpa only [map_inv, mul_assoc, inv_mul_cancel, mul_one] using he.symm }
  have hclosed : IsClosed (J : Set (KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)) := by
    change IsClosed {a | ∀ h : Group R, T.theta v (h * H a) = T.theta v h}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro h
    exact isClosed_eq (((T.automorphic v).1.1).comp
      (continuous_const.mul (QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk))) continuous_const
  have hsingle : RestrictedProductDensity.singleSet C (exteriorFactor R) ⊆ (J : Set _) := by
    rintro a ⟨w, b, hb, rfl⟩ h
    cases w with
    | inl w =>
      have he : b = 1 := hb
      simp [he, H]
    | inr p =>
      by_cases hp : p ∉ R.A.Sf
      · exact theta_exterior_spherical R T v p hp b
          (exteriorFactor_le_compact R (Sum.inr p) hb) h
      · have he : b = 1 := by simpa only [exteriorFactor, dif_neg hp, Subgroup.mem_bot] using hb
        simp [he, H]
  have hle : Subgroup.closure (RestrictedProductDensity.singleSet C (exteriorFactor R)) ≤ J :=
    (Subgroup.closure_le J).mpr hsingle
  have hd := RestrictedProductDensity.closure_closure_singleSet_eq_forall_mem C
    (exteriorFactor R) (exteriorFactor_closed R)
  have hmem : k ∈ closure (Subgroup.closure (RestrictedProductDensity.singleSet C (exteriorFactor R)) : Set _) := by
    rw [hd]
    exact hk
  exact (closure_minimal hle hclosed hmem) g

theorem upper_full_exterior {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient)
    (k : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (hk : ∀ w, k w ∈ exteriorFactor R w) (g : Group R) :
    upper R Q.dq (T.theta v)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 k)) =
      upper R Q.dq (T.theta v) g := by
  have hint := theta_upper_integrable R T v g
  unfold upper
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc, theta_full_exterior R T v k hk]

end DedekindZetaZeroFree.DigitMasks

end
