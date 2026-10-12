module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.InvariantPairing
public import DedekindZetaZeroFree.Adeles.Quotients.Residual.LpAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualQuotientAveragePairing
open ResidualQuotientAverage
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => KPSmoothLocalQuotientCharts.ActualCover F ζ hζ
local notation "Xq" => KPSmoothLocalQuotientCharts.X F ζ hζ
local instance : IsTopologicalGroup G := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup G) : MeasurableSpace K := borel K
local instance (K : Subgroup G) : BorelSpace K := ⟨rfl⟩

theorem fixed_pairing_average (K : Subgroup G) (hK : IsCompact (K : Set G))
    (ν : Measure K) [IsProbabilityMeasure ν]
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (c f : Xq → ℂ) (hc2 : MemLp c 2 R.quotientHaar) (hf2 : MemLp f 2 R.quotientHaar)
    (hc : ∀ (k : K) x, c (KPSmoothActualFlowData.rightTranslate F ζ hζ k.val x) = c x) :
    (∫ x, star (c x) * ResidualQuotientAverage.average F ζ hζ K ν f x ∂ R.quotientHaar) =
      ∫ x, star (c x) * f x ∂ R.quotientHaar := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI : BorelSpace Xq := ⟨rfl⟩
  let Γ := KPSmoothActualFlowData.rationalSubgroup F ζ hζ
  have hopen : IsOpenQuotientMap (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    MulAction.isOpenQuotientMap_quotientMk
  have hΓ : IsClosed (Γ : Set G) :=
    (ActualQuotient.actual_rational_closed_discrete F ζ hζ).1
  letI : T2Space Xq :=
    (t2Space_iff_of_isOpenQuotientMap hopen).mpr (by
      convert hΓ.preimage (continuous_snd.mul continuous_fst.inv) using 1
      ext p
      exact Quotient.eq.trans (QuotientGroup.rightRel_apply (s := Γ)))
  letI : IsFiniteMeasureOnCompacts R.quotientHaar := ⟨fun K hK =>
    lt_top_iff_ne_top.mpr
      (KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry.quotientHaar_compact_ne_top R K hK)⟩
  letI : SecondCountableTopology G := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : ContinuousConstSMul Γ G := ⟨fun γ => continuous_const.mul continuous_id⟩
  letI : SecondCountableTopology Xq := ContinuousConstSMul.secondCountableTopology
  letI : SigmaCompactSpace Xq := by
    letI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
    rw [← isSigmaCompact_univ_iff]
    have hh := isSigmaCompact_range (continuous_quot_mk :
      Continuous (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ))
    change IsSigmaCompact (Set.range (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)) at hh
    rw [show Set.range (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) = Set.univ from
      Set.range_eq_univ.mpr Quotient.mk_surjective] at hh
    exact hh
  letI : SigmaFinite R.quotientHaar := SigmaFinite.of_isFiniteMeasureOnCompacts _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : BorelSpace Xq := ⟨rfl⟩
  letI : SecondCountableTopology K := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let act : K → Xq → Xq := fun k => KPSmoothActualFlowData.rightTranslate F ζ hζ k.val
  have hact : Continuous (Function.uncurry act) :=
    (action_continuous F ζ hζ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hmeas : Measurable (fun p : K × Xq => (p.1, act p.1 p.2)) :=
    (continuous_fst.prodMk hact).measurable
  apply ResidualAveragePairing.fixed_pairing_average (X := Xq) ν R.quotientHaar act hmeas
    (ResidualSubgroupHaar.quotient_subgroup_measurePreserving K hK R)
  · intro k
    let e : Xq ≃ₜ Xq :=
      { toFun := KPSmoothActualFlowData.rightTranslate F ζ hζ k.val
        invFun := KPSmoothActualFlowData.rightTranslate F ζ hζ k.val⁻¹
        left_inv := by
          intro x
          induction x using Quotient.inductionOn with
          | h g => change Quotient.mk _ ((g*k.val)*k.val⁻¹) = Quotient.mk _ g; simp
        right_inv := by
          intro x
          induction x using Quotient.inductionOn with
          | h g => change Quotient.mk _ ((g*k.val⁻¹)*k.val) = Quotient.mk _ g; simp
        continuous_toFun := (action_continuous F ζ hζ).comp (continuous_const.prodMk continuous_id)
        continuous_invFun := (action_continuous F ζ hζ).comp (continuous_const.prodMk continuous_id) }
    exact e.measurableEmbedding
  · exact hc2.star.integrable_mul hf2
  · exact hc

end DedekindZetaZeroFree.FourierContinuation.ResidualQuotientAveragePairing

end
