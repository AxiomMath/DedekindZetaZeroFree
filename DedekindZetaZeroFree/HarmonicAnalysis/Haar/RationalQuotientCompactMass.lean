module

public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField Topology ENNReal Pointwise

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem quotientHaar_compact_ne_top
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (K : Set (KPSmoothLocalQuotientCharts.X F ζ hζ)) (hK : IsCompact K) :
    R.quotientHaar K ≠ ⊤ := by
  let q := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
  let ν := R.adelicHaar
  let D := R.domain
  haveI : T2Space (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  haveI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  haveI : IsTopologicalGroup (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  haveI : SecondCountableTopology (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ
  haveI : BorelSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := ⟨rfl⟩
  haveI : BorelSpace (KPSmoothLocalQuotientCharts.X F ζ hζ) := ⟨rfl⟩
  haveI : ν.IsHaarMeasure := R.adelic_isHaar
  haveI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) := by
    have hΓ := ActualQuotient.actual_rational_closed_discrete F ζ hζ
    exact (IsLindelof.countable_of_isDiscrete hΓ.1.isLindelof hΓ.2).to_subtype
  haveI : SMulInvariantMeasure (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) ν := inferInstance
  have hqcont : Continuous q := continuous_quot_mk
  have hqopen : IsOpenMap q := isOpenMap_quotient_mk'_mul

  have hpt : ∀ x : K, ∃ W : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ),
      IsOpen W ∧ (x : KPSmoothLocalQuotientCharts.X F ζ hζ) ∈ q '' W ∧ ν W < ⊤ := by
    intro x
    obtain ⟨g, hg⟩ := Quotient.mk_surjective (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds g
    refine ⟨interior C, isOpen_interior, ?_, ?_⟩
    · rw [← hg]
      exact ⟨g, mem_interior_iff_mem_nhds.2 hCn, rfl⟩
    · exact lt_of_le_of_lt (measure_mono interior_subset) hC.measure_lt_top
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => q '' (Classical.choose (hpt i)))
    (fun i => hqopen _ (Classical.choose_spec (hpt i)).1)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, (Classical.choose_spec (hpt ⟨x, hx⟩)).2.1⟩)
  set W : Set (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    ⋃ i ∈ t, Classical.choose (hpt i) with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact isOpen_biUnion fun i _ => (Classical.choose_spec (hpt i)).1
  have hWtop : ν W < ⊤ := by
    rw [hWdef]
    calc ν (⋃ i ∈ t, Classical.choose (hpt i))
        ≤ ∑ i ∈ t, ν (Classical.choose (hpt i)) := measure_biUnion_finset_le _ _
      _ < ⊤ := ENNReal.sum_lt_top.mpr
          (fun i _ => (Classical.choose_spec (hpt i)).2.2)

  have hKsub : K ⊆ q '' W := by
    intro x hx
    obtain ⟨i, hit, w, hw, hqw⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨w, ?_, hqw⟩
    rw [hWdef]
    exact Set.subset_biUnion_of_mem hit hw
  have hpre : q ⁻¹' (q '' W) ⊆
      ⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hy
    have hrel : QuotientGroup.rightRel (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
        w y := Quotient.exact hyw
    rw [QuotientGroup.rightRel_apply] at hrel
    refine Set.mem_iUnion.2
      ⟨(⟨y * w⁻¹, hrel⟩ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ), ?_⟩
    refine Set.mem_smul_set.2 ⟨w, hw, ?_⟩
    show (y * w⁻¹ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * w = y
    simp [mul_assoc]

  have hbound : ν (D ∩ ⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) ≤
      ν W := by
    have htsum : ν W = ∑' γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
        ν (W ∩ γ⁻¹ • D) :=
      (R.domain_fundamental.measure_eq_tsum' W).trans
        ((Equiv.inv (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)).tsum_eq
          (fun γ => ν (W ∩ γ • D))).symm
    have hsub : ν (D ∩ ⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) ≤
        ∑' γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ν (D ∩ γ • W) := by
      rw [Set.inter_iUnion]
      exact measure_iUnion_le _
    have hstep : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
        ν (D ∩ γ • W) = ν (W ∩ γ⁻¹ • D) := by
      intro γ
      rw [← measure_smul ν γ⁻¹ (D ∩ γ • W), Set.smul_set_inter, inv_smul_smul]
      exact congrArg ν (Set.inter_comm _ _)
    calc ν (D ∩ ⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W)
        ≤ ∑' γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ν (D ∩ γ • W) := hsub
      _ = ∑' γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ν (W ∩ γ⁻¹ • D) :=
          tsum_congr hstep
      _ = ν W := htsum.symm
  have hmeasUnion : MeasurableSet
      (⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) :=
    MeasurableSet.iUnion fun γ => hWopen.measurableSet.const_smul γ
  have hmain : R.quotientHaar K ≤ ν W := by
    calc R.quotientHaar K
        = Measure.map q (ν.restrict D) K := by
          rw [show R.quotientHaar = Measure.map q (ν.restrict D) from
            R.quotient_normalization.symm]
      _ ≤ Measure.map q (ν.restrict D) (q '' W) := measure_mono hKsub
      _ = ν.restrict D (q ⁻¹' (q '' W)) :=
          Measure.map_apply hqcont.measurable (hqopen W hWopen).measurableSet
      _ ≤ ν.restrict D
            (⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) :=
          measure_mono hpre
      _ = ν ((⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) ∩ D) :=
          Measure.restrict_apply hmeasUnion
      _ = ν (D ∩ ⋃ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, γ • W) :=
          congrArg ν (Set.inter_comm _ _)
      _ ≤ ν W := hbound
  exact ne_of_lt (lt_of_le_of_lt hmain hWtop)

end DedekindZetaZeroFree.KPGlobalResidualKernel.RawStageL2.TruncatedEstimate.CompactCore.ArchimedeanGeometry

end
