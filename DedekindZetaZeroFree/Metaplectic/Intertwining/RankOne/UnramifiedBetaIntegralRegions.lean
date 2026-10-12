module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicCharacterProjection

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition

open MeasureTheory ValuativeRel
noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def rawIntegrand (b u : ℂˣ) (y : Kˣ) : ℂ := by
  classical
  exact if h : 1 - (y : K) = 0 then 0 else
    (KPRankOneCubicProjection.eta K b y : ℂ) *
      (u ^ KPCubicExpansion.valuationExponent K (Units.mk0 (1 - (y : K)) h) : ℂ) /
      (KPCubicHaar.abs K (1 - (y : K)) : ℂ)

def rawA : ℂ := (KPCubicUnitIndices.residueCard K : ℂ)⁻¹

def small : Set Kˣ := {y | KPCubicHaar.abs K (y : K) < 1}

def nearOne : Set Kˣ := {y | KPCubicHaar.abs K (1 - (y : K)) < 1}

def large : Set Kˣ := {y | 1 < KPCubicHaar.abs K (y : K)}

def residue : Set Kˣ :=
  {y | KPCubicHaar.abs K (y : K) = 1 ∧ KPCubicHaar.abs K (1 - (y : K)) = 1}

variable [MeasurableSpace K] [BorelSpace K]

theorem four_regions (μ : Measure Kˣ) (f : Kˣ → ℂ)
    (hs : IntegrableOn f (small K) μ)
    (hn : IntegrableOn f (nearOne K) μ)
    (hl : IntegrableOn f (large K) μ)
    (hr : IntegrableOn f (residue K) μ) :
    Integrable f μ ∧
      ∫ y : Kˣ, f y ∂μ =
        (∫ y in small K, f y ∂μ) + (∫ y in nearOne K, f y ∂μ) +
          (∫ y in large K, f y ∂μ) + (∫ y in residue K, f y ∂μ) := by
  classical
  letI : BorelSpace Kˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
    rw [BorelSpace.measurable_eq (α := K),
      (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]⟩
  have hsmall : ∀ x : K, KPCubicHaar.abs K x < 1 →
      KPCubicHaar.abs K (1 - x) = 1 := by
    intro x hx
    have hv : valuation K x < valuation K 1 :=
      (KPCubicHaar.abs_lt_iff K one_ne_zero).mp (by simpa using hx)
    have hs := (valuation K).map_sub_eq_of_lt_left hv
    have hn : 1 - x ≠ 0 := by
      intro he
      simpa [he] using hs
    simp [KPCubicHaar.abs, hn, hs]
  have hlarge : ∀ x : K, 1 < KPCubicHaar.abs K x →
      KPCubicHaar.abs K (1 - x) = KPCubicHaar.abs K x := by
    intro x hx
    have hn : x ≠ 0 := by
      intro he
      have hf : (1 : ℝ) < 0 := by simpa [he] using hx
      linarith
    have hv : valuation K 1 < valuation K x :=
      (KPCubicHaar.abs_lt_iff K hn).mp (by simpa using hx)
    have hs := (valuation K).map_sub_eq_of_lt_right hv
    have hz : 1 - x ≠ 0 := by
      intro he
      exact ((Valuation.ne_zero_iff (valuation K)).mpr hn) (by simpa only [he, map_zero] using hs.symm)
    simp [KPCubicHaar.abs, hz, hn, hs]
  have hnear : ∀ y : Kˣ, y ∈ nearOne K → KPCubicHaar.abs K (y : K) = 1 := by
    intro y hy
    simpa only [sub_sub_cancel] using hsmall (1 - (y : K)) hy
  have dsn : Disjoint (small K) (nearOne K) := by
    rw [Set.disjoint_left]
    intro y hy hn
    have := hnear y hn
    change KPCubicHaar.abs K (y : K) < 1 at hy
    linarith
  have dsl : Disjoint (small K) (large K) := by
    rw [Set.disjoint_left]
    intro y hy hl
    change KPCubicHaar.abs K (y : K) < 1 at hy
    change 1 < KPCubicHaar.abs K (y : K) at hl
    linarith
  have dnl : Disjoint (nearOne K) (large K) := by
    rw [Set.disjoint_left]
    intro y hn hl
    have := hnear y hn
    change 1 < KPCubicHaar.abs K (y : K) at hl
    linarith
  have dr : Disjoint (small K ∪ nearOne K ∪ large K) (residue K) := by
    rw [Set.disjoint_left]
    intro y hy hr
    rcases hy with (hs | hn) | hl
    · exact (ne_of_lt hs) hr.1
    · exact (ne_of_lt hn) hr.2
    · exact (ne_of_gt hl) hr.1
  have cover : small K ∪ nearOne K ∪ large K ∪ residue K = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases lt_trichotomy (KPCubicHaar.abs K (y : K)) 1 with hs | he | hl
    · exact Or.inl (Or.inl (Or.inl hs))
    · rcases lt_trichotomy (KPCubicHaar.abs K (1 - (y : K))) 1 with hn | hz | hl
      · exact Or.inl (Or.inl (Or.inr hn))
      · exact Or.inr ⟨he, hz⟩
      · have h := hlarge (1 - (y : K)) hl
        simp only [sub_sub_cancel, he] at h
        linarith
    · exact Or.inl (Or.inr hl)
  have mn : MeasurableSet (nearOne K) := by
    have he : nearOne K = (fun y : Kˣ => 1 - (y : K)) ⁻¹'
        {x : K | (valuation K).restrict x < (valuation K).restrict 1} := by
      ext y
      change KPCubicHaar.abs K (1 - (y : K)) < 1 ↔ _
      rw [← KPCubicHaar.abs_one K, KPCubicHaar.abs_lt_iff K one_ne_zero]
      exact (valuation K).restrict_lt_iff.symm
    rw [he]
    exact (((valuation K).isOpen_ball _).preimage
      (continuous_const.sub Units.continuous_val)).measurableSet
  have mc : Continuous (fun y : Kˣ => KPCubicHaar.abs K (y : K)) :=
    (KPCubicHaar.abs_units_locallyConstant K).continuous
  have ms : MeasurableSet (small K) := (isOpen_lt mc continuous_const).measurableSet
  have ml : MeasurableSet (large K) := (isOpen_lt continuous_const mc).measurableSet
  have mr : MeasurableSet (residue K) := by
    have he : residue K = (small K ∪ nearOne K ∪ large K)ᶜ := by
      ext y
      constructor
      · intro hy hz
        exact Set.disjoint_left.mp dr hz hy
      · intro hy
        have hc : y ∈ small K ∪ nearOne K ∪ large K ∪ residue K := by rw [cover]; trivial
        exact hc.resolve_left hy
    rw [he]
    exact ((ms.union mn).union ml).compl
  have hsn := hs.union hn
  have hsnl := hsn.union hl
  have hall := hsnl.union hr
  have hi : Integrable f μ := by
    simpa only [cover, integrableOn_univ] using hall
  refine ⟨hi, ?_⟩
  have dsnl : Disjoint (small K ∪ nearOne K) (large K) := dsl.union_left dnl
  calc
    ∫ y : Kˣ, f y ∂μ = ∫ y in small K ∪ nearOne K ∪ large K ∪ residue K, f y ∂μ := by
      simp [cover]
    _ = (∫ y in small K ∪ nearOne K ∪ large K, f y ∂μ) +
        (∫ y in residue K, f y ∂μ) := setIntegral_union dr mr hsnl hr
    _ = ((∫ y in small K ∪ nearOne K, f y ∂μ) +
        (∫ y in large K, f y ∂μ)) + (∫ y in residue K, f y ∂μ) := by
      rw [setIntegral_union dsnl ml hsn hl]
    _ = _ := by rw [setIntegral_union dsn mn hs hn]

end
end DedekindZetaZeroFree.KPRankOneUnramifiedBetaShells.RegionDecomposition
