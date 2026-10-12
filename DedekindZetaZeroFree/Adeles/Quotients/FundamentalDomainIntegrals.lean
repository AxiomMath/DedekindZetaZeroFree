module

public import DedekindZetaZeroFree.Theta.Unfolding.SheetFundamentalDomains

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped Topology
variable {F : Type} [Field F] [NumberField F]

structure PregroupingDomain (A : SArithmeticData F) where
  carrier : Set A.G1
  measurable : MeasurableSet carrier
  compact_closure : IsCompact (closure carrier)
  tiling : ∀ y : A.G1, ∃! γ : A.Gamma1, γ.val * y ∈ carrier

theorem pregroupingDomain_exists (A : SArithmeticData F) : Nonempty (PregroupingDomain A) := by
  obtain ⟨K, D, _, _, hD, hDc, _, ht⟩ := A.exists_multiplicative_quotient_balanced_tiling
  have hD' : MeasurableSet D := by
    convert hD using 1 <;> exact (BorelSpace.measurable_eq (α := A.G1))
  exact ⟨⟨D, hD', hDc, ht⟩⟩

def pregroupingDomain (A : SArithmeticData F) : PregroupingDomain A :=
  Classical.choice (pregroupingDomain_exists A)

def pregroupingSheet (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (l : PositiveAxis) : Set (Sheet A l) :=
  sheetTranslation A v₀ l '' (pregroupingDomain A).carrier

theorem pregroupingSheet_measurable (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (l : PositiveAxis) : MeasurableSet (pregroupingSheet A v₀ l) :=
  (sheetTranslation A v₀ l).measurableEmbedding.measurableSet_image.mpr
    (pregroupingDomain A).measurable

theorem pregroupingSheet_tiling (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (l : PositiveAxis) : ∀ y : Sheet A l, ∃! γ : A.Gamma1,
      γ • y ∈ pregroupingSheet A v₀ l := by
  let e := sheetTranslation A v₀ l
  have he (γ : A.Gamma1) (z : A.G1) : e (γ.val * z) = γ • e z := by
    apply Subtype.ext
    change normSection A v₀ l * (γ.val.val * z.val) =
      γ.val.val * (normSection A v₀ l * z.val)
    ac_rfl
  intro y
  obtain ⟨γ, hγ, hu⟩ := (pregroupingDomain A).tiling (e.symm y)
  have hm (δ : A.Gamma1) : δ • y ∈ pregroupingSheet A v₀ l ↔
      δ.val * e.symm y ∈ (pregroupingDomain A).carrier := by
    rw [← e.apply_symm_apply y, ← he]
    simpa only [pregroupingSheet, e.symm_apply_apply] using
      (e.injective.mem_set_image (s := (pregroupingDomain A).carrier)
        (a := δ.val * e.symm y))
  exact ⟨γ, (hm γ).mpr hγ, fun δ hδ => hu δ ((hm δ).mp hδ)⟩

theorem pregroupingSheet_fundamental (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    IsFundamentalDomain A.Gamma1 (pregroupingSheet A v₀ l) (sheetHaar A v₀ μG l) :=
  IsFundamentalDomain.mk' (pregroupingSheet_measurable A v₀ l).nullMeasurableSet
    (pregroupingSheet_tiling A v₀ l)

def pregroupingSheetHaar (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) : Measure (Sheet A l) :=
  (sheetHaar A v₀ μG l).restrict (pregroupingSheet A v₀ l)

theorem pregroupingSheetHaar_eq_map (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    pregroupingSheetHaar A v₀ μG l =
      Measure.map (sheetTranslation A v₀ l)
        ((kernelHaar A v₀ μG).restrict (pregroupingDomain A).carrier) := by
  rw [pregroupingSheetHaar, sheetHaar, pregroupingSheet,
    (sheetTranslation A v₀ l).measurableEmbedding.restrict_map,
    (sheetTranslation A v₀ l).injective.preimage_image]

theorem pregroupingSheet_projection (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    MeasurePreserving (sheetProjection A l) (pregroupingSheetHaar A v₀ μG l)
      (sheetQuotientHaar A v₀ μG l) :=
  sheetProjection_measurePreserving A v₀ μG l _ (pregroupingSheet_fundamental A v₀ μG l)

theorem pregroupingSheet_integral (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (f : SheetQuotient A l → ℂ) (hf : Integrable f (sheetQuotientHaar A v₀ μG l)) :
    (∫ z, f z ∂sheetQuotientHaar A v₀ μG l) =
      ∫ y, f (sheetProjection A l y) ∂pregroupingSheetHaar A v₀ μG l := by
  have hm := (pregroupingSheet_projection A v₀ μG l).map_eq
  rw [← hm]
  apply integral_map measurable_quotient_mk''.aemeasurable
  change AEStronglyMeasurable f (Measure.map (sheetProjection A l) (pregroupingSheetHaar A v₀ μG l))
  rw [hm]
  exact hf.aestronglyMeasurable

end DedekindZetaZeroFree.MomentSources

end
