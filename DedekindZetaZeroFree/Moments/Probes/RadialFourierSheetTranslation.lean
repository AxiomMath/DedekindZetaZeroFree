module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates
public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace ProbeSheetTranslation
variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _

local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

def fieldUnit (A : SArithmeticData F) (r : A.R) (hr : r ≠ 0) : Fˣ :=
  Units.mk0 (r : F) (by exact_mod_cast hr)

def q (A : SArithmeticData F) (r : A.R) (hr : r ≠ 0) : ℝ :=
  A.norm (A.diagonal (fieldUnit A r hr))

def translatedFourier (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F A.Sf))
    (W0 : SLocalProduct F A.Sf → ℂ)
    (x : (SLocalProduct F A.Sf)ˣ) (t : A.G1) : ℂ :=
  ProbeWeight.fourier F A.Sf e μ W0 ((ProbeSheet.localUnits A t.val * x).val)

def fractionPoint (A : SArithmeticData F) (X : ℝ) (hX : 0 < X)
    (s a h : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (hh : h ≠ 0) :
    (SLocalProduct F A.Sf)ˣ :=
  ProbeSheet.ell A (q A s hs * X) *
    ProbeSheet.localUnits A (A.diagonal (fieldUnit A h hh)) /
    (ProbeSheet.localUnits A (A.diagonal (fieldUnit A s hs)) *
      ProbeSheet.localUnits A (A.diagonal (fieldUnit A a ha)))

private theorem norm_mul (A : SArithmeticData F) (x y : A.G) :
    A.norm (x * y) = A.norm x * A.norm y := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, _root_.norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem norm_div (A : SArithmeticData F) (x y : A.G) :
    A.norm (x / y) = A.norm x / A.norm y := by
  simp [SArithmeticData.norm, norm_div, div_pow, Finset.prod_div_distrib,
    mul_div_mul_comm]

private theorem norm_pos (A : SArithmeticData F) (x : A.G) : 0 < A.norm x := by
  apply mul_pos
  · apply Finset.prod_pos
    intro w hw
    exact pow_pos (norm_pos_iff.mpr (x.1 w).ne_zero) _
  · apply Finset.prod_pos
    intro v hv
    exact norm_pos_iff.mpr (x.2 v).ne_zero

private theorem norm_ell (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) :
    A.norm ((ProbeSheet.localUnits A).symm (ProbeSheet.ell A T)) = T := by
  simp only [ProbeSheet.ell, dif_pos hT, MulEquiv.symm_apply_apply]
  exact A.norm_radialSection T hT

end ProbeSheetTranslation

local instance instTranslationG1Measurable {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance instTranslationG1Borel {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

set_option maxHeartbeats 1000000

theorem probe_sheet_shape_translation (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (hnormalized : ProbeSheet.HaarDisintegration A ν dt)
    (w : InfinitePlace F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : (SLocalProduct F A.Sf)ˣ) (T : ℝ),
        0 < T → A.norm ((ProbeSheet.localUnits A).symm x) = T →
          Integrable (ProbeSheetTranslation.translatedFourier A e μ W0 x) dt ∧
          (∫ t, ProbeSheetTranslation.translatedFourier A e μ W0 x t ∂dt) =
            ProbeSheet.envelope A e μ dt W0 T ∧
          (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0 x t‖ ∂dt) =
            (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0
              (ProbeSheet.ell A T) t‖ ∂dt) ∧
          (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0 x t‖ ∂dt) ≤
            C * T ^ (-σ) := by
  letI := hdt
  have hm := probe_sheet_mellin_estimates_of_disintegration F A e he htrace hne
    μ ν dt hμ hν hdt hnormalized w W0 W1 hW0 hcompact hannular
  obtain ⟨C, hC, hbound⟩ := hm.2.1 σ 0 hσ
  refine ⟨C, hC, ?_⟩
  intro x T hT hx
  let k : A.G1 := ⟨(ProbeSheet.localUnits A).symm x /
      (ProbeSheet.localUnits A).symm (ProbeSheet.ell A T), by
    change A.norm _ = 1
    rw [ProbeSheetTranslation.norm_div, hx, ProbeSheetTranslation.norm_ell A T hT]
    exact div_self hT.ne'⟩
  have hshift (t : A.G1) :
      ProbeSheetTranslation.translatedFourier A e μ W0 x t =
      ProbeSheetTranslation.translatedFourier A e μ W0 (ProbeSheet.ell A T) (k * t) := by
    have hu : ProbeSheet.localUnits A k.val = x / ProbeSheet.ell A T := by
      simp [k]
    have hg : ProbeSheet.localUnits A t.val * x =
        ProbeSheet.localUnits A (k.val * t.val) * ProbeSheet.ell A T := by
      rw [map_mul, hu]
      calc
        _ = (ProbeSheet.localUnits A t.val * (x / ProbeSheet.ell A T)) *
            ProbeSheet.ell A T := by
          rw [mul_assoc, div_mul_cancel]
        _ = _ := by rw [mul_comm (ProbeSheet.localUnits A t.val)]
    exact congrArg (ProbeWeight.fourier F A.Sf e μ W0 ∘ Units.val) hg
  have hflow (y : SLocalProduct F A.Sf) : ProbeSheet.complexNormFlow A w 0 y = y := by
    dsimp [ProbeSheet.complexNormFlow, SLocalProduct, InfiniteAdeleRing] at y ⊢
    apply Prod.ext
    · apply funext
      intro v
      by_cases hv : v = w
      · subst v
        simp [ProbeSheet.complexNormFlow, Function.update_self]
      · simp [ProbeSheet.complexNormFlow, hv, Function.update_self]
    · rfl
  have hb := hbound T hT
  simp only [ProbeSheet.logDerivative, iteratedDeriv_zero, hflow] at hb
  have hi : Integrable
      (ProbeSheetTranslation.translatedFourier A e μ W0 (ProbeSheet.ell A T)) dt :=
    hb.1
  have hint : (∫ t, ProbeSheetTranslation.translatedFourier A e μ W0 x t ∂dt) =
      ProbeSheet.envelope A e μ dt W0 T := by
    simp_rw [hshift]
    exact integral_mul_left_eq_self _ k
  have hnorm : (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0 x t‖ ∂dt) =
      (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0
        (ProbeSheet.ell A T) t‖ ∂dt) := by
    simp_rw [hshift]
    exact integral_mul_left_eq_self (μ := dt)
      (fun t => ‖ProbeSheetTranslation.translatedFourier A e μ W0
        (ProbeSheet.ell A T) t‖) k
  refine ⟨?_, hint, hnorm, ?_⟩
  · have hf : ProbeSheetTranslation.translatedFourier A e μ W0 x =
        fun t => ProbeSheetTranslation.translatedFourier A e μ W0
          (ProbeSheet.ell A T) (k * t) := funext hshift
    rw [hf]
    exact hi.comp_mul_left k
  · rw [hnorm]
    exact hb.2

theorem probe_sheet_shape_translation_fraction (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct F A.Sf) (borel _))
    (ν : @Measure (SLocalProduct F A.Sf)ˣ
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)))
    (dt : @Measure A.G1 (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct F A.Sf) _ _ (borel _) μ)
    (hν : @Measure.IsHaarMeasure (SLocalProduct F A.Sf)ˣ _ _
      (@Units.instMeasurableSpace (SLocalProduct F A.Sf) _ (borel _)) ν)
    (hdt : @Measure.IsHaarMeasure A.G1 _ _ (borel _) dt)
    (hnormalized : ProbeSheet.HaarDisintegration A ν dt)
    (w : InfinitePlace F)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (hW0 : ProbeWeight.IsAnnularTensor F A.Sf W0)
    (hcompact : HasCompactSupport W0) (hannular : tsupport W0 ⊆ {x | IsUnit x})
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℝ) (hX : 0 < X) (s a h : A.R)
        (hs : s ≠ 0) (ha : a ≠ 0) (hh : h ≠ 0),
        let x := ProbeSheetTranslation.fractionPoint A X hX s a h hs ha hh
        let T := X * ProbeSheetTranslation.q A h hh /
          ProbeSheetTranslation.q A a ha
        0 < T ∧ A.norm ((ProbeSheet.localUnits A).symm x) = T ∧
          Integrable (ProbeSheetTranslation.translatedFourier A e μ W0 x) dt ∧
          (∫ t, ProbeSheetTranslation.translatedFourier A e μ W0 x t ∂dt) =
            ProbeSheet.envelope A e μ dt W0 T ∧
          (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0 x t‖ ∂dt) =
            (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0
              (ProbeSheet.ell A T) t‖ ∂dt) ∧
          (∫ t, ‖ProbeSheetTranslation.translatedFourier A e μ W0 x t‖ ∂dt) ≤
            C * T ^ (-σ) := by
  obtain ⟨C, hC, hbound⟩ := probe_sheet_shape_translation F A e he htrace hne
    μ ν dt hμ hν hdt hnormalized w W0 W1 hW0 hcompact hannular σ hσ
  refine ⟨C, hC, ?_⟩
  intro X hX s a h hs ha hh
  let x := ProbeSheetTranslation.fractionPoint A X hX s a h hs ha hh
  let T := X * ProbeSheetTranslation.q A h hh / ProbeSheetTranslation.q A a ha
  have hspos : 0 < ProbeSheetTranslation.q A s hs :=
    ProbeSheetTranslation.norm_pos A (A.diagonal (ProbeSheetTranslation.fieldUnit A s hs))
  have hapos : 0 < ProbeSheetTranslation.q A a ha :=
    ProbeSheetTranslation.norm_pos A (A.diagonal (ProbeSheetTranslation.fieldUnit A a ha))
  have hhpos : 0 < ProbeSheetTranslation.q A h hh :=
    ProbeSheetTranslation.norm_pos A (A.diagonal (ProbeSheetTranslation.fieldUnit A h hh))
  have hT : 0 < T := div_pos (mul_pos hX hhpos) hapos
  have hx : A.norm ((ProbeSheet.localUnits A).symm x) = T := by
    dsimp [x, ProbeSheetTranslation.fractionPoint]
    rw [map_div, map_mul, map_mul, ProbeSheetTranslation.norm_div,
      ProbeSheetTranslation.norm_mul, ProbeSheetTranslation.norm_mul]
    simp only [MulEquiv.symm_apply_apply]
    rw [ProbeSheetTranslation.norm_ell A _ (mul_pos hspos hX)]
    change (ProbeSheetTranslation.q A s hs * X * ProbeSheetTranslation.q A h hh) /
      (ProbeSheetTranslation.q A s hs * ProbeSheetTranslation.q A a ha) = T
    dsimp [T]
    field_simp
  exact ⟨hT, hx, hbound x T hT hx⟩

end
end DedekindZetaZeroFree
