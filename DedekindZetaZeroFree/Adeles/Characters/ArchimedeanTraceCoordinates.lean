module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.ArchimedeanTraceInversion
public import DedekindZetaZeroFree.Adeles.Characters.StandardComplexCharacter
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.TraceHaarTransport
open NumberField MeasureTheory KPCplxCharacterHaar
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance : MeasurableSpace (InfiniteAdeleRing F) := borel (InfiniteAdeleRing F)
local instance : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

open DedekindZetaZeroFree.ArchSelfDual (pi_complexMeasure_eq_smul_volume)

 def complexPlacesEquiv : InfinitePlace F ≃ {w : InfinitePlace F // w.IsComplex} where
  toFun w := ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  invFun w := w.val
  left_inv _ := rfl
  right_inv _ := rfl

def archTraceCoordinates : InfiniteAdeleRing F ≃ᵐ (InfinitePlace F → ℂ) where
  toEquiv := Equiv.piCongrRight (fun w =>
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toEquiv)
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro w
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).continuous.measurable.comp
      (@Continuous.measurable (InfiniteAdeleRing F) w.Completion _ _ _ _ _ _
        (fun a => a w) (continuous_apply w))
  measurable_invFun := by
    apply Continuous.measurable
    apply continuous_pi
    intro w
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.continuous.comp
      (continuous_apply w)

@[simp] theorem archTraceCoordinates_apply (a : InfiniteAdeleRing F) (w : InfinitePlace F) :
    archTraceCoordinates F ζ hζ a w =
      InfinitePlace.Completion.extensionEmbedding w (a w) := rfl

theorem measurePreserving_archTraceCoordinates :
    MeasurePreserving (archTraceCoordinates F ζ hζ) (KPAdditiveHaar.archMeasure F)
      (Measure.pi (fun _ : InfinitePlace F => characterHaar standardComplexParameter)) := by
  refine ⟨(archTraceCoordinates F ζ hζ).measurable, ?_⟩
  let : IsTotallyComplex F := primitive12_totallyComplex F ζ hζ
  let : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (KPHilbert.infinite_isComplex F ζ hζ w.val)) w.property⟩
  let e := MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace F => ℂ)
    (complexPlacesEquiv F ζ hζ).symm
  let u := PoissonArch.infiniteAdeleToSpace F
  let v := mixedEmbedding.euclidean.toMixed F
  have hcoord : (archTraceCoordinates F ζ hζ : InfiniteAdeleRing F → _) =
      fun a => e ((v (u a)).2) := by
    funext a w
    simp only [e, MeasurableEquiv.piCongrLeft, complexPlacesEquiv]
    rw [PoissonArch.infiniteAdeleToSpace_coordinates]
    rfl
  rw [hcoord, KPAdditiveHaar.archMeasure]
  have hu : Measurable u := u.continuous.measurable
  have hv : Measurable v := v.continuous.measurable
  have he : Measurable e := e.measurable
  have hmap : Measure.map (fun a : InfiniteAdeleRing F => e ((v (u a)).2))
      (Measure.map u.symm (PoissonArch.traceMeasure F)) =
      Measure.map e (Measure.map Prod.snd (Measure.map v (PoissonArch.traceMeasure F))) := by
    have hf : Measurable (fun a : InfiniteAdeleRing F => e ((v (u a)).2)) :=
      he.comp (measurable_snd.comp (hv.comp hu))
    rw [Measure.map_map hf u.symm.continuous.measurable]
    have hc : (fun a : InfiniteAdeleRing F => e ((v (u a)).2)) ∘ u.symm =
        e ∘ Prod.snd ∘ v := by funext a; simp
    rw [hc, ← Measure.map_map he (measurable_snd.comp hv), ← Measure.map_map measurable_snd hv]
  rw [hmap, PoissonArch.traceMeasure_map_toMixed, Measure.map_smul]
  change Measure.map e (ENNReal.ofReal (PoissonArch.haarScalar F) •
    Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)).prod
      (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)))) = _
  rw [Measure.map_snd_prod]
  have hm : (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)) Set.univ = 1 := by
    change (Measure.pi (fun _ => (volume : Measure ℝ))) Set.univ = _
    simp
  rw [hm, one_smul]
  have hp := measurePreserving_piCongrLeft
    (fun _ : InfinitePlace F => (volume : Measure ℂ)) (complexPlacesEquiv F ζ hζ).symm
  change Measure.map e
    (ENNReal.ofReal (PoissonArch.haarScalar F) •
      (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ))) = _
  rw [Measure.map_smul]
  have hp' : Measure.map e (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) =
      (volume : Measure (InfinitePlace F → ℂ)) := hp.map_eq
  rw [hp', show (fun _ : InfinitePlace F => characterHaar standardComplexParameter) =
    (fun _ => ArchSelfDual.complexMeasure) by
      funext w; rw [standard_complex_mass]; rfl, pi_complexMeasure_eq_smul_volume]
  congr 1
  simp [PoissonArch.haarScalar, ENNReal.ofReal_pow, InfinitePlace.nrComplexPlaces,
    Fintype.card_congr (complexPlacesEquiv F ζ hζ)]
  all_goals fun_prop

theorem archTraceCharacter_eq_standard (w : InfinitePlace F) (z : w.Completion) :
    archTraceCharacter w z = character (standardComplexParameter : ℂ)
      (archTraceCoordinates F ζ hζ (Pi.single w z) w) := by
  rw [archTraceCoordinates_apply, Pi.single_eq_same,
    archTraceCharacter_of_isComplex w (KPHilbert.infinite_isComplex F ζ hζ w)]
  change Circle.exp (2 * Real.pi * (2 * (InfinitePlace.Completion.extensionEmbedding w z).re)) =
    Circle.exp ((((4 * Real.pi : ℝ) : ℂ) * InfinitePlace.Completion.extensionEmbedding w z).re)
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem adelicTraceCharacter_arch_finite (a : InfiniteAdeleRing F)
    (b : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :
    (adelicTraceCharacter F ((a, b) : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) : ℂ) =
      (∏ w : InfinitePlace F, (character (standardComplexParameter : ℂ)
        (archTraceCoordinates F ζ hζ a w) : ℂ)) *
      (adelicTraceCharacter F ((0, b) : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) : ℂ) := by
  have h (w : InfinitePlace F) : archTraceCharacter w (a w) =
      character (standardComplexParameter : ℂ) (archTraceCoordinates F ζ hζ a w) := by
    simpa only [archTraceCoordinates_apply, Pi.single_eq_same] using
      archTraceCharacter_eq_standard F ζ hζ w (a w)
  simp only [adelicTraceCharacter_apply]
  rw [show (∏ w : InfinitePlace F, archTraceCharacter w (a w)) =
      ∏ w : InfinitePlace F, character (standardComplexParameter : ℂ)
        (archTraceCoordinates F ζ hζ a w) from Finset.prod_congr rfl (fun w _ => h w)]
  simp only [Circle.coe_mul]
  have hp := map_prod Circle.coeHom (fun w : InfinitePlace F =>
    character (standardComplexParameter : ℂ) (archTraceCoordinates F ζ hζ a w)) Finset.univ
  change (↑(∏ w, character (standardComplexParameter : ℂ) (archTraceCoordinates F ζ hζ a w)) : ℂ) =
    ∏ w, (character (standardComplexParameter : ℂ) (archTraceCoordinates F ζ hζ a w) : ℂ) at hp
  rw [hp]
  congr 1
  have hz : (∏ w : InfinitePlace F, archTraceCharacter w ((0 : InfiniteAdeleRing F) w)) = 1 := by
    apply Finset.prod_eq_one
    intro w hw
    exact (archTraceCharacter w).map_zero_eq_one
  rw [hz, Circle.coe_one, one_mul]

theorem integrable_archTraceCoordinates_iff (f : (InfinitePlace F → ℂ) → ℂ) :
    Integrable (fun a => f (archTraceCoordinates F ζ hζ a)) (KPAdditiveHaar.archMeasure F) ↔
      Integrable f (Measure.pi (fun _ : InfinitePlace F => characterHaar standardComplexParameter)) := by
  have h := measurePreserving_archTraceCoordinates F ζ hζ
  rw [← h.map_eq, (archTraceCoordinates F ζ hζ).measurableEmbedding.integrable_map_iff]
  rfl

theorem integral_archTraceCoordinates (f : (InfinitePlace F → ℂ) → ℂ) :
    (∫ a, f (archTraceCoordinates F ζ hζ a) ∂KPAdditiveHaar.archMeasure F) =
      ∫ x, f x ∂Measure.pi (fun _ : InfinitePlace F => characterHaar standardComplexParameter) := by
  have h := measurePreserving_archTraceCoordinates F ζ hζ
  rw [← h.map_eq, (archTraceCoordinates F ζ hζ).measurableEmbedding.integral_map]

end DedekindZetaZeroFree.TraceHaarTransport

end
