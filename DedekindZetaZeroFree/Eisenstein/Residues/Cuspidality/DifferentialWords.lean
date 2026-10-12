module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residual.IteratedRightDerivatives

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAllWordCusp
open KPMsGreenFlux KPMsGreenFlux.IntrinsicAveraging KPSmoothActualFlowData
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
theorem constantTerm_word_zero
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (hz : constantTerm A dn j (IntrinsicAveraging.pullback f) = 0)
    (word : List (B F)) :
    constantTerm A dn j (IntrinsicAveraging.pullback (wordDerivative F ζ hζ word f)) = 0 := by
  induction word with
  | nil => exact hz
  | cons b word ih =>
    rw [← ResidualIntrinsicJets.rightDerivative_constantTerm_word A dn j f hf word b.1 b.2, ih]
    funext g
    simp [rightDerivative]

theorem constantTerm_eq_upper (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (g : Cover F ζ hζ) :
    constantTerm A dn j (IntrinsicAveraging.pullback f) g =
      ∫ q, IntrinsicAveraging.pullback f
        (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
          ((cuspRepresentative A j)⁻¹ * g)) ∂dn := by
  apply integral_congr_ae
  filter_upwards [] with q
  have hmem : cuspRepresentative A j ∈
      KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := ⟨_, rfl⟩
  simpa only [mul_assoc] using IntrinsicAveraging.pullback_rational f
    ⟨cuspRepresentative A j, hmem⟩
    (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
      ((cuspRepresentative A j)⁻¹ * g))

theorem upper_actualRightWord_zero
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : ∀ w, SmoothAutomorphic F ζ hζ (wordDerivative F ζ hζ w f))
    (hz : ∀ g, ∫ q, IntrinsicAveraging.pullback f
      (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g) ∂dn = 0)
    (word : List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
    (g : Cover F ζ hζ) :
    ∫ q, KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ word
      (IntrinsicAveraging.pullback f)
      (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g) ∂dn = 0 := by
  have hz' : constantTerm A dn j (IntrinsicAveraging.pullback f) = 0 := by
    funext g
    rw [constantTerm_eq_upper A dn j f g]
    exact hz _
  let ww := word.map (KPMsClearedTruncationL2.NativeWordBridge.wordIndexEquiv F)
  have hh := congrFun (constantTerm_word_zero A dn j f hf hz' ww)
    (cuspRepresentative A j * g)
  rw [constantTerm_eq_upper A dn j] at hh
  have he : KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ word
      (IntrinsicAveraging.pullback f) = IntrinsicAveraging.pullback
        (wordDerivative F ζ hζ ww f) := by
    funext x
    exact KPMsClearedTruncationL2.NativeWordBridge.actualRightWord_eq_wordDerivative
      F ζ hζ word f x
  rw [he]

  simpa only [inv_mul_cancel_left, Pi.zero_apply, IntrinsicAveraging.pullback, ww,
    KPMsClearedTruncationL2.NativeWordBridge.actualRightWord_eq_wordDerivative] using hh

include A in
theorem upper_word_zero
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (f : ResidualWeakEnergy.smoothAllWordL2 R)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (hz : ∀ g, ∫ q, f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g)) ∂dn = 0)
    (v : List (B F)) (g : Cover F ζ hζ) :
    ∫ q, wordDerivative F ζ hζ v f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g)) ∂dn = 0 := by
  let i : Fin A.componentCount := ⟨0, A.positive_componentCount⟩
  let j : Cusps A := ⟨i, ⟨0, (A.cuspAtlas i).positive_cuspCount⟩⟩
  let W := v.map (KPMsClearedTruncationL2.NativeWordBridge.wordIndexEquiv F).symm
  have hW : W.map (KPMsClearedTruncationL2.NativeWordBridge.wordIndexEquiv F) = v := by
    simp [W]
  have hh := upper_actualRightWord_zero A dn j f.val
    (fun w => (f.property w).1) hz W g
  have hp (a : Cover F ζ hζ) :
      KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ W
        (IntrinsicAveraging.pullback f.val) a =
      wordDerivative F ζ hζ v f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a) := by
    change KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ W
      (fun aa => f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ aa)) a = _
    rw [KPMsClearedTruncationL2.NativeWordBridge.actualRightWord_eq_wordDerivative, hW]
  have he : (∫ q, wordDerivative F ζ hζ v f.val (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g)) ∂dn) =
      ∫ q, KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ W
        (IntrinsicAveraging.pullback f.val)
        (KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) * g) ∂dn := by
    apply integral_congr_ae
    filter_upwards [] with q
    exact (hp _).symm
  exact he.trans hh

end DedekindZetaZeroFree.FourierContinuation.ResidualAllWordCusp

end
