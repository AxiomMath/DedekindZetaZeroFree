module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem constantTerm_casimir_expansion
    (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : Cover F ζ hζ → ℂ)
    (hfi : ∀ (word : List (KPSmoothActualFlowData.B F)) g,
      Integrable (fun q =>
        (word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) f)
          (cuspRepresentative A j *
            KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
              (cuspRepresentative A j)⁻¹ * g)) dn) (g : Cover F ζ hζ) :
    constantTerm A dn j (casimir F ζ hζ f) g =
      ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
        (constantTerm A dn j (rightDerivative F ζ hζ w 0
            (rightDerivative F ζ hζ w 0 f)) g -
         constantTerm A dn j (rightDerivative F ζ hζ w 1
            (rightDerivative F ζ hζ w 1 f)) g +
         2 * (constantTerm A dn j (rightDerivative F ζ hζ w 2
                (rightDerivative F ζ hζ w 4 f)) g +
              constantTerm A dn j (rightDerivative F ζ hζ w 4
                (rightDerivative F ζ hζ w 2 f)) g -
              constantTerm A dn j (rightDerivative F ζ hζ w 3
                (rightDerivative F ζ hζ w 5 f)) g -
              constantTerm A dn j (rightDerivative F ζ hζ w 5
                (rightDerivative F ζ hζ w 3 f)) g)) := by
  let orbit := fun q => cuspRepresentative A j *
    KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
      (cuspRepresentative A j)⁻¹ * g
  let d := fun (w : NumberField.InfinitePlace F) (i k : Fin 6) q =>
    rightDerivative F ζ hζ w i (rightDerivative F ζ hζ w k f) (orbit q)
  have hd (w : NumberField.InfinitePlace F) (i k : Fin 6) : Integrable (d w i k) dn := by
    simpa only [List.foldr_cons, List.foldr_nil] using hfi [(w,i), (w,k)] g
  have hm (w : NumberField.InfinitePlace F) :
      Integrable (fun q => d w 2 4 q + d w 4 2 q - d w 3 5 q - d w 5 3 q) dn :=
    (((hd w 2 4).add (hd w 4 2)).sub (hd w 3 5)).sub (hd w 5 3)
  have hs (w : NumberField.InfinitePlace F) :
      Integrable (fun q => -((1 : ℂ) / 4) *
        (d w 0 0 q - d w 1 1 q + 2 *
          (d w 2 4 q + d w 4 2 q - d w 3 5 q - d w 5 3 q))) dn :=
    (((hd w 0 0).sub (hd w 1 1)).add ((hm w).const_mul 2)).const_mul (-((1 : ℂ) / 4))
  change (∫ q, ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
    (d w 0 0 q - d w 1 1 q + 2 *
      (d w 2 4 q + d w 4 2 q - d w 3 5 q - d w 5 3 q)) ∂dn) = _
  rw [integral_finset_sum _ (fun w _ => hs w)]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [integral_const_mul]
  rw [integral_add (f := fun q => d w 0 0 q - d w 1 1 q)
    (g := fun q => 2 * (d w 2 4 q + d w 4 2 q - d w 3 5 q - d w 5 3 q))
    ((hd w 0 0).sub (hd w 1 1)) ((hm w).const_mul 2),
    integral_sub (hd w 0 0) (hd w 1 1), integral_const_mul,
    integral_sub (f := fun q => d w 2 4 q + d w 4 2 q - d w 3 5 q)
      (((hd w 2 4).add (hd w 4 2)).sub (hd w 3 5)) (hd w 5 3),
    integral_sub (f := fun q => d w 2 4 q + d w 4 2 q)
      ((hd w 2 4).add (hd w 4 2)) (hd w 3 5),
    integral_add (hd w 2 4) (hd w 4 2)]
  rfl

theorem constant_term_commutes_of_rightDerivative_commutes
    (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : Cover F ζ hζ → ℂ)
    (hfi : ∀ (word : List (KPSmoothActualFlowData.B F)) g,
      Integrable (fun q =>
        (word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) f)
          (cuspRepresentative A j *
            KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
              (cuspRepresentative A j)⁻¹ * g)) dn)
    (hcomm : ∀ (word : List (KPSmoothActualFlowData.B F)), word.length ≤ 1 →
      ∀ (w : NumberField.InfinitePlace F) (i : Fin 6),
        let df := word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) f
        rightDerivative F ζ hζ w i (constantTerm A dn j df) =
          constantTerm A dn j (rightDerivative F ζ hζ w i df)) :
    casimir F ζ hζ (constantTerm A dn j f) =
      constantTerm A dn j (casimir F ζ hζ f) := by
  have hfirst (w : NumberField.InfinitePlace F) (i : Fin 6) :
      rightDerivative F ζ hζ w i (constantTerm A dn j f) =
        constantTerm A dn j (rightDerivative F ζ hζ w i f) :=
    hcomm [] (by simp) w i
  have hsecond (w : NumberField.InfinitePlace F) (i k : Fin 6) :
      rightDerivative F ζ hζ w i
        (rightDerivative F ζ hζ w k (constantTerm A dn j f)) =
      constantTerm A dn j
        (rightDerivative F ζ hζ w i (rightDerivative F ζ hζ w k f)) := by
    rw [hfirst]
    exact hcomm [(w,k)] (by simp) w i
  funext g
  rw [constantTerm_casimir_expansion A dn j f hfi g]
  simp only [casimir, hsecond]

end DedekindZetaZeroFree.KPMsGreenFlux

end
