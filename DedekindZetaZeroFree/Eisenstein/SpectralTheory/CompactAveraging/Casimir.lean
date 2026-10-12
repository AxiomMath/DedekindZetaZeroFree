module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.DifferentialWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageCasimir
open KPLiteralRaw KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
open ResidualAverageWord
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming nativeIndex → nativeIndex
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming native_second_word → native_second_word
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (KPLiteralRaw.G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
theorem casimir_average
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact (K : Set (KPLiteralRaw.G F ζ hζ)))
    (μ : Measure K) [IsFiniteMeasure μ] (u : KPLiteralRaw.G F ζ hζ → ℂ)
    (hu : Smooth F ζ hζ u) (g : KPLiteralRaw.G F ζ hζ) :
    KPMsGreenFlux.casimir F ζ hζ (ResidualRawAverage.average F ζ hζ K μ u) g =
      ∫ k : K, KPMsGreenFlux.casimir F ζ hζ (fun a => u (a*k.val)) g ∂μ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D (v : NumberField.InfinitePlace F) (i j : Fin 6) (k : K) :=
    KPMsGreenFlux.rightDerivative F ζ hζ v i
      (KPMsGreenFlux.rightDerivative F ζ hζ v j (fun a => u (a*k.val))) g
  have hi (v) (i j : Fin 6) : Integrable (D v i j) μ := by
    have hc := translated_word_continuous F ζ hζ K hK μ u hu
      [nativeIndex F (v,i),nativeIndex F (v,j)] g
    simp_rw [native_second_word] at hc
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (v) (i j : Fin 6) : KPMsGreenFlux.rightDerivative F ζ hζ v i
      (KPMsGreenFlux.rightDerivative F ζ hζ v j (ResidualRawAverage.average F ζ hζ K μ u)) g =
      ∫ k, D v i j k ∂μ := by
    simpa only [native_second_word,D] using word_average F ζ hζ K hK μ u hu
      [nativeIndex F (v,i),nativeIndex F (v,j)] g
  have hslot (v) : Integrable (fun k => -((1:ℂ)/4) * (D v 0 0 k-D v 1 1 k+
      2*(D v 2 4 k+D v 4 2 k-D v 3 5 k-D v 5 3 k))) μ :=
    (((hi v 0 0).sub (hi v 1 1)).add
      (((((hi v 2 4).add (hi v 4 2)).sub (hi v 3 5)).sub (hi v 5 3)).const_mul 2)).const_mul _
  unfold KPMsGreenFlux.casimir
  simp_rw [he]
  change (∑ v, -((1:ℂ)/4)*((∫k,D v 0 0 k ∂μ)-(∫k,D v 1 1 k ∂μ)+
    2*((∫k,D v 2 4 k ∂μ)+(∫k,D v 4 2 k ∂μ)-(∫k,D v 3 5 k ∂μ)-(∫k,D v 5 3 k ∂μ)))) =
    ∫k,∑v,-((1:ℂ)/4)*(D v 0 0 k-D v 1 1 k+2*(D v 2 4 k+D v 4 2 k-D v 3 5 k-D v 5 3 k)) ∂μ
  rw [integral_finsetSum _ (fun v _ => hslot v)]
  apply Finset.sum_congr rfl
  intro v _
  have ia := integral_add ((hi v 0 0).sub (hi v 1 1))
    (((((hi v 2 4).add (hi v 4 2)).sub (hi v 3 5)).sub (hi v 5 3)).const_mul 2)
  have is0 := integral_sub (hi v 0 0) (hi v 1 1)
  have is1 := integral_sub (((hi v 2 4).add (hi v 4 2)).sub (hi v 3 5)) (hi v 5 3)
  have is2 := integral_sub ((hi v 2 4).add (hi v 4 2)) (hi v 3 5)
  have ia2 := integral_add (hi v 2 4) (hi v 4 2)
  simp only [Pi.sub_apply,Pi.add_apply] at ia is0 is1 is2 ia2
  rw [integral_const_mul,ia,is0,integral_const_mul,is1,is2,ia2]

end DedekindZetaZeroFree.FourierContinuation.ResidualAverageCasimir

end
