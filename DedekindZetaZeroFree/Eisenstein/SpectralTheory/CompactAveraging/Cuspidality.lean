module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspPeriods.UpperZeroInvariance
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SmoothAutomorphicAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAverageCusp
open KPMsGreenFlux
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
local instance (K : Subgroup (Cover F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (Cover F ζ hζ)) : BorelSpace K := ⟨rfl⟩
theorem constantTerm_average_zero (K : Subgroup (Cover F ζ hζ))
    (hK : IsCompact (K : Set (Cover F ζ hζ))) (ν : Measure K) [IsFiniteMeasure ν]
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) [IsFiniteMeasure dn]
    (j : Cusps A) (f : Cover F ζ hζ → ℂ) (hf : Continuous f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g, f (γ.val*g)=f g)
    (hz : constantTerm A dn j f = 0) :
    constantTerm A dn j (ResidualRawAverage.average F ζ hζ K ν f) = 0 := by
  letI : IsTopologicalGroup (Cover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  funext g
  let L : KPCompactFourier.AdditiveQuotient F × K → ℂ := fun p =>
    f (cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F p.1) * (cuspRepresentative A j)⁻¹ * (g*p.2.val))
  have hmap : Continuous (fun p : KPCompactFourier.AdditiveQuotient F × K =>
      (p.1, g * (p.2 : Cover F ζ hζ))) := by
    exact continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  have hc0 := FiniteSlabActualMean.integrand_joint_continuous (F := F) (ζ := ζ) (hζ := hζ) (hF := hF) (U := U) A j f hf hr
  have hc1 := hc0.comp hmap
  have hc : Continuous L := hc1
  have hi : Integrable L (dn.prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ q, ∫ k : K, f ((cuspRepresentative A j * KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F q) * (cuspRepresentative A j)⁻¹ * g)*k.val) ∂ν ∂dn) = 0
  simp only [mul_assoc]
  have he := integral_integral_swap (f := fun q k => L (q,k)) hi
  change (∫ q, ∫ k, L (q,k) ∂ν ∂dn) = (∫ k, ∫ q, L (q,k) ∂dn ∂ν) at he
  rw [show (∫ q, ∫ k : K, f (cuspRepresentative A j * (KPGlobalTorusFunctionData.N F ζ hζ
      (KPCompactFourier.representative F q) * ((cuspRepresentative A j)⁻¹ * (g*k.val)))) ∂ν ∂dn) =
      ∫ q, ∫ k, L (q,k) ∂ν ∂dn by simp only [L,mul_assoc], he]
  have hz' (k : K) : (∫ q, L (q,k) ∂dn) = 0 := congrFun hz (g*k.val)
  simp only [hz', integral_zero]
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabActualMean renaming cuspRepresentative_mem_rational → cuspRepresentative_mem_rational

theorem upper_zero_iff_constantTerm (j : Cusps A) (f : Cover F ζ hζ → ℂ)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g, f (γ.val*g)=f g) :
    ResidualCuspBoundary.UpperZero F ζ hζ f ↔
      constantTerm A (KPWildKernelUpperBound.quotientHaar F) j f = 0 := by
  have he (g : Cover F ζ hζ) :
      constantTerm A (KPWildKernelUpperBound.quotientHaar F) j f g =
      ∫ q : KPAdditiveQuotient F, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) *
        ((cuspRepresentative A j)⁻¹ * g)) ∂(KPWildKernelUpperBound.quotientHaar F) := by
    apply integral_congr_ae
    filter_upwards with q
    simpa only [mul_assoc, KPCompactFourier.representative] using hr ⟨cuspRepresentative A j, cuspRepresentative_mem_rational A j⟩
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q) * ((cuspRepresentative A j)⁻¹*g))
  constructor
  · intro hz
    funext g
    exact (he g).trans (hz _)
  · intro hz g
    have ht := he (cuspRepresentative A j * g)
    rw [hz] at ht
    simpa only [Pi.zero_apply, inv_mul_cancel_left] using ht.symm

theorem upperZero_average (j : Cusps A) (K : Subgroup (Cover F ζ hζ))
    (hK : IsCompact (K : Set (Cover F ζ hζ))) (ν : Measure K) [IsFiniteMeasure ν]
    (f : Cover F ζ hζ → ℂ) (hf : Continuous f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g, f (γ.val*g)=f g)
    (hz : ResidualCuspBoundary.UpperZero F ζ hζ f) :
    ResidualCuspBoundary.UpperZero F ζ hζ (ResidualRawAverage.average F ζ hζ K ν f) := by
  have har (γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (g) :
      ResidualRawAverage.average F ζ hζ K ν f (γ.val*g) =
        ResidualRawAverage.average F ζ hζ K ν f g := by
    apply integral_congr_ae
    filter_upwards with k
    simpa only [mul_assoc] using hr γ (g*k.val)
  apply (upper_zero_iff_constantTerm A j _ har).mpr
  exact constantTerm_average_zero A K hK ν _ j f hf hr
    ((upper_zero_iff_constantTerm A j f hr).mp hz)
end DedekindZetaZeroFree.FourierContinuation.ResidualAverageCusp

end
