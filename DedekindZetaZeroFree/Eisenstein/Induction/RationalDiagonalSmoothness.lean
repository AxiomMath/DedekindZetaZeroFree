module

public import DedekindZetaZeroFree.Metaplectic.Torus.Charts.WeightedJetEstimates

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.RationalDiagonalSectionSmoothness
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalArchUnits (y : Fˣ) (w : InfinitePlace F) : ℂˣ :=
  Units.map ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      (algebraMap F (KPHilbert.Completion F (Sum.inl w)))) y

theorem rationalLift_split (y : Fˣ) :
    ∃ b : G F ζ hζ, b ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ ∧
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y).val.val =
        KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * b := by
  let r := KPAdelicCoverRestrictedProduct.rationalTuple F ζ hζ (KubotaRankTwo.d F y 1)
  let a := KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ
    (fun w => (rationalArchUnits F ζ hζ y w : ℂ))
  let q := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
  refine ⟨q (a⁻¹ * r), ?_, ?_⟩
  · refine ⟨a⁻¹ * r, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change (a (Sum.inl w))⁻¹ * r (Sum.inl w) = 1
    have he : a (Sum.inl w) = r (Sum.inl w) := by
      change KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ _ (Sum.inl w) =
        KPAdelicCoverRestrictedProduct.rationalCoordinates F ζ hζ _ (Sum.inl w)
      rw [KPAdelicCoverRestrictedProduct.rationalCoordinates_A]
      change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : (rationalArchUnits F ζ hζ y w : ℂ) = 0 then 1 else
          Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm (rationalArchUnits F ζ hζ y w)) _) = _
      simp only [Units.ne_zero, ↓reduceDIte]
      congr 1
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w))
              (algebraMap F (KPHilbert.Completion F (Sum.inl w)) y.val)) = _
      exact RingEquiv.symm_apply_apply _ _
    change (a (Sum.inl w))⁻¹ * r (Sum.inl w) = 1
    rw [he, inv_mul_cancel]
  · change q r = q a * q (a⁻¹ * r)
    simp

theorem rational_eval_contDiffOn (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ P)
    (hf : f ∈ InducedLevel F ζ hζ P J) (g : G F ζ hζ) (y : Fˣ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val
        (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y).val)
      (groupArchDomain F) := by
  obtain ⟨b, hb, he⟩ := rationalLift_split F ζ hζ y
  have hc := (hf.1 (b * g)).comp
    (TorusChartTransport.groupArchDiagonalTransport_contDiff F
      (rationalArchUnits F ζ hζ y)).contDiffOn
    (fun z hz => (TorusChartTransport.groupArchDiagonalTransport_domain F
      (rationalArchUnits F ζ hζ y) z).2 hz)
  apply hc.congr
  intro z hz
  rw [TorusChartTransport.inducedFunctions_fiber_eval]
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      (KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y).val = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf,
      KPGlobalTorusPeriodizationInverse.rationalLift, delta_rational]
  rw [hhalf, inv_one, one_mul, he]
  have hcomm := (TorusChartTransport.groupArchChart_commutes_finite F ζ hζ b hb z).eq
  have hm : (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * b) *
        (groupArchChart F ζ hζ z * g) =
      (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun w => (rationalArchUnits F ζ hζ y w : ℂ)) * groupArchChart F ζ hζ z) * (b * g) := by
    rw [mul_assoc, ← mul_assoc b, ← hcomm]
    group
  rw [hm, TorusChartTransport.groupArchDiagonalTransport_absorption F ζ hζ _ z hz]
  rfl

end
end DedekindZetaZeroFree.RationalDiagonalSectionSmoothness
