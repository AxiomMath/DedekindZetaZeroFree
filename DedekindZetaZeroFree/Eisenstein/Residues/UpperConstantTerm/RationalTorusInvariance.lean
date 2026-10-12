module

public import DedekindZetaZeroFree.Adeles.Quotients.RationalDilation
public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.ContinuityAndInvariance
public import DedekindZetaZeroFree.Eisenstein.Induction.CompactModels.ScalarAngularDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryInvariance
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPGlobalCenterRationalCharacter renaming p_rational → p_rational
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ

theorem rational_torus_mem (y : Fˣ) :
    (KPGlobalTorusFunctionData.s F ζ hζ y).val ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
  refine ⟨KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.d F y 1),?_⟩
  rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
  rfl

theorem rational_root_commute (y : Fˣ) (a : KPGlobalTorusFunctionData.Adeles F) :
    KPGlobalTorusFunctionData.N F ζ hζ a * (KPGlobalTorusFunctionData.s F ζ hζ y).val =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val *
        KPGlobalTorusFunctionData.N F ζ hζ (KPAdditiveRationalDilation.dilation F y⁻¹ a) := by
  have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ
    (KPGlobalTorusFunctionData.s F ζ hζ y) (KPAdditiveRationalDilation.dilation F y⁻¹ a)
  rw [p_rational] at hn
  have ha : (IdeleGroup.unitEmbedding (𝓞 F) F y : KPGlobalTorusFunctionData.Adeles F) *
      KPAdditiveRationalDilation.dilation F y⁻¹ a = a := by
    change algebraMap F (KPGlobalTorusFunctionData.Adeles F) (y:F) *
      (algebraMap F (KPGlobalTorusFunctionData.Adeles F) (↑y⁻¹:F) * a) = a
    simp [← mul_assoc,← map_mul]
  rw [ha] at hn
  rw [← hn]
  group

theorem upper_rational (f : G → ℂ) (hc : Continuous f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀g, f (γ.val*g)=f g)
    (y : Fˣ) (g : G) :
    upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F) f
      ((KPGlobalTorusFunctionData.s F ζ hζ y).val*g) =
    upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F) f g := by
  let φ : KPAdditiveQuotient F → ℂ := fun q => f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)
  let μ := KPWildKernelUpperBound.quotientHaar F
  have he (q : KPAdditiveQuotient F) :
      f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*((KPGlobalTorusFunctionData.s F ζ hζ y).val*g)) =
      φ (KPAdditiveRationalDilation.quotientDilation F y⁻¹ q) := by
    rw [← mul_assoc,rational_root_commute,mul_assoc,hr ⟨_,rational_torus_mem y⟩]
    dsimp [φ]
    apply upper_integrand_descends f hr g
    exact (congrArg (KPAdditiveRationalDilation.quotientDilation F y⁻¹) (Quotient.out_eq q)).trans
      (Quotient.out_eq _).symm
  change (∫q, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*((KPGlobalTorusFunctionData.s F ζ hζ y).val*g)) ∂μ) = ∫q,φ q ∂μ
  simp_rw [he]
  obtain ⟨e,heq⟩ := KPAdditiveRationalDilation.quotientDilation_is_additive_homeomorphism F y⁻¹
  have hmp := KPAdditiveRationalDilation.quotientDilation_measurePreserving F y⁻¹ μ
  have hfun : (e : KPAdditiveQuotient F → KPAdditiveQuotient F) = KPAdditiveRationalDilation.quotientDilation F y⁻¹ := funext heq
  rw [← hfun] at hmp ⊢
  exact hmp.integral_comp e.toHomeomorph.measurableEmbedding φ
end DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryInvariance

end
