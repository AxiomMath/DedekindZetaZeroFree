module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.QuotientRange
public import DedekindZetaZeroFree.Theta.Whittaker.Residues.NonzeroFourierCoefficient
public import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw KPGlobalTorusFiniteStages ThetaExpansion TensorActionSource
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
variable (N : MomentSources.TraceHaarTransport R)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
local notation "W" => MomentSources.actualLocal R (actualImageData R P C μ hμ)
local notation "V" => RestrictedTensorSimple.Core W (actualReference R P C μ hμ) (bad R.A P C)
local notation "dq" => KPWildKernelUpperBound.quotientHaar F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem actualCoreResidue_automorphic (x : V) :
    Automorphic F ζ hζ (actualCoreResidue R P C μ hμ N x) := by
  have hm : actualCoreResidue R P C μ hμ N x ∈ (coreResidue R P C).range := by
    rw [← actualCoreResidue_range_eq R P C μ hμ N]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hm
  rw [← hy]
  exact coreResidue_raw_automorphic R P C y

theorem actualCoreResidue_period_integrable (x : V) (g : MomentSources.Group R) :
    Integrable (fun q : KPAdditiveQuotient F => actualCoreResidue R P C μ hμ N x
      (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g) *
      star (adelicTraceQuotientCharacter F q : ℂ)) dq := by
  exact (KPLiteralPeriod.haar_fourier_vanishing_forces_root_invariance F ζ hζ
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    dq inferInstance _ (actualCoreResidue_automorphic R P C μ hμ N x)).2.2.1 g

def actualCoreFourier (g : MomentSources.Group R) : V →ₗ[ℂ] ℂ where
  toFun x := MomentSources.fourier R dq (actualCoreResidue R P C μ hμ N x) g
  map_add' x y := by
    simp only [MomentSources.fourier,map_add,Pi.add_apply,add_mul]
    exact integral_add (actualCoreResidue_period_integrable R P C μ hμ N x g)
      (actualCoreResidue_period_integrable R P C μ hμ N y g)
  map_smul' c x := by
    simp only [MomentSources.fourier,map_smul,Pi.smul_apply,smul_eq_mul,mul_assoc]
    exact integral_const_mul c _

@[simp] theorem actualCoreFourier_apply (g : MomentSources.Group R) (x : V) :
    actualCoreFourier R P C μ hμ N g x = MomentSources.fourier R dq
      (actualCoreResidue R P C μ hμ N x) g := rfl

theorem actualCore_fourier_left_root (x : V) (a : KPAdeles F) (g : MomentSources.Group R) :
    actualCoreFourier R P C μ hμ N
      (KPGlobalTorusFunctionData.N F ζ hζ a*g) x =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk a) : ℂ) *
        actualCoreFourier R P C μ hμ N g x := by
  apply ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R dq _ ?_ a g
    (actualCoreResidue_period_integrable R P C μ hμ N x g)
  intro t g
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (actualCoreResidue_automorphic R P C μ hμ N x).2.1 _ _

theorem actual_upper_local_injection (q : KPFinitePlace F) (z : q.adicCompletion F) :
    KPGlobalTorusFunctionData.N F ζ hζ (KPRationalAdelicSplitting.localAdele F (Sum.inr q) z) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q)
          (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) z)) := by
  unfold KPGlobalTorusFunctionData.N KPAdelicCoverRestrictedProduct.localInjection
  congr 1
  change KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _ =
    KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _
  congr 1
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl p =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inl p) 0 =
      RestrictedProduct.mulSingle _ (Sum.inr q) _ (Sum.inl p)
    simp
  | inr p =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr p)
      (RestrictedProduct.single (fun w : KPFinitePlace F => w.adicCompletionIntegers F) q z p) =
      RestrictedProduct.mulSingle _ (Sum.inr q) _ (Sum.inr p)
    by_cases hp : p = q
    · subst p; simp
    · simp [hp,Ne.symm hp]

theorem actualCoreFourier_stage_finite (t : RestrictedTensorSimple.Level (bad R.A P C))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (x : ∀ j:t.val, W j.val) :
    actualCoreFourier R P C μ hμ N 1
      (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
          (KPRankOneShellRepair.actualCanonicalImageRepresentation F ζ hζ q
            (actualImageData R P C μ hμ q).inducing
            (actualImageData R P C μ hμ q).inducing.polarization (μ q) (hμ q)
            (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) a) (x ⟨Sum.inr q,hq⟩))))) =
    actualCoreFourier R P C μ hμ N
      (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a))
      (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
        (PiTensorProduct.tprod ℂ x)) := by
  unfold actualCoreFourier MomentSources.fourier
  simp only [LinearMap.coe_mk,AddHom.coe_mk,mul_one]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [actualCoreResidue_update_finite]

theorem actualCoreFourier_stage_upper (t : RestrictedTensorSimple.Level (bad R.A P C))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ t.val)
    (z : q.adicCompletion F) (x : ∀ j:t.val, W j.val) :
    actualCoreFourier R P C μ hμ N 1
      (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
        (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q,hq⟩
          (KPRankOneShellRepair.actualCanonicalImageRepresentation F ζ hζ q
            (actualImageData R P C μ hμ q).inducing
            (actualImageData R P C μ hμ q).inducing.polarization (μ q) (hμ q)
            (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) (x ⟨Sum.inr q,hq⟩))))) =
    (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
      (KPRationalAdelicSplitting.localAdele F (Sum.inr q) z)) : ℂ) *
    actualCoreFourier R P C μ hμ N 1
      (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
        (PiTensorProduct.tprod ℂ x)) := by
  have he := actualCoreFourier_stage_finite R P C μ hμ N t q hq
    (KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) z) x
  rw [← actual_upper_local_injection R q z] at he
  have hr := actualCore_fourier_left_root R P C μ hμ N
    (RestrictedTensorSimple.stageInclusion W (actualReference R P C μ hμ) (bad R.A P C) t
      (PiTensorProduct.tprod ℂ x)) (KPRationalAdelicSplitting.localAdele F (Sum.inr q) z) 1
  rw [mul_one] at hr
  exact he.trans hr

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
