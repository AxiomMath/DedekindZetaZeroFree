module

public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalTraceAndResidueTransport
public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.QuotientRange
public import DedekindZetaZeroFree.Eisenstein.Residues.NonzeroReferenceVectors
public import DedekindZetaZeroFree.Theta.Whittaker.Exterior.NormalizedExistence
public import DedekindZetaZeroFree.Theta.Whittaker.Residues.NonzeroFourierCoefficient

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

open KPRankOneShellRepair KPLocalExceptionalConstruction KPLocalPrincipalSeries
open ExteriorWhittakerValues.ActualShellNormalization ExteriorWhittakerValues.ActualSpherical
open scoped ValuativeRel
open ValuativeRel

theorem actualReference_spherical (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    actualReference R P C μ hμ (Sum.inr q) ∈
      ImageFixed F ζ hζ q (actualImageData R P C μ hμ q).inducing
        (C.polarization q) (μ q) (hμ q) (C.actual_compact q hq).choose := by
  let ht := (C.actual_compact q hq).choose
  intro k
  obtain ⟨k,hk⟩ := k
  obtain ⟨a,ha⟩ := hk
  subst k
  apply Subtype.ext
  change IMinus (C.canonical q).borel (C.polarization q)
      (actualGoodCompactSplit F ζ hζ q ht a)
      (actualCanonicalForwardLinear F ζ hζ q (C.canonical q) (C.polarization q)
        (μ q) (hμ q) (plusReference R.A P C (Sum.inr q))) = _
  rw [← actualCanonicalForwardLinear_intertwines]
  have hk : actualGoodCompactSplit F ζ hζ q ht a ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup :
      Subgroup (ActualCover F ζ hζ q))
    have hm : actualGoodCompactSplit F ζ hζ q ht a ∈
        (actualGoodCompactSplit F ζ hζ q ht).range := MonoidHom.mem_range.mpr ⟨a,rfl⟩
    exact Eq.mpr (congrArg (fun K : Subgroup (ActualCover F ζ hζ q) =>
      actualGoodCompactSplit F ζ hζ q ht a ∈ K) (C.actual_compact q hq).choose_spec) hm
  rw [plusReference_fixed R.A P C q hq ⟨_,hk⟩]
  rfl

theorem actualReference_normalized_whittaker (hC : C.exceptional = R.A.Sf)
    (p : ThetaBranch.ExteriorPrime R.A) :
    ∃ L : MomentSources.actualLocal R (actualImageData R P C μ hμ) (Sum.inr p.val) →ₗ[ℂ] ℂ,
      IsWhittaker F ζ hζ p.val (actualImageData R P C μ hμ p.val).inducing
        (C.polarization p.val) (μ p.val) (hμ p.val) (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val) L ∧
      L (actualReference R P C μ hμ (Sum.inr p.val)) = 1 := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (valuation (LocalField F p.val)).integer)
  have hp : p.val ∉ C.exceptional := by simpa only [hC] using p.property
  obtain ⟨π,hπ,_⟩ := ExteriorWhittakerValues.ShellArithmetic.allowedGenerator_integer_irreducible R p
  exact ResidualExteriorWhittaker.exists_normalized_whittaker F ζ hζ p.val
    (actualImageData R P C μ hμ p.val).inducing (C.polarization p.val)
    (μ p.val) (hμ p.val) (C.actual_compact p.val hp).choose (ExteriorWhittakerValues.exterior_good_six p)
    π hπ (ExteriorWhittakerValues.ShellArithmetic.tracePsi p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_continuous p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_unitary p.val)
    (ExteriorWhittakerValues.ShellArithmetic.tracePsi_conductorZero R p π hπ)
    (actualReference R P C μ hμ (Sum.inr p.val))
    (actualReference_spherical R P C μ hμ p.val hp)
    (actualReference_ne_zero R P C μ hμ hC (Sum.inr p.val)
      (by simpa only [bad,KPGlobalResidualConstruction.ScalarAbsorption.fullBad,
        Finset.inr_mem_disjSum] using hp))
end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
