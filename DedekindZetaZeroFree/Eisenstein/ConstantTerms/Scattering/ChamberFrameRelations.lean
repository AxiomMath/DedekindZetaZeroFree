module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Scattering.AnalyticAdjugateFrames

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPLiteralRaw KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem coreScattering_chamber_frame (N : MomentSources.TraceHaarTransport R)
    (t : RestrictedTensorSimple.Level (bad R.A P C))
    (x : ∀ j : t.val, Plus R.A P C j.val) (q : KPFinitePlace F)
    (hq : Sum.inr q ∈ t.val) (g : Raw R.A)
    (μ : Measure (q.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1) :
    ∃ (ι : Type) (_ : Fintype ι)
      (e : LocalFiber F ζ hζ P C q ≃ₗ[ℂ] (ι → ℂ))
      (tests : ι → Plus R.A P C (Sum.inr q)) (d : ℂ → ℂ)
      (c : Plus R.A P C (Sum.inr q) → ℂ → ι → ℂ),
      AnalyticOnNhd ℂ d KPContinuation.spectralDomain ∧ d 0 = 1 ∧
      (∀ f i, AnalyticOnNhd ℂ (fun z => c f z i) KPContinuation.spectralDomain) ∧
      (∀ f, c f 0 = e (scatteringSlotOutput R P C q μ hμ 0 g f)) ∧
      (∀ z, (1 / 3 : ℝ) < z.re → ∀ f,
        d z * coreScattering R P C (slotCore R P C t x q hq f) z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ g)) =
        ∑ i, c f z i * coreScattering R P C (slotCore R P C t x q hq (tests i)) z
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ g))) := by
  obtain ⟨ι, hi, e, tests, d, c, hd, hd0, hc, hc0, hframe⟩ :=
    scatteringSlotOutput_frame R P C q μ hμ g
  letI : Fintype ι := hi
  refine ⟨ι, hi, e, tests, d, c, hd, hd0, hc, hc0, ?_⟩
  intro z hz f
  let A := scatteringSlotOutputLinear R P C q μ hμ z g
  let H := (coreScatteringLinear R P C z hz
    (scalarQuotient F ζ hζ (amalgamation F ζ hζ g))).comp
      (slotCore R P C t x q hq)
  have hk : A.ker ≤ H.ker := scatteringSlotOutputLinear_ker_le R P C N t x q hq g μ hμ z hz
  have hsumA : A (∑ i, c f z i • tests i) = ∑ i, c f z i • A (tests i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact A.map_smul _ _
  have hAz : d z • f + (-1 : ℂ) • (∑ i, c f z i • tests i) ∈ A.ker := by
    rw [LinearMap.mem_ker, A.map_add, A.map_smul, A.map_smul, hsumA]
    have hfA : d z • A f = ∑ i, c f z i • A (tests i) := hframe z f
    rw [← hfA]
    simp
  have hHz := hk hAz
  rw [LinearMap.mem_ker] at hHz
  simp only [map_add, map_smul, map_sum, smul_eq_mul, neg_one_mul] at hHz
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg, H, LinearMap.comp_apply,
    coreScatteringLinear, LinearMap.coe_mk, AddHom.coe_mk] using hHz)

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
