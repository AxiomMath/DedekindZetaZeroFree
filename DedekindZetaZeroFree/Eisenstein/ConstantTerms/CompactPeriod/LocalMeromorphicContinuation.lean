module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberIntegrability
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.Analyticity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def numeratorProfile (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : Metric.ball (0 : ℂ) T.radius) (g : Group R) : C(KPAdditiveQuotient F, ℂ) :=
  ⟨fun q => T.cleared v s.val
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g),
    cleared_integrand_continuous T v s.val s.property g⟩

def upperCLM (Q : AdmissibleFlatSources R) : C(KPAdditiveQuotient F, ℂ) →L[ℂ] ℂ := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  let L : C(KPAdditiveQuotient F, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, f q ∂Q.dq
      map_add' := fun f h => integral_add
        (by simpa using f.continuous.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ)
        (by simpa using h.continuous.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ)
      map_smul' := fun c f => by simpa using integral_smul c (fun q => f q) }
  exact L.mkContinuous 1 (fun f => by
    change ‖∫ q, f q ∂Q.dq‖ ≤ 1 * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := Q.dq)
      (Filter.Eventually.of_forall f.norm_coe_le_norm))

@[simp] theorem upperCLM_apply (f : C(KPAdditiveQuotient F, ℂ)) :
    upperCLM Q f = ∫ q, f q ∂Q.dq := rfl

@[simp] theorem upperCLM_numeratorProfile (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    upperCLM Q (numeratorProfile T v s g) = upper R Q.dq (T.cleared v s.val) g := rfl

def localPeriod (T : Realization R Q) (v : R.A.UnitQuotient) (s : ℂ)
    (g : Group R) : ℂ := upper R Q.dq (T.cleared v s) g / s

theorem localPeriod_meromorphic (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) : MeromorphicOn (fun s => localPeriod T v s g)
      (Metric.ball (0 : ℂ) T.radius) :=
  (upper_cleared_analyticOnNhd T v g).meromorphicOn.div analyticOnNhd_id.meromorphicOn

theorem localPeriod_clears (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (hs0 : s ≠ 0) (g : Group R) :
    Integrable (fun q => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq ∧
    upper R Q.dq (T.cleared v s) g = s * localPeriod T v s g := by
  refine ⟨cleared_integrable T v s hs g, ?_⟩
  dsimp [localPeriod]
  field_simp

end DedekindZetaZeroFree.CompactPeriodAnalyticity.CompactPeriod

end
