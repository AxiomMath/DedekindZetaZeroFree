module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalInvariance
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory

namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent

theorem extension_of_compact_period
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (q : C(X, Y)) (hq : Function.Surjective q)
    (μ : Measure Y) [IsFiniteMeasure μ] :
    ∃ L : C(X, ℂ) →L[ℂ] ℂ, ∀ f : C(Y, ℂ),
      L (f.comp q) = ∫ y, f y ∂μ := by
  let T : C(Y, ℂ) →L[ℂ] C(X, ℂ) := ContinuousMap.compCLM ℂ ℂ q
  have hT : Function.Injective T := by
    intro f g h
    apply ContinuousMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact congrArg (fun a : C(X, ℂ) => a x) h
  let inv : T.toLinearMap.range →ₗ[ℂ] C(Y, ℂ) :=
    (LinearEquiv.ofInjective T.toLinearMap hT).symm.toLinearMap
  have heq (f : T.toLinearMap.range) (x : X) : inv f (q x) = f.val x := by
    have h := (LinearEquiv.ofInjective T.toLinearMap hT).apply_symm_apply f
    exact congrArg (fun a : T.toLinearMap.range => a.val x) h
  let l : T.toLinearMap.range →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y, inv f y ∂μ
      map_add' := by
        intro f g
        simp only [map_add, ContinuousMap.coe_add, Pi.add_apply]
        exact integral_add
          ((inv f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((inv g).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro z f
        simp only [map_smul, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact integral_const_mul z _ }
  have hb (f : T.toLinearMap.range) : ‖l f‖ ≤ μ.real Set.univ * ‖f‖ := by
    change ‖∫ y, inv f y ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    rw [mul_comm]
    apply norm_integral_le_of_norm_le_const
    apply Filter.Eventually.of_forall
    intro y
    obtain ⟨x, rfl⟩ := hq y
    rw [heq]
    exact f.val.norm_coe_le_norm x
  let lc := l.mkContinuous (μ.real Set.univ) hb
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq T.toLinearMap.range lc
  refine ⟨L, fun f => ?_⟩
  have h := hL ((LinearEquiv.ofInjective T.toLinearMap hT) f)
  change L (T f) = ∫ y, inv ((LinearEquiv.ofInjective T.toLinearMap hT) f) y ∂μ at h
  have hi : inv ((LinearEquiv.ofInjective T.toLinearMap hT) f) = f :=
    (LinearEquiv.ofInjective T.toLinearMap hT).symm_apply_apply f
  rw [hi] at h
  exact h

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.CompactPeriodDescent

namespace DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem upper_fiber_eq (θ : Functions F ζ hζ)
    (hθ : ∀ (γ : Matrix.ProjGenLinGroup (Fin 2) F) g, θ (rationalLift F ζ hζ γ * g) = θ g)
    (g : G F ζ hζ) (x : KPAdeles F) :
    θ (KPGlobalTorusFunctionData.N F ζ hζ
        (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) =
      θ (KPGlobalTorusFunctionData.N F ζ hζ x * g) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add
    (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  rw [hr, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact hθ _ _

theorem compact_additive_representatives :
    ∃ X : Set (KPAdeles F), IsCompact X ∧
      (QuotientAddGroup.mk : KPAdeles F → KPAdditiveQuotient F) '' X = Set.univ := by
  obtain ⟨B, hB, hcover⟩ := KPAdelicQuotient.exists_compact_infinite_cover F
  let X : Set (KPAdeles F) :=
    B ×ˢ (KPAdelicTopology.integralAdeles F : Set (KPAdelicTopology.FiniteAdeles F))
  refine ⟨X, hB.prod (KPAdelicTopology.integralAdeles_isCompact F), ?_⟩
  change KPAdelicQuotient.quotientMap F '' X = Set.univ
  exact hcover

end DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.QuotientUpperOrbit

end
