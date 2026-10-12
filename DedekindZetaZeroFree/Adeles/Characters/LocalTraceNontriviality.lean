module

public import DedekindZetaZeroFree.Adeles.Characters.QuotientParametrizationAndAnnihilator
public import DedekindZetaZeroFree.Adeles.Characters.LocalRestrictionsAndWhittakerForms
public import DedekindZetaZeroFree.Theta.Periods.ResidualQuotientOrbitIntegral

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open NumberField IsDedekindDomain
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

variable (F : Type) [Field F] [NumberField F]

def actualQuotientCircle (ψ : ContinuousAddChar (KPAdditiveQuotient F)) :
    AddChar (KPAdditiveQuotient F) Circle where
  toFun := characterCircle F ψ
  map_zero_eq_one' := by apply Subtype.ext; exact ψ.toAddChar.map_zero_eq_one
  map_add_eq_mul' := by
    intro x y
    apply Subtype.ext
    exact ψ.toAddChar.map_add_eq_mul x y

theorem actualQuotientCircle_trace_parameter
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) :
    ∃! t : F, ∀ x : KPAdeles F,
      ψ.toAddChar (QuotientAddGroup.mk x) =
        (adelicTraceCharacter F (algebraMap F (KPAdeles F) t * x) : ℂ) := by
  obtain ⟨t, ht, hu⟩ := KPAdelicQuotient.quotient_character_parametrization F
    (actualQuotientCircle F ψ) (characterCircle F ψ).continuous
  refine ⟨t, ?_, ?_⟩
  · intro x
    have h := congrArg (fun χ : AddChar (KPAdditiveQuotient F) Circle =>
      (χ (QuotientAddGroup.mk x) : ℂ)) ht
    exact h
  · intro s hs
    apply hu s
    apply AddChar.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    apply Subtype.ext
    exact hs x

theorem actualQuotientCircle_nonzero_trace_parameter
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ) :
    ∃ t : F, t ≠ 0 ∧ ∀ x : KPAdeles F,
      ψ.toAddChar (QuotientAddGroup.mk x) =
        (adelicTraceCharacter F (algebraMap F (KPAdeles F) t * x) : ℂ) := by
  obtain ⟨t, ht, _⟩ := actualQuotientCircle_trace_parameter F ψ
  refine ⟨t, ?_, ht⟩
  intro hz
  obtain ⟨q, hq⟩ := hψ
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  have h := ht x
  simp only [hz, map_zero, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one] at h
  exact hq h

theorem actualLocalAdditive_principal_mul (t : F) (v : KPHilbert.Place F)
    (x : KPHilbert.Completion F v) :
    algebraMap F (KPAdeles F) t * actualLocalAdditive F v x =
      actualLocalAdditive F v (algebraMap F (KPHilbert.Completion F v) t * x) := by
  cases v with
  | inl w =>
    apply Prod.ext
    · change (fun j : InfinitePlace F => algebraMap F j.Completion t) * Pi.single w x =
        Pi.single w (algebraMap F w.Completion t * x)
      exact (Pi.single_mul_right (i := w) x).symm
    · exact mul_zero _
  | inr q =>
    apply Prod.ext
    · exact mul_zero _
    · exact (RestrictedProduct.mul_single
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) q x _).symm

theorem actualLocalPsi_nontrivial (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ) (v : KPHilbert.Place F) :
    ∃ x : KPHilbert.Completion F v, (actualLocalPsi F ψ v).toAddChar x ≠ 1 := by
  obtain ⟨t, ht, hf⟩ := actualQuotientCircle_nonzero_trace_parameter F ψ hψ
  by_contra hn
  push Not at hn
  have hall (x : KPHilbert.Completion F v) :
      adelicTraceCharacter F (actualLocalAdditive F v
        (algebraMap F (KPHilbert.Completion F v) t * x)) = 1 := by
    apply Subtype.ext
    have h := hf (actualLocalAdditive F v x)
    rw [actualLocalAdditive_principal_mul] at h
    exact h.symm.trans (hn x)
  have hzero : algebraMap F (KPHilbert.Completion F v) t = 0 := by
    cases v with
    | inl w =>
      apply (archTraceCharacter_nondegenerate w _).mp
      intro x
      have h := hall x
      change adelicTraceCharacter F ((Pi.single w
        (algebraMap F w.Completion t * x), 0) : KPAdeles F) = 1 at h
      rwa [adelicTraceCharacter_arch_single] at h
    | inr q =>
      apply (localFiniteCharacter_nondegenerate F q _).mp
      intro x
      have h := hall x
      change adelicTraceCharacter F ((0, RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) q
        (algebraMap F (q.adicCompletion F) t * x)) : KPAdeles F) = 1 at h
      rwa [adelicTraceCharacter_finite_single] at h
  exact ht ((map_eq_zero (algebraMap F (KPHilbert.Completion F v))).mp hzero)

end DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw

end
