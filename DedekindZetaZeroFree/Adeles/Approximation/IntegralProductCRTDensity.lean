module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.IntegralCompletionDensity

@[expose] public section

namespace DedekindZetaZeroFree
open IsDedekindDomain

noncomputable def ringOfIntegers_integralDiagonal
    (F : Type*) [Field F] [NumberField F] :
    NumberField.RingOfIntegers F →
      ((v : HeightOneSpectrum (NumberField.RingOfIntegers F)) → v.adicCompletionIntegers F) :=
  fun a v => algebraMap (NumberField.RingOfIntegers F) (v.adicCompletionIntegers F) a

private theorem integral_congruence_neighborhood
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (U : Set (v.adicCompletionIntegers F)) (hU : IsOpen U)
    (x : v.adicCompletionIntegers F) (hx : x ∈ U) :
    ∃ (a : NumberField.RingOfIntegers F) (n : ℕ),
      ∀ b : NumberField.RingOfIntegers F, b - a ∈ v.asIdeal ^ n →
        algebraMap (NumberField.RingOfIntegers F) (v.adicCompletionIntegers F) b ∈ U := by
  obtain ⟨a, ha⟩ := (denseRange_ringOfIntegers_adicCompletionIntegers F v).mem_nhds
    (hU.mem_nhds hx)
  obtain ⟨u, hu, huU⟩ := (mem_nhds_subtype _
    (algebraMap (NumberField.RingOfIntegers F) (v.adicCompletionIntegers F) a) U).mp
      (hU.mem_nhds ha)
  obtain ⟨ε, hε⟩ := Valued.mem_nhds.mp hu
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom ε
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt (Units.ne_zero γ)
  refine ⟨a, n, fun b hb => huU ?_⟩
  apply hε
  apply Valued.v.restrict_lt_iff_lt_embedding.mpr
  change Valued.v
    ((algebraMap (NumberField.RingOfIntegers F) (v.adicCompletion F) b) -
      (algebraMap (NumberField.RingOfIntegers F) (v.adicCompletion F) a)) < _
  rw [← map_sub]
  have heq : Valued.v ((algebraMap (NumberField.RingOfIntegers F)
      (v.adicCompletion F)) (b - a)) = v.intValuation (b - a) :=
    (v.valuedAdicCompletion_eq_valuation (K := F) (b - a)).trans
      (v.valuation_of_algebraMap (K := F) (b - a))
  rw [heq]
  exact ((v.intValuation_le_pow_iff_mem (b - a) n).mpr hb).trans_lt hn

theorem exists_ringOfIntegers_integralDiagonal_mem_finite_open
    (F : Type*) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (x : (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) → v.adicCompletionIntegers F)
    (U : (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
      Set (v.adicCompletionIntegers F))
    (hU : ∀ v ∈ T, IsOpen (U v) ∧ x v ∈ U v) :
    ∃ a : NumberField.RingOfIntegers F,
      ∀ v ∈ T, algebraMap (NumberField.RingOfIntegers F)
        (v.adicCompletionIntegers F) a ∈ U v := by
  classical
  have hlocal (v : T) := integral_congruence_neighborhood F v (U v)
    (hU v v.property).1 (x v) (hU v v.property).2
  choose a n hn using hlocal
  let e (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) : ℕ :=
    if hv : v ∈ T then n ⟨v, hv⟩ else 0
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := T) (fun v => v.asIdeal) e (fun v _ => v.prime)
    (fun v _ w _ hvw => HeightOneSpectrum.asIdeal_injective.ne hvw) a
  refine ⟨b, fun v hv => hn ⟨v, hv⟩ b ?_⟩
  simpa only [e, dif_pos hv] using hb v hv

theorem denseRange_ringOfIntegers_integralDiagonal
    (F : Type*) [Field F] [NumberField F] :
    DenseRange (ringOfIntegers_integralDiagonal F) := by
  intro x
  rw [mem_closure_iff]
  intro U hU hx
  obtain ⟨T, u, hu, huU⟩ := isOpen_pi_iff.mp hU x hx
  obtain ⟨a, ha⟩ := exists_ringOfIntegers_integralDiagonal_mem_finite_open F T x u hu
  exact ⟨ringOfIntegers_integralDiagonal F a, huU (fun v hv => ha v hv), ⟨a, rfl⟩⟩

end DedekindZetaZeroFree
