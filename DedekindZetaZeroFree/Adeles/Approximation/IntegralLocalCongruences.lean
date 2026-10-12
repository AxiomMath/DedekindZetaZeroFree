module

public import DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity
public import DedekindZetaZeroFree.Arithmetic.LocalFields.ValuationBallsAndIntegrality

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

theorem sIntegral_crt
    (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (y : (v : S) → v.val.adicCompletionIntegers F)
    (n : S → ℕ) :
    ∃ a : RingOfIntegers F, ∀ v : S,
      (Valued.v (y v - algebraMap F (v.val.adicCompletion F) (a : F)) :
        WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(n v : ℤ)) := by
  classical

  set x : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun w => if hw : w ∈ S then y ⟨w, hw⟩ else 0 with hx
  set m : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun w => if hw : w ∈ S then n ⟨w, hw⟩ else 0 with hm

  set U : (w : HeightOneSpectrum (𝓞 F)) → Set (w.adicCompletionIntegers F) :=
    fun w => {z | ((z : w.adicCompletion F) -
      ((x w : w.adicCompletionIntegers F) : w.adicCompletion F)) ∈
        PoissonSLocalBalls.ball F w (m w)} with hU
  obtain ⟨a, ha⟩ := exists_ringOfIntegers_integralDiagonal_mem_finite_open F S x U
    (fun w _ => ⟨by
        have hcont : Continuous (fun z : w.adicCompletionIntegers F =>
            (z : w.adicCompletion F) -
              ((x w : w.adicCompletionIntegers F) : w.adicCompletion F)) :=
          continuous_subtype_val.sub continuous_const
        have hopen := (PoissonSLocalBalls.ball_isOpen F w (m w)).preimage hcont
        rw [hU]
        exact hopen
      , by
        rw [hU]
        simp only [Set.mem_setOf_eq, sub_self]
        exact (PoissonSLocalBalls.ball F w (m w)).zero_mem⟩)
  refine ⟨a, fun v => ?_⟩
  have hv := ha (v : HeightOneSpectrum (𝓞 F)) v.property
  rw [hU] at hv
  simp only [Set.mem_setOf_eq] at hv
  rw [PoissonSLocalBalls.mem_ball] at hv

  have hxv : x (v : HeightOneSpectrum (𝓞 F)) = y v := by
    rw [hx]
    simp only [dif_pos v.property]
  have hmv : m (v : HeightOneSpectrum (𝓞 F)) = n v := by
    rw [hm]
    simp only [dif_pos v.property]

  have hB : (algebraMap (𝓞 F) (v.val.adicCompletionIntegers F) a :
        v.val.adicCompletion F) =
      algebraMap F (v.val.adicCompletion F) (a : F) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion (𝓞 F) F (S := 𝓞 F) v.val) a
  rw [hB, hxv, hmv] at hv
  rw [Valuation.map_sub_swap]
  exact hv

end DedekindZetaZeroFree

end
