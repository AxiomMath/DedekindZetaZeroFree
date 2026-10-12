module

public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerLocalProduct
public import DedekindZetaZeroFree.Adeles.Approximation.IntegralLocalCongruences
public import DedekindZetaZeroFree.Arithmetic.Ideals.SSupportedDenominators

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped Classical

namespace DedekindZetaZeroFree.PoissonSFiniteDensity

variable (F : Type*) [Field F] [NumberField F]

abbrev Space (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (v : S) → v.val.adicCompletion F

def diagonal (S : Finset (HeightOneSpectrum (𝓞 F))) :
    sIntegerRing F S →+* Space F S :=
  (RingHom.snd (InfiniteAdeleRing F) (Space F S)).comp (sIntegerDiagonal F S)

@[simp] theorem diagonal_apply (S : Finset (HeightOneSpectrum (𝓞 F)))
    (m : sIntegerRing F S) (v : S) :
    diagonal F S m v = algebraMap F (v.val.adicCompletion F) (m : F) := rfl

theorem local_congruence_approximation (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : S → ℤ) (b : Space F S) :
    ∃ m : sIntegerRing F S, ∀ v : S,
      algebraMap F (v.val.adicCompletion F) (m : F) - b v ∈
        PoissonSLocalBalls.ball F v.val (k v) := by
  obtain ⟨d, hd, -, hout, -, hclear⟩ :=
    DedekindZetaZeroFree.sSupported_denominator F S
  obtain ⟨t, ht⟩ := hclear b k
  have hdF : (d : F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd
  let y (v : S) : v.val.adicCompletionIntegers F :=
    ⟨algebraMap F (v.val.adicCompletion F) (d : F) ^ t * b v, (ht v).1⟩
  let n (v : S) : ℕ :=
    (k v + (t : ℤ) * (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)).toNat
  obtain ⟨a, ha⟩ := DedekindZetaZeroFree.sIntegral_crt F S y n
  have hquot : (a : F) / (d : F) ^ t ∈ sIntegerRing F S := by
    rw [DedekindZetaZeroFree.mem_sIntegerRing_iff]
    intro w hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (↑((a : F) / (d : F) ^ t) : w.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe, Valuation.map_div, Valuation.map_pow,
      w.valuation_of_algebraMap (K := F), w.valuation_of_algebraMap (K := F)]
    have hval : w.intValuation d = 1 := by
      rw [w.intValuation_eq_exp_neg_multiplicity hd, hout w hw, Nat.cast_zero,
        neg_zero, WithZero.exp_zero]
    rw [hval, one_pow, div_one]
    exact w.intValuation_le_one a
  refine ⟨⟨(a : F) / (d : F) ^ t, hquot⟩, ?_⟩
  intro v
  rw [PoissonSLocalBalls.mem_ball]
  have hv : (0 : ℤ) ≤ k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ) := (ht v).2
  have hn : ((n v : ℕ) : ℤ) = k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ) := Int.toNat_of_nonneg hv
  have hdlocal : (Valued.v (algebraMap F (v.val.adicCompletion F) (d : F)) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)) := by
    change Valued.v (FinitePlace.embedding v.val (d : F)) = _
    rw [FinitePlace.embedding_apply, HeightOneSpectrum.adicCompletion.valued_coe,
      v.val.valuation_of_algebraMap (K := F), v.val.intValuation_eq_exp_neg_multiplicity hd]
  have hcr : (Valued.v ((y v : v.val.adicCompletion F) -
      algebraMap F (v.val.adicCompletion F) (a : F)) : WithZero (Multiplicative ℤ)) ≤
      WithZero.exp (-(n v : ℤ)) := ha v
  have hm : algebraMap F (v.val.adicCompletion F) (d : F) ^ t *
      (algebraMap F (v.val.adicCompletion F) ((a : F) / (d : F) ^ t) - b v) =
      algebraMap F (v.val.adicCompletion F) (a : F) - (y v : v.val.adicCompletion F) := by
    dsimp only [y]
    rw [map_div₀ (algebraMap F (v.val.adicCompletion F)), map_pow]
    field_simp [(map_ne_zero (algebraMap F (v.val.adicCompletion F))).mpr hdF]
  have hval := congrArg (fun z : v.val.adicCompletion F =>
      (Valued.v z : WithZero (Multiplicative ℤ))) hm
  rw [map_mul, map_pow, hdlocal] at hval
  rw [← Valuation.map_sub_swap] at hcr
  rw [hn] at hcr
  have hexp : WithZero.exp (-(k v + (t : ℤ) *
      (multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ))) =
      WithZero.exp (-(multiplicity v.val.asIdeal (Ideal.span {d}) : ℤ)) ^ t *
        WithZero.exp (-k v) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  rw [hexp, ← hval] at hcr
  exact (mul_le_mul_iff_right₀
    (pow_pos (bot_lt_iff_ne_bot.mpr WithZero.exp_ne_zero) t)).mp hcr

theorem diagonal_denseRange (S : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (diagonal F S) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨b, hb⟩ := hUne
  obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.mp hU b hb
  have hn : ∀ v : S, ∃ k : ℤ,
      (PoissonSLocalBalls.ball F v.val k : Set (v.val.adicCompletion F)) ⊆
        {x | x + b v ∈ u v} := by
    intro v
    apply PoissonSLocalBalls.exists_ball_subset
    apply ((hu v).1.preimage (continuous_id.add continuous_const)).mem_nhds
    simpa using (hu v).2
  choose k hk using hn
  obtain ⟨m, hm⟩ := local_congruence_approximation F S k b
  refine ⟨diagonal F S m, ?_, ⟨m, rfl⟩⟩
  apply huU
  intro v _
  have hv := hk v (hm v)
  simpa only [Set.mem_setOf_eq, sub_add_cancel, diagonal_apply] using hv

end DedekindZetaZeroFree.PoissonSFiniteDensity

end
