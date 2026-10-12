module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalDifferentNormalization

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

local instance ballMassCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance ballMassCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def localBallMass (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^
    (-(n : ℝ) - (localDifferentExponent F v : ℝ) / 2)

private lemma absNorm_cast_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.zero_lt_one.trans (finiteCompletion_residueCard_gt_one F v)
  exact_mod_cast h1

theorem localBallMass_pos (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    0 < localBallMass F v n := by
  rw [localBallMass]
  exact Real.rpow_pos_of_pos (absNorm_cast_pos F v) _

private lemma localBallMass_mul_absNorm (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localBallMass F v (n + 1) * (Ideal.absNorm v.asIdeal : ℝ) = localBallMass F v n := by
  have hQ := absNorm_cast_pos F v
  have key : (Ideal.absNorm v.asIdeal : ℝ) ^
        (-(↑(n+1) : ℝ) - (localDifferentExponent F v : ℝ) / 2 + 1) =
      (Ideal.absNorm v.asIdeal : ℝ) ^
          (-(↑(n+1) : ℝ) - (localDifferentExponent F v : ℝ) / 2) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := Real.rpow_add hQ _ _
  rw [Real.rpow_one] at key
  rw [localBallMass, localBallMass, ← key]
  congr 1
  push_cast
  ring

private lemma absNorm_mul_localBallMass_pred (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    (Ideal.absNorm v.asIdeal : ℝ) * localBallMass F v n = localBallMass F v (n - 1) := by
  have hQ := absNorm_cast_pos F v
  have key : (Ideal.absNorm v.asIdeal : ℝ) ^
        (1 + (-(↑n : ℝ) - (localDifferentExponent F v : ℝ) / 2)) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(↑n : ℝ) - (localDifferentExponent F v : ℝ) / 2) :=
    Real.rpow_add hQ _ _
  rw [Real.rpow_one] at key
  rw [localBallMass, localBallMass, ← key]
  congr 1
  push_cast
  ring

private lemma localNormalizedHaar_finiteCompletionBall_succ
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localNormalizedHaar F v (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      ENNReal.ofReal (Ideal.absNorm v.asIdeal : ℝ) *
        localNormalizedHaar F v (finiteCompletionBall F v (n+1) : Set (v.adicCompletion F)) := by
  obtain ⟨r, hrmem, hrdisj, hrunion⟩ := finiteCompletionBall_disjoint_coset_decomposition F v n
  have hmeasB : MeasurableSet (finiteCompletionBall F v (n+1) : Set (v.adicCompletion F)) :=
    (isCompact_finiteCompletionBall F v (n+1)).isClosed.measurableSet
  have hpre (i : Fin (Ideal.absNorm v.asIdeal)) :
      {x : v.adicCompletion F | x - r i ∈ finiteCompletionBall F v (n+1)} =
        (fun x => -(r i) + x) ⁻¹' (finiteCompletionBall F v (n+1) : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    have h : x - r i = -(r i) + x := by abel
    rw [h]
  have hmeas : ∀ i, MeasurableSet
      {x : v.adicCompletion F | x - r i ∈ finiteCompletionBall F v (n+1)} := by
    intro i
    rw [hpre i]
    exact hmeasB.preimage (by fun_prop)
  have hcoset : ∀ i, localNormalizedHaar F v
      {x : v.adicCompletion F | x - r i ∈ finiteCompletionBall F v (n+1)} =
      localNormalizedHaar F v (finiteCompletionBall F v (n+1) : Set (v.adicCompletion F)) := by
    intro i
    rw [hpre i, measure_preimage_add]
  rw [hrunion]
  rw [measure_iUnion hrdisj hmeas]
  simp_rw [hcoset]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul, ENNReal.ofReal_natCast]

private lemma localNormalizedHaar_finiteCompletionBall_zero
    (v : HeightOneSpectrum (𝓞 F)) :
    localNormalizedHaar F v (finiteCompletionBall F v 0 : Set (v.adicCompletion F)) =
      ENNReal.ofReal (localBallMass F v 0) := by
  have hset : (finiteCompletionBall F v 0 : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [finiteCompletionBall_zero]; rfl
  rw [hset, localNormalizedHaar_integerRing]
  have h0 : localBallMass F v 0 = localHalfDifferentFactor F v := by
    rw [localBallMass, localHalfDifferentFactor]
    congr 1
    push_cast
    ring
  rw [h0]

theorem localNormalizedHaar_finiteCompletionBall
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localNormalizedHaar F v (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      ENNReal.ofReal (localBallMass F v n) := by
  have hQpos := absNorm_cast_pos F v
  have hQne : ENNReal.ofReal (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hQpos
  have hfwd : ∀ k : ℕ,
      localNormalizedHaar F v (finiteCompletionBall F v (k:ℤ) : Set (v.adicCompletion F)) =
        ENNReal.ofReal (localBallMass F v (k:ℤ)) := by
    intro k
    induction k with
    | zero => simpa using localNormalizedHaar_finiteCompletionBall_zero F v
    | succ k ih =>
      have hrec := localNormalizedHaar_finiteCompletionBall_succ F v (k:ℤ)
      have hk : ((k:ℤ) + 1) = ((k+1:ℕ):ℤ) := by push_cast; ring
      rw [hk] at hrec
      have hreal : localBallMass F v (k:ℤ) =
          localBallMass F v ((k+1:ℕ):ℤ) * (Ideal.absNorm v.asIdeal : ℝ) := by
        have h := localBallMass_mul_absNorm F v (k:ℤ)
        rw [hk] at h
        exact h.symm
      have hof : ENNReal.ofReal (localBallMass F v (k:ℤ)) =
          ENNReal.ofReal (Ideal.absNorm v.asIdeal : ℝ) *
            ENNReal.ofReal (localBallMass F v ((k+1:ℕ):ℤ)) := by
        rw [hreal,
          ENNReal.ofReal_mul (le_of_lt (localBallMass_pos F v ((k+1:ℕ):ℤ))), mul_comm]
      have key : ENNReal.ofReal (Ideal.absNorm v.asIdeal : ℝ) *
            localNormalizedHaar F v
              (finiteCompletionBall F v ((k+1:ℕ):ℤ) : Set (v.adicCompletion F))
          = ENNReal.ofReal (Ideal.absNorm v.asIdeal : ℝ) *
            ENNReal.ofReal (localBallMass F v ((k+1:ℕ):ℤ)) := by
        rw [← hrec, ih, hof]
      exact (ENNReal.mul_right_inj hQne ENNReal.ofReal_ne_top).mp key
  have hbwd : ∀ k : ℕ,
      localNormalizedHaar F v (finiteCompletionBall F v (-(k:ℤ)) : Set (v.adicCompletion F)) =
        ENNReal.ofReal (localBallMass F v (-(k:ℤ))) := by
    intro k
    induction k with
    | zero => simpa using localNormalizedHaar_finiteCompletionBall_zero F v
    | succ k ih =>
      have hrec := localNormalizedHaar_finiteCompletionBall_succ F v (-((k+1:ℕ):ℤ))
      have hk : (-((k+1:ℕ):ℤ)) + 1 = -(k:ℤ) := by push_cast; ring
      rw [hk] at hrec
      have hstep : localBallMass F v (-((k+1:ℕ):ℤ)) =
          (Ideal.absNorm v.asIdeal : ℝ) * localBallMass F v (-(k:ℤ)) := by
        have h := absNorm_mul_localBallMass_pred F v (-(k:ℤ))
        rw [show (-(k:ℤ) - 1) = -((k+1:ℕ):ℤ) by push_cast; ring] at h
        exact h.symm
      rw [hrec, ih, hstep, ENNReal.ofReal_mul (le_of_lt hQpos)]
  obtain ⟨k, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact hfwd k
  · exact hbwd k

theorem localNormalizedHaar_finiteCompletionBall_coset
    (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletion F) (n : ℤ) :
    localNormalizedHaar F v {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n} =
      ENNReal.ofReal (localBallMass F v n) := by
  have hset : {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n} =
      (fun x => -b + x) ⁻¹' (finiteCompletionBall F v n : Set (v.adicCompletion F)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    have h : x - b = -b + x := by abel
    rw [h]
  rw [hset, measure_preimage_add, localNormalizedHaar_finiteCompletionBall]

theorem localNormalizedHaar_finiteCompletionBall_toReal
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    (localNormalizedHaar F v
      (finiteCompletionBall F v n : Set (v.adicCompletion F))).toReal =
        localBallMass F v n := by
  rw [localNormalizedHaar_finiteCompletionBall,
    ENNReal.toReal_ofReal (le_of_lt (localBallMass_pos F v n))]

theorem localBallMass_mul_dual (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localBallMass F v n *
      localBallMass F v (-n - (localDifferentExponent F v : ℤ)) = 1 := by
  have hQ := absNorm_cast_pos F v
  have hsum : (-(↑n : ℝ) - (localDifferentExponent F v : ℝ) / 2) +
      (-(↑(-n - (localDifferentExponent F v : ℤ)) : ℝ) -
        (localDifferentExponent F v : ℝ) / 2) = 0 := by
    push_cast
    ring
  rw [localBallMass, localBallMass, ← Real.rpow_add hQ, hsum, Real.rpow_zero]

end DedekindZetaZeroFree

end
