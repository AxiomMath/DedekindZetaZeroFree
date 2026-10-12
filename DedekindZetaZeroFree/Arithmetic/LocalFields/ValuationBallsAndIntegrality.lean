module

public import DedekindZetaZeroFree.Adeles.Characters.FractionalIdealOpenKernels
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompletionBallMass

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Filter Topology
open scoped Classical nonZeroDivisors WithZero

namespace DedekindZetaZeroFree.PoissonSLocalBalls

set_option backward.isDefEq.respectTransparency false

variable (F : Type*) [Field F] [NumberField F]

def ball (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) : AddSubgroup (v.adicCompletion F) :=
  (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).leAddSubgroup (WithZero.exp (-k))

@[simp] theorem mem_ball (v : HeightOneSpectrum (𝓞 F)) (k : ℤ)
    (x : v.adicCompletion F) :
    x ∈ ball F v k ↔ Valued.v x ≤ WithZero.exp (-k) := Iff.rfl

@[simp] theorem ball_zero (v : HeightOneSpectrum (𝓞 F)) :
    (ball F v 0 : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  ext x
  simp [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem ball_isOpen (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    IsOpen (ball F v k : Set (v.adicCompletion F)) := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-k))
  have hn : Valued.v.restrict a ≠ 0 := by
    intro h
    have ha0 : a = 0 := (Valued.v.restrict.map_eq_zero_iff).mp h
    exact WithZero.exp_ne_zero (ha.symm.trans (by simp [ha0]))
  convert Valued.isOpen_closedBall (v.adicCompletion F) hn using 1
  ext x
  simp only [ball, SetLike.mem_coe, Valuation.mem_leAddSubgroup_iff,
    Set.mem_setOf_eq, Valuation.restrict_le_iff, ha]

theorem ball_eq_normBall (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    (ball F v k : Set (v.adicCompletion F)) =
      {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)} := by
  have hq : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  ext x
  simp only [SetLike.mem_coe, mem_ball, Set.mem_setOf_eq]
  by_cases hx : x = 0
  · simp only [hx, map_zero, zero_le, norm_zero, true_iff]
    exact (zpow_pos (lt_trans zero_lt_one hq) (-k)).le
  have hv : Valued.v x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr hx
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
  change Valued.v x ≤ WithZero.exp (-k) ↔
    (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)
  rw [zpow_le_zpow_iff_right₀ hq, ← WithZero.log_exp (-k)]
  exact (WithZero.log_le_log hv WithZero.exp_ne_zero).symm

theorem ball_isCompact (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    IsCompact (ball F v k : Set (v.adicCompletion F)) := by
  rw [ball_eq_normBall]
  simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : v.adicCompletion F) ((v.asIdeal.absNorm : ℝ) ^ (-k))

theorem ball_basis_nat (v : HeightOneSpectrum (𝓞 F)) :
    (𝓝 (0 : v.adicCompletion F)).HasBasis (fun _ : ℕ => True)
      (fun n => (ball F v (n : ℤ) : Set (v.adicCompletion F))) := by
  refine Filter.HasBasis.mk fun U => ⟨?_, ?_⟩
  · intro hU
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
    have hn : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := by
      simpa using γ.ne_zero
    obtain ⟨n, hn'⟩ := WithZero.exists_exp_neg_natCast_lt hn
    refine ⟨n, trivial, fun x hx => hγ ?_⟩
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hx.trans_lt hn'
  · rintro ⟨n, _, hn⟩
    exact Filter.mem_of_superset ((ball_isOpen F v n).mem_nhds (ball F v n).zero_mem) hn

theorem exists_ball_subset (v : HeightOneSpectrum (𝓞 F))
    {U : Set (v.adicCompletion F)} (hU : U ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ k : ℤ, (ball F v k : Set (v.adicCompletion F)) ⊆ U := by
  obtain ⟨n, _, hn⟩ := (ball_basis_nat F v).mem_iff.mp hU
  exact ⟨n, hn⟩

end DedekindZetaZeroFree.PoissonSLocalBalls

end
