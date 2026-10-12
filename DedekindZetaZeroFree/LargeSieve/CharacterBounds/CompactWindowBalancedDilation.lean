module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.BallVolumesAndCovolumes
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters
public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerLocalProduct

@[expose] public section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical

def normalizedFrequency (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : F → sIntegerRing F S) (a : F) : PoissonArch.Space F :=
  PoissonArch.traceAdapter F
    (PoissonArch.infiniteAdeleToSpace F
      (sLocalDiagonal F S (a + (r a : F))).1)

theorem compact_window_balanced_dilation
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ell : ℝ → SLocalProduct F S)
    (hell : ∀ N, ell N =
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (N ^ (1 / (Module.finrank ℚ F : ℝ)) •
          (1 : mixedEmbedding.mixedSpace F)), 1))
    (K : Set (SLocalProduct F S)) (hK : IsCompact K) :
    ∃ (k : (v : S) → ℤ) (R : ℝ),
      (∀ v, k v ≤ 0) ∧ 0 < R ∧
      Continuous ((PoissonS.finiteBall F S k).indicator (fun _ => (1 : ℝ))) ∧
      (∀ x ∈ K, x.2 ∈ PoissonS.finiteBall F S k ∧
        ‖PoissonArch.infiniteAdeleToSpace F x.1‖ ≤ R) ∧
      (∀ (N : ℝ) (x : SLocalProduct F S), 1 ≤ N →
        (ell N * x).2 = x.2 ∧
        PoissonArch.infiniteAdeleToSpace F (ell N * x).1 =
          N ^ (1 / (Module.finrank ℚ F : ℝ)) •
            PoissonArch.infiniteAdeleToSpace F x.1) := by
  have hb (v : S) : ∃ n : ℕ, ∀ x ∈ K,
      ‖x.2 v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ n := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun x : SLocalProduct F S => x.2 v) (by fun_prop)
    have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    obtain ⟨n, hn⟩ := exists_nat_pow_near (le_max_right C 1) hq
    exact ⟨n + 1, fun x hx => (hC x hx).trans
      ((le_max_left C 1).trans hn.2.le)⟩
  choose n hn using hb
  let k : (v : S) → ℤ := fun v => -(n v : ℤ)
  have hcl : IsClopen (PoissonS.finiteBall F S k) := by
    have heq : PoissonS.finiteBall F S k =
        ⋂ v : S, (fun x : PoissonFinite.Space F S => x v) ⁻¹'
          Metric.closedBall 0 ((v.val.asIdeal.absNorm : ℝ) ^ (-k v)) := by
      ext x
      simp [PoissonS.finiteBall, Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    constructor
    · exact isClosed_iInter fun v => Metric.isClosed_closedBall.preimage (continuous_apply v)
    · apply isOpen_iInter_of_finite
      intro v
      apply IsOpen.preimage (continuous_apply v)
      apply IsUltrametricDist.isOpen_closedBall
      have hq : (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
        exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))
      exact (zpow_pos hq _).ne'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : SLocalProduct F S => PoissonArch.infiniteAdeleToSpace F x.1)
    (by fun_prop)
  refine ⟨k, max C 0 + 1, ?_, by positivity,
    hcl.continuous_indicator continuous_const, ?_, ?_⟩
  · intro v
    exact neg_nonpos.mpr (Int.natCast_nonneg _)
  · intro x hx
    constructor
    · intro v
      simpa [k] using hn v x hx
    · exact (hC x hx).trans (by linarith [le_max_left C 0])
  · intro N x hN
    rw [hell N]
    constructor
    · exact one_mul x.2
    · apply (mixedEmbedding.euclidean.toMixed F).injective
      rw [PoissonArch.infiniteAdeleToSpace_coordinates,
        (mixedEmbedding.euclidean.toMixed F).map_smul,
        PoissonArch.infiniteAdeleToSpace_coordinates]
      change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (N ^ (1 / (Module.finrank ℚ F : ℝ)) • 1) * x.1) = _
      rw [map_mul, RingEquiv.apply_symm_apply, smul_mul_assoc, one_mul]

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
