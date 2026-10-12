module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.ElementaryTensorSummation
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.FinitePlaces.UniformBallPartitions

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS

local instance baseCompletionMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance baseCompletionBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private lemma indicator_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    (A : ∀ i, Set (α i)) (z : ∀ i, α i) :
    (Set.pi Set.univ A).indicator (fun _ => (1 : ℂ)) z =
      ∏ i, (A i).indicator (fun _ => (1 : ℂ)) (z i) := by
  by_cases h : ∀ i, z i ∈ A i
  · rw [Set.indicator_of_mem (by simpa [Set.mem_pi] using h), Finset.prod_eq_one]
    intro i _
    exact Set.indicator_of_mem (h i) _
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [Set.indicator_of_notMem (by simpa [Set.mem_pi] using h)]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

private lemma ball_eq_finiteCompletionBall (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (k : ℤ) :
    PoissonSLocalBalls.ball F v k = finiteCompletionBall F v k := by
  ext x
  simp

private lemma localCosetIndicator_ball_eq (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (c : v.adicCompletion F) (k : ℤ) :
    localCosetIndicator F v c (PoissonSLocalBalls.ball F v k) =
      localCosetIndicator F v c (finiteCompletionBall F v k) := by
  unfold localCosetIndicator
  rw [ball_eq_finiteCompletionBall F v k]

private lemma elementaryTensorFunction_eq_tensor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (fArch : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    elementaryTensorFunction F S fArch k t =
      tensorFunction F S fArch (fun v : S =>
        localCosetIndicator F v.val (FinitePlace.embedding v.val (t : F))
          (finiteCompletionBall F v.val (k v))) := by
  funext x
  unfold elementaryTensorFunction tensorFunction
  congr 1
  rw [show ({z : PoissonFinite.Space F S |
        z - PoissonFinite.diagonal F S (t : F) ∈ finiteBall F S k}) =
      Set.pi Set.univ (fun v : S => {z : v.val.adicCompletion F |
        z - FinitePlace.embedding v.val (t : F) ∈
          PoissonSLocalBalls.ball F v.val (k v)}) from ?_]
  · rw [indicator_pi]
    apply Finset.prod_congr rfl
    intro v _
    change localCosetIndicator F v.val (FinitePlace.embedding v.val (t : F))
      (PoissonSLocalBalls.ball F v.val (k v)) (x.2 v) = _
    rw [localCosetIndicator_ball_eq F v.val (FinitePlace.embedding v.val (t : F)) (k v)]
  · ext z
    rw [PoissonSUniformBallPartition.finiteBall_eq_valuation_product]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.sub_apply,
      PoissonFinite.diagonal]

private lemma elementaryTensorFunction_integrable (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (fArch : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    Integrable (elementaryTensorFunction F S fArch k t) (productMeasure F S μ) := by
  rw [elementaryTensorFunction_eq_tensor F S fArch k t]
  refine tensorFunction_integrable F S μ fArch _ (fun v => ?_) (fun v => ?_)
  · exact ((mem_localSchwartz F v.val _).mp
      (localCosetIndicator_ball_mem_localSchwartz F v.val
        (FinitePlace.embedding v.val (t : F)) (k v))).1
  · exact ((mem_localSchwartz F v.val _).mp
      (localCosetIndicator_ball_mem_localSchwartz F v.val
        (FinitePlace.embedding v.val (t : F)) (k v))).2

private lemma base_kernel_integrable
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    (f : Space F S → ℂ) (hf : Integrable f (productMeasure F S μ))
    (y : Space F S) :
    Integrable (fun x => f x *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
      ∏ v : S, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ))
      (productMeasure F S μ) := by
  have hc : Continuous (fun x : Space F S =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
      ∏ v : S, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)) := by
    apply Continuous.mul
    · unfold PoissonArch.tracePairing
      fun_prop
    · apply continuous_finset_prod
      intro v hv
      exact continuous_subtype_val.comp ((continuous_localFiniteCharacter F v.val).comp
        ((continuous_apply v).comp continuous_snd |>.neg.mul continuous_const))
  have hn (x : Space F S) :
      ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : S, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)‖ = 1 := by
    rw [norm_mul]
    rw [show (-2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ) =
        ((-2 * Real.pi * PoissonArch.tracePairing F x.1 y.1 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
    exact Finset.prod_eq_one fun v _ => Circle.norm_coe _
  simpa only [mul_assoc] using hf.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (hn x).le))

theorem poisson_sum_tensorFunction
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (hS : ContainsDifferent F S)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (hnorm : LocalNormalization F S μ)
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    let f := tensorFunction F S fArch φ
    let fHat := fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ f
    Summable (fun m : sIntegerRing F S => ‖f (diagonalHom F S (m : F))‖) ∧
      Summable (fun h : sIntegerRing F S => ‖fHat (diagonalHom F S (h : F))‖) ∧
      (∑' m : sIntegerRing F S, f (diagonalHom F S (m : F))) =
        ∑' h : sIntegerRing F S, fHat (diagonalHom F S (h : F)) := by
  dsimp only
  obtain ⟨k, n, t, c, _, hpartition, _⟩ :=
    PoissonSUniformBallPartition.exists_uniform_ball_partition F S φ hlocal hsupport
  let G : Fin n → Space F S → ℂ := fun j => elementaryTensorFunction F S fArch k (t j)
  let H : Fin n → Space F S → ℂ := fun j =>
    fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ (G j)
  have hf (x : Space F S) : tensorFunction F S fArch φ x =
      ∑ j : Fin n, c j * G j x := by
    unfold tensorFunction
    rw [hpartition x.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [G, elementaryTensorFunction, PoissonSUniformBallPartition.coset]
    ring
  have hhat (y : Space F S) :
      fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ
        (tensorFunction F S fArch φ) y = ∑ j : Fin n, c j * H j y := by
    unfold fourierIntegral
    simp_rw [hf, Finset.sum_mul]
    have hi (j : Fin n) : Integrable (fun x : Space F S => c j * G j x *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : S, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ))
        (productMeasure F S μ) := by
      simpa only [mul_assoc] using
        (base_kernel_integrable F S μ (G j)
          (elementaryTensorFunction_integrable F S μ fArch k (t j)) y).const_mul (c j)
    rw [integral_finset_sum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mul_assoc, integral_const_mul]
    simp only [H, fourierIntegral, mul_assoc]
  have hg (j : Fin n) : Summable (fun m : sIntegerRing F S =>
      c j * G j (diagonalHom F S (m : F))) :=
    (summable_norm_elementaryTensorFunction F S hS fArch k (t j)).of_norm.mul_left (c j)
  have hh (j : Fin n) : Summable (fun m : sIntegerRing F S =>
      c j * H j (diagonalHom F S (m : F))) :=
    (summable_norm_fourierIntegral_elementaryTensorFunction F S hS μ hnorm
      fArch k (t j)).of_norm.mul_left (c j)
  have hgf : Summable (fun m : sIntegerRing F S =>
      tensorFunction F S fArch φ (diagonalHom F S (m : F))) := by
    simp_rw [hf]
    exact summable_sum (fun j _ => hg j)
  have hhf : Summable (fun m : sIntegerRing F S =>
      fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ
        (tensorFunction F S fArch φ) (diagonalHom F S (m : F))) := by
    simp_rw [hhat]
    exact summable_sum (fun j _ => hh j)
  refine ⟨hgf.norm, hhf.norm, ?_⟩
  simp_rw [hf, hhat]
  rw [Summable.tsum_finsetSum (fun j _ => hg j),
    Summable.tsum_finsetSum (fun j _ => hh j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_mul_left, tsum_mul_left]
  congr 1
  exact poisson_elementaryTensorFunction F S hS μ hnorm fArch k (t j)

end DedekindZetaZeroFree.PoissonS

end
