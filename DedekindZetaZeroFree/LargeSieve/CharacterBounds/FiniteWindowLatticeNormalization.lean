module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.CompactWindowBalancedDilation
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ReducedExteriorFractionSeparation
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTensorCosets
public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation

@[expose] public section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped Classical FourierTransform nonZeroDivisors

 theorem arch_pairing_complex (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (x y : InfiniteAdeleRing F) :
    PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F x)
      (PoissonArch.infiniteAdeleToSpace F y) =
    ∑ v : InfinitePlace F, 2 *
      (InfinitePlace.Completion.extensionEmbedding v (x v * y v)).re := by
  rw [PoissonArch.tracePairing,
    PoissonArch.infiniteAdeleToSpace_coordinates,
    PoissonArch.infiniteAdeleToSpace_coordinates,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  haveI : IsEmpty {v : InfinitePlace F // v.IsReal} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex v.val)) v.property⟩
  simp only [Finset.sum_empty, Finset.univ_eq_empty, zero_add]
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun v => IsTotallyComplex.isComplex v))
  intro v
  simp only [map_mul]
  rfl

 theorem trace_modulation_of_shifts (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((∑ v : InfinitePlace F, 2 *
        (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
      ∏ v : S, (e v (x.2 v) : ℂ))
    (htrace : ∀ m : sIntegerRing F S, χ (sIntegerDiagonal F S m) = 1)
    (k : (v : S) → ℤ) (r : F → ProbeSeparation.Integers F S)
    (hr : ∀ (a : F) (x : PoissonFinite.Space F S),
      x ∈ PoissonS.finiteBall F S k → ∀ v : S,
      e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) = 1)
    (a : F) (m : ProbeSeparation.Integers F S)
    (hm : (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k) :
    χ (sLocalDiagonal F S ((m : F) * a)) =
      (𝐞 (inner ℝ (PoissonArch.infiniteAdeleToSpace F
        (sLocalDiagonal F S (m : F)).1) (normalizedFrequency F S r a)) : ℂ) := by
  let T : F → ℝ := fun t => ∑ v : InfinitePlace F, 2 *
    (InfinitePlace.Completion.extensionEmbedding v
      (algebraMap F v.Completion t)).re
  let P : F → ℂ := fun t => ∏ v : S,
    (e v (algebraMap F (v.val.adicCompletion F) t) : ℂ)
  let A : F → ℂ := fun t => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (T t : ℂ))
  have hc (t : F) : χ (sLocalDiagonal F S t) = A t * P t := by
    simpa only [A, T, P, sLocalDiagonal_infinite, sLocalDiagonal_finite,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      hχ (sLocalDiagonal F S t)
  have hT (x y : F) : T (x + y) = T x + T y := by
    simp [T, map_add, mul_add, Finset.sum_add_distrib]
  have hA (x y : F) : A (x + y) = A x * A y := by
    simp only [A, hT, Complex.ofReal_add, mul_add, Complex.exp_add]
  have hP (x y : F) : P (x + y) = P x * P y := by
    simp only [P, map_add, AddChar.map_add_eq_mul, Circle.coe_mul,
      Finset.prod_mul_distrib]
  have hPr : P ((m : F) * (a + (r a : F))) = 1 := by
    dsimp [P]
    apply Finset.prod_eq_one
    intro v _
    rw [map_mul]
    simpa only [sLocalDiagonal_finite, Circle.coe_one] using congrArg
      (fun z : Circle => (z : ℂ)) (hr a _ hm v)
  have hmr : A ((m : F) * (r a : F)) * P ((m : F) * (r a : F)) = 1 := by
    exact (hc _).symm.trans (htrace (m * r a))
  have hAr : A ((m : F) * (a + (r a : F))) = A ((m : F) * a) * P ((m : F) * a) := by
    have h := hP ((m : F) * a) ((m : F) * (r a : F))
    rw [← mul_add, hPr] at h
    rw [mul_add, hA]
    have hAr' : A ((m : F) * (r a : F)) = P ((m : F) * a) := by
      calc
        A ((m : F) * (r a : F)) =
            A ((m : F) * (r a : F)) * (P ((m : F) * a) * P ((m : F) * (r a : F))) := by rw [← h, mul_one]
        _ = P ((m : F) * a) * (A ((m : F) * (r a : F)) * P ((m : F) * (r a : F))) := by ring
        _ = P ((m : F) * a) := by rw [hmr, mul_one]
    rw [hAr']
  rw [hc, ← hAr]
  rw [normalizedFrequency, ← PoissonArch.tracePairing_eq_inner, arch_pairing_complex]
  simp only [sLocalDiagonal_infinite, ← map_mul]
  rw [Real.fourierChar_apply]
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (T _ : ℂ)) =
    Complex.exp (((2 * Real.pi * T _) : ℝ) * Complex.I)
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  ring

theorem finite_window_phase_representatives (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (k : S → ℤ) :
    ∃ r : F → ProbeSeparation.Integers F S,
      ∀ a x, x ∈ PoissonS.finiteBall F S k → ∀ v : S,
        e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) = 1 := by
  have hK : IsCompact (PoissonS.finiteBall F S k) := by
    have heq : PoissonS.finiteBall F S k =
        Set.pi Set.univ (fun v : S => (PoissonSLocalBalls.ball F v.val (k v) : Set _)) := by
      ext x
      simp [PoissonS.finiteBall, PoissonSLocalBalls.ball_eq_normBall]
    rw [heq]
    exact isCompact_univ_pi fun v => PoissonSLocalBalls.ball_isCompact F v.val (k v)
  obtain ⟨U, hU, hp⟩ := PoissonFinite.BallExpansion.exists_open_phase_annihilator F S e he _ hK
  have hr (a : F) : ∃ r : ProbeSeparation.Integers F S,
      (fun v : S => algebraMap F (v.val.adicCompletion F) (a + (r : F))) ∈ U := by
    let A : PoissonFinite.Space F S := fun v => algebraMap F (v.val.adicCompletion F) a
    obtain ⟨r, hr⟩ := (PoissonSFiniteDensity.diagonal_denseRange F S).exists_mem_open
      (hU.preimage (continuous_id.add continuous_const))
      (show Set.Nonempty ((fun x : PoissonFinite.Space F S => x + A) ⁻¹' (U : Set _)) from
        ⟨-A, by simp [U.zero_mem]⟩)
    refine ⟨r, ?_⟩
    have heq : (fun v : S => algebraMap F (v.val.adicCompletion F) (a + (r : F))) =
        PoissonSFiniteDensity.diagonal F S r + A := by
      funext v
      simp only [Pi.add_apply, PoissonSFiniteDensity.diagonal_apply, A, map_add, add_comm]
    rw [heq]
    exact hr
  choose r hr using hr
  refine ⟨r, ?_⟩
  intro a x hx v
  let y : PoissonFinite.Space F S := Pi.single v (-x v)
  have hy : y ∈ PoissonS.finiteBall F S k := by
    intro w
    by_cases hw : w = v
    · subst w
      simpa [y] using hx v
    · simp [y, Pi.single_eq_of_ne hw]
      positivity
  have h := hp _ (hr a) y hy
  have hh : (e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) : ℂ) = 1 := by
    rw [Finset.prod_eq_single v] at h
    · simpa only [y, Pi.single_eq_same, neg_neg] using h
    · intro w _ hw
      simp [y, Pi.single_eq_of_ne hw]
    · simp
  exact Circle.coe_injective (by simpa using hh)

theorem finite_window_lattice_equiv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) :
    ∃ E : {m : ProbeSeparation.Integers F S //
      (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k} ≃
      PoissonS.ballArchLattice F S k,
      ∀ m, (E m : PoissonArch.Space F) =
        PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m.val : F)).1 := by
  have hcoord (a : F) :
      PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S a).1 =
      PoissonArch.minkowskiEmbedding F a := by
    apply (mixedEmbedding.euclidean.toMixed F).injective
    rw [PoissonArch.infiniteAdeleToSpace_coordinates]
    simp [PoissonArch.minkowskiEmbedding, sLocalDiagonal_infinite, mixedEmbedding]
    exact ⟨rfl, rfl⟩
  have hmem (m : ProbeSeparation.Integers F S) :
      (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k ↔
        (m : F) ∈ PoissonS.ballFractionalIdeal F S k :=
    PoissonS.ScaleShift.finiteBall_diagonal_mem F S k m
  let I : PoissonArch.NonzeroFractionalIdeal F :=
    Units.mk0 (PoissonS.ballFractionalIdeal F S k) (PoissonS.ballFractionalIdeal_ne_zero F S k)
  have hlat : PoissonS.ballArchLattice F S k = PoissonArch.idealLattice F I :=
    PoissonS.ballArchLattice_eq F S k
  let f : {m : ProbeSeparation.Integers F S //
      (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k} →
      PoissonS.ballArchLattice F S k := fun m =>
    ⟨PoissonArch.minkowskiEmbedding F (m.val : F), by
      rw [hlat, PoissonArch.mem_idealLattice]
      exact ⟨m.val, (hmem m.val).mp m.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      apply Subtype.ext
      apply Subtype.ext
      apply mixedEmbedding_injective F
      have h' := congrArg (fun y : PoissonS.ballArchLattice F S k =>
        mixedEmbedding.euclidean.toMixed F (y : PoissonArch.Space F)) h
      simpa [f, PoissonArch.minkowskiEmbedding] using h'
    · intro y
      have hy : (y : PoissonArch.Space F) ∈ PoissonArch.idealLattice F I := by
        rw [← hlat]
        exact y.property
      obtain ⟨a, ha, he⟩ := (PoissonArch.mem_idealLattice F I _).mp hy
      let m : ProbeSeparation.Integers F S :=
        ⟨a, PoissonS.ScaleShift.ballFractionalIdeal_le_sIntegers F S k ha⟩
      exact ⟨⟨m, (hmem m).mpr ha⟩, Subtype.ext he⟩
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro m
  exact (hcoord _).symm

theorem finite_window_lattice_normalization
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ))
    (htrace : ∀ m : sIntegerRing F S, χ (sIntegerDiagonal F S m) = 1)
    (k : (v : S) → ℤ) (hk : ∀ v, k v ≤ 0) :
    ∃ hd : DiscreteTopology (PoissonS.ballArchLattice F S k),
    letI := hd;
    IsZLattice ℝ (PoissonS.ballArchLattice F S k) ∧
    ∃ r : F → ProbeSeparation.Integers F S,
      (∀ (a : F) (x : PoissonFinite.Space F S),
        x ∈ PoissonS.finiteBall F S k → ∀ v : S,
          e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) = 1) ∧
      (∀ (a : F) (m : ProbeSeparation.Integers F S),
        (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k →
        χ (sLocalDiagonal F S ((m : F) * a)) =
          (𝐞 (inner ℝ
            (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (m : F)).1)
            (normalizedFrequency F S r a)) : ℂ)) ∧
      (∃ E : {m : ProbeSeparation.Integers F S //
          (sLocalDiagonal F S (m : F)).2 ∈ PoissonS.finiteBall F S k} ≃
          PoissonS.ballArchLattice F S k,
        ∀ m, (E m : PoissonArch.Space F) =
          PoissonArch.infiniteAdeleToSpace F
            (sLocalDiagonal F S (m.val : F)).1) := by
  letI : IsTotallyComplex F := primitive12_totallyComplex F ζ12 hζ12
  have hlat : ∃ hd : DiscreteTopology (PoissonS.ballArchLattice F S k),
      letI := hd; IsZLattice ℝ (PoissonS.ballArchLattice F S k) := by
    rw [PoissonS.ballArchLattice_eq]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨hd, hL⟩ := hlat
  refine ⟨hd, ?_⟩
  letI := hd
  refine ⟨hL, ?_⟩
  obtain ⟨r, hr⟩ := finite_window_phase_representatives F S e he k
  refine ⟨r, hr, ?_, finite_window_lattice_equiv F S k⟩
  intro a m hm
  exact trace_modulation_of_shifts F S e χ hχ htrace k r hr a m hm

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
