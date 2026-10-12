module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DualBallFibers
public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceClassification

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree

section Helpers

open scoped Classical NumberField nonZeroDivisors Topology

set_option backward.isDefEq.respectTransparency false

private theorem sAnnihilator_arch_pairing (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : InfiniteAdeleRing F) :
    sLocalTraceCharacter F S ((x * y, 0) : SLocalProduct F S) =
      Circle.exp (2 * Real.pi * KPArchTrace.infiniteTracePairing F x y) := by
  have hp : KPArchTrace.infiniteTracePairing F x y =
      ∑ w : InfinitePlace F, archTrace w (x w * y w) := by
    unfold KPArchTrace.infiniteTracePairing KPArchTrace.infiniteToSpace
    rw [PoissonArch.tracePairing]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x,
      InfiniteAdeleRing.ringEquiv_mixedSpace_apply F y]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)
      (fun w => archTrace w (x w * y w))]
    congr 1
    · apply Finset.sum_congr rfl
      intro v _
      simp only [archTrace_of_isReal v.1 v.2, map_mul]
      rfl
    · rw [← Fintype.sum_equiv
        (Equiv.subtypeEquivRight (fun v => (InfinitePlace.not_isReal_iff_isComplex).symm))
        (fun v : {v : InfinitePlace F // v.IsComplex} => archTrace v.1 (x v.1 * y v.1))
        (fun v : {v : InfinitePlace F // ¬ v.IsReal} => archTrace v.1 (x v.1 * y v.1))
        (fun _ => rfl)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [archTrace_of_isComplex v.1 v.2, map_mul]
      rfl
  have hprod : ∀ (s : Finset (InfinitePlace F)) (f : InfinitePlace F → ℝ),
      Circle.exp (∑ w ∈ s, f w) = ∏ w ∈ s, Circle.exp (f w) := by
    intro s
    induction s using Finset.induction with
    | empty => intro f; simp
    | insert a s ha ih =>
        intro f
        rw [Finset.sum_insert ha, Finset.prod_insert ha, Circle.exp_add, ih]
  rw [hp, sLocalTraceCharacter_apply, Finset.mul_sum, hprod]
  have hf : (∏ v : S, localFiniteCharacter F v.val ((0 : PoissonSFiniteDensity.Space F S) v)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    exact (localFiniteCharacter F v.val).map_zero_eq_one
  rw [hf, mul_one]
  apply Finset.prod_congr rfl
  intro v _
  rfl

private theorem sAnnihilator_arch_rational (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : PoissonS.ContainsDifferent F S)
    (y : SLocalProduct F S)
    (hy : ∀ m : sIntegerRing F S,
      sLocalTraceCharacter F S (y * sIntegerDiagonal F S m) = 1) :
    ∃ n : sIntegerRing F S,
      y.1 = (sIntegerDiagonal F S n).1 := by
  have hb : ∀ v : S, ∃ k : ℤ, ∀ a ∈ PoissonSLocalBalls.ball F v.val k,
      localFiniteCharacter F v.val (y.2 v * a) = 1 := by
    intro v
    have hl := (isLocallyConstant_localFiniteCharacter F v.val).comp_continuous
      (continuous_const.mul continuous_id : Continuous (fun a : v.val.adicCompletion F => y.2 v * a))
    have hn : {a : v.val.adicCompletion F | localFiniteCharacter F v.val (y.2 v * a) = 1} ∈
        nhds (0 : v.val.adicCompletion F) :=
      (hl.isOpen_fiber 1).mem_nhds (by simp)
    obtain ⟨k, hk⟩ := PoissonSLocalBalls.exists_ball_subset F v.val hn
    exact ⟨k, fun a ha => hk ha⟩
  choose k hk using hb
  let I := PoissonS.ballFractionalIdeal F S k
  let χ : AddChar (InfiniteAdeleRing F) Circle :=
    (sLocalTraceCharacter F S).compAddMonoidHom
      { toFun := fun x => (y.1 * x, 0)
        map_zero' := by simp
        map_add' := by intros; simp [mul_add] }
  have hc : Continuous χ := (continuous_sLocalTraceCharacter F S).comp
    ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hχ : ∀ x, χ x = Circle.exp
      (2 * Real.pi * KPArchTrace.infiniteTracePairing F x y.1) := by
    intro x
    change sLocalTraceCharacter F S (y.1 * x, 0) = _
    rw [mul_comm]
    exact sAnnihilator_arch_pairing F S x y.1
  have hIχ : ∀ a : F, a ∈ I → χ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    have haR := PoissonS.ScaleShift.ballFractionalIdeal_le_sIntegers F S k ha
    let m : sIntegerRing F S := ⟨a, haR⟩
    have hm : PoissonFinite.diagonal F S a ∈ PoissonS.finiteBall F S k :=
      (PoissonS.ScaleShift.finiteBall_diagonal_mem F S k m).mpr ha
    have hf : sLocalTraceCharacter F S
        ((0, y.2 * (sIntegerDiagonal F S m).2) : SLocalProduct F S) = 1 := by
      rw [sLocalTraceCharacter_apply]
      have hz : (∏ v : InfinitePlace F, archTraceCharacter v ((0 : InfiniteAdeleRing F) v)) = 1 := by
        apply Finset.prod_eq_one
        intro v _
        change archTraceCharacter v 0 = 1
        simp
      rw [hz, one_mul]
      apply Finset.prod_eq_one
      intro v _
      apply hk v
      change ((sIntegerDiagonal F S m).2 v) ∈
        (PoissonSLocalBalls.ball F v.val (k v) : Set (v.val.adicCompletion F))
      rw [PoissonSLocalBalls.ball_eq_normBall]
      exact hm v
    have hh := hy m
    have hd : y * sIntegerDiagonal F S m =
        (y.1 * (sIntegerDiagonal F S m).1, 0) +
          (0, y.2 * (sIntegerDiagonal F S m).2) := by
      apply Prod.ext <;> simp
    rw [hd, AddChar.map_add_eq_mul, hf, mul_one] at hh
    exact hh
  obtain ⟨n, hn, he⟩ := KPArchTrace.infinite_character_parameter_mem_inverseDifferent F I
    (PoissonS.ballFractionalIdeal_ne_zero F S k) χ hc y.1 hχ hIχ
  have hn' : n ∈ PoissonS.dualBallFractionalIdeal F S k := by
    simpa only [SetLike.mem_coe, PoissonS.dualBallFractionalIdeal, KPArchTrace.inverseDifferent,
      PoissonArch.codifferentIdeal_eq_inv_different, I] using hn
  refine ⟨⟨n, PoissonS.dualBallFractionalIdeal_subset_sIntegerRing F S hS k hn'⟩, ?_⟩
  exact he.symm

end Helpers

attribute [-instance] IsAffineAddMonoid.toIsAddTorsionFree

theorem sInteger_trace_annihilator (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (hS : ∀ v : HeightOneSpectrum (RingOfIntegers F),
      differentIdeal ℤ (RingOfIntegers F) ≤ v.asIdeal → v ∈ S)
    (y : SLocalProduct F S) :
    (∀ m : sIntegerRing F S,
      sLocalTraceCharacter F S (y * sIntegerDiagonal F S m) = 1) ↔
      ∃ n : sIntegerRing F S, y = sIntegerDiagonal F S n := by
  classical
  have hS' : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (RingOfIntegers F))) :=
    fun v hv => hS v ((Ideal.dvd_iff_le).mp hv)
  constructor
  · intro h
    obtain ⟨n, hn⟩ := sAnnihilator_arch_rational F S hS' y h
    let z := y - sIntegerDiagonal F S n
    have hz : z.1 = 0 := by dsimp [z]; rw [hn, sub_self]
    have hdiag : ∀ m : sIntegerRing F S,
        sLocalTraceCharacter F S (z * sIntegerDiagonal F S m) = 1 := by
      intro m
      dsimp [z]
      rw [sub_mul, AddChar.map_sub_eq_div, h,
        sLocalTraceCharacter_sIntegerDiagonal_mul_eq_one F S hS' n m, div_self']
    have hf : ∀ a : PoissonSFiniteDensity.Space F S,
        sLocalTraceCharacter F S (0, z.2 * a) = 1 := by
      have heq : (fun a : PoissonSFiniteDensity.Space F S =>
          sLocalTraceCharacter F S (0, z.2 * a)) = (fun _ => 1) := by
        apply (PoissonSFiniteDensity.diagonal_denseRange F S).equalizer
          ((continuous_sLocalTraceCharacter F S).comp
            (continuous_const.prodMk (continuous_const.mul continuous_id))) continuous_const
        funext m
        have hh := hdiag m
        change sLocalTraceCharacter F S (z.1 * _, z.2 * _) = 1 at hh
        change sLocalTraceCharacter F S (0, z.2 * (sIntegerDiagonal F S m).2) = 1
        simpa only [hz, zero_mul] using hh
      exact congrFun heq
    have hzf : z.2 = 0 := by
      funext v
      apply (localFiniteCharacter_nondegenerate F v.val (z.2 v)).mp
      intro a
      have hh := hf (Pi.single v a)
      rw [sLocalTraceCharacter_apply] at hh
      have hzprod : (∏ w : InfinitePlace F, archTraceCharacter w ((0 : InfiniteAdeleRing F) w)) = 1 := by
        apply Finset.prod_eq_one
        intro w _
        change archTraceCharacter w 0 = 1
        simp
      rw [hzprod, one_mul] at hh
      have hsingle : z.2 * Pi.single v a = Pi.single v (z.2 v * a) :=
        (Pi.single_mul_right (i := v) (f := z.2) a).symm
      rw [hsingle] at hh
      have hp : (∏ w : S, localFiniteCharacter F w.val ((Pi.single v (z.2 v * a) : PoissonSFiniteDensity.Space F S) w)) =
          localFiniteCharacter F v.val (z.2 v * a) := by
        rw [Finset.prod_eq_single v]
        · rw [Pi.single_eq_same]
        · intro w _ hw
          rw [Pi.single_eq_of_ne hw]
          exact (localFiniteCharacter F w.val).map_zero_eq_one
        · simp
      rw [hp] at hh
      exact hh
    refine ⟨n, sub_eq_zero.mp ?_⟩
    exact Prod.ext hz hzf
  · rintro ⟨n, rfl⟩ m
    exact sLocalTraceCharacter_sIntegerDiagonal_mul_eq_one F S hS' n m

end DedekindZetaZeroFree

end
