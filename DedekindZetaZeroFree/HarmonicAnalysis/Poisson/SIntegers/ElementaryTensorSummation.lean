module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DualBallFibers

@[expose] public section

set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical nonZeroDivisors SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS

attribute [local instance] completionMeasurable completionBorel

def elementaryTensorFunction (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (g : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    Space F S → ℂ :=
  fun x => g x.1 *
    {z : PoissonFinite.Space F S | z - PoissonFinite.diagonal F S (t : F) ∈
      finiteBall F S k}.indicator (fun _ => (1 : ℂ)) x.2

private theorem elementary_eq_tensor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (g : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    elementaryTensorFunction F S g k t = tensorFunction F S g (fun v z =>
      if ‖z - PoissonFinite.diagonal F S (t : F) v‖ ≤
        (v.val.asIdeal.absNorm : ℝ) ^ (-k v) then 1 else 0) := by
  funext x
  unfold elementaryTensorFunction tensorFunction
  change g x.1 * (if x.2 - PoissonFinite.diagonal F S (t : F) ∈ finiteBall F S k
    then (1 : ℂ) else 0) = _
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, forall_const, finiteBall,
    Set.mem_setOf_eq, Pi.sub_apply]

private theorem canonical_conductor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    TraceConductor F S (fun v => localFiniteCharacter F v.val) := by
  intro v y
  let T : Finset (HeightOneSpectrum (RingOfIntegers F)) := {v.val}
  letI : Unique T := ⟨⟨⟨v.val, Finset.mem_singleton_self _⟩⟩,
    fun w => Subtype.ext (Finset.mem_singleton.mp w.property)⟩
  let yy : PoissonFinite.Space F T := fun w =>
    (Finset.mem_singleton.mp w.property).symm ▸ y
  have he := finiteBallAnnihilator_eq F T (fun _ => 0)
  have hy : yy ∈ finiteBallAnnihilator F T (fun _ => 0) ↔
      ‖y‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val := by
    rw [he]
    simp only [finiteBall, Set.mem_setOf_eq]
    rw [Unique.forall_iff]
    simp only [sub_zero, neg_neg]
    change ‖(Finset.mem_singleton.mp (default : T).property).symm ▸ y‖ ≤
      ((default : T).val.asIdeal.absNorm : ℝ) ^ differentExponent F (default : T).val ↔ _
    rfl
  rw [← hy]
  unfold finiteBallAnnihilator
  simp only [Set.mem_setOf_eq, finiteBallTraceCharacter_apply, Fintype.prod_unique,
    Pi.mul_apply, finiteBall, Set.mem_setOf_eq, neg_zero, zpow_zero]
  constructor
  · intro h u hu
    exact h (u default) (hu default)
  · intro h x hx
    let xx : PoissonFinite.Space F T := fun w =>
      (Finset.mem_singleton.mp w.property).symm ▸ x
    exact h xx (by rw [Unique.forall_iff]; exact hx)

theorem summable_norm_elementaryTensorFunction
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (g : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    Summable (fun m : sIntegerRing F S =>
      ‖elementaryTensorFunction F S g k t (diagonalHom F S (m : F))‖) := by
  rw [elementary_eq_tensor]
  have htest (v : S) := ScaleShift.local_ball_test F v.val (k v)
    (PoissonFinite.diagonal F S (t : F) v)
  have hs := summable_norm_tensorFunction_lattice F S g _
    (fun v => (htest v).1) (fun v => (htest v).2) 1 one_ne_zero
  exact (ScaleShift.diagonalLatticeEquiv F S).summable_iff.mpr hs

theorem summable_norm_fourierIntegral_elementaryTensorFunction
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (g : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    Summable (fun h : sIntegerRing F S =>
      ‖fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ
        (elementaryTensorFunction F S g k t) (diagonalHom F S (h : F))‖) := by
  rw [elementary_eq_tensor]
  have htest (v : S) := ScaleShift.local_ball_test F v.val (k v)
    (PoissonFinite.diagonal F S (t : F) v)
  have hs := summable_norm_fourierIntegral_tensorFunction_lattice F S _ μ
    (fun v => continuous_localFiniteCharacter F v.val)
    (ScaleShift.traceConductor_nontrivial F S _ (canonical_conductor F S))
    g _ (fun v => (htest v).1) (fun v => (htest v).2) (1 : F) one_ne_zero
  rw [inv_one] at hs
  exact (ScaleShift.diagonalLatticeEquiv F S).summable_iff.mpr hs

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_diagonal_phase (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (r : sIntegerRing F S) :
    ScaleShift.rawPhase F S (fun v => localFiniteCharacter F v.val)
      (diagonalHom F S (r : F)) (diagonalHom F S 1) = 1 := by
  have h := congrArg (fun z : Circle => (z : ℂ))
    (sLocalTraceCharacter_sIntegerDiagonal_eq_one F S hS r)
  have ha : (∏ v : InfinitePlace F, (archTraceCharacter v
      (algebraMap F v.Completion (r : F)) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F (PoissonArch.minkowskiEmbedding F r)
          (PoissonArch.minkowskiEmbedding F 1) : ℂ)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)]
    let he : {v : InfinitePlace F // ¬v.IsReal} ≃ {v : InfinitePlace F // v.IsComplex} :=
      Equiv.subtypeEquivRight (fun v => InfinitePlace.not_isReal_iff_isComplex)
    rw [← he.symm.prod_comp (fun v : {v : InfinitePlace F // ¬v.IsReal} =>
      (archTraceCharacter v.val (algebraMap F v.val.Completion (r : F)) : ℂ))]
    have hr (v : {v : InfinitePlace F // v.IsReal}) :
        (archTraceCharacter v.val (algebraMap F v.val.Completion (r : F)) : ℂ) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (InfinitePlace.embedding_of_isReal v.property (r : F) : ℂ)) := by
      change (Circle.exp (2 * Real.pi * archTrace v.val
        (algebraMap F v.val.Completion (r : F))) : ℂ) = _
      rw [archTrace_of_isReal _ v.property]
      have hx : algebraMap F v.val.Completion (r : F) =
        ((WithAbs.equiv v.val.1).symm (r : F) : v.val.Completion) := rfl
      rw [hx]
      simp only [Circle.coe_exp, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply]
      congr 1
      push_cast
      ring
    have hc (v : {v : InfinitePlace F // v.IsComplex}) :
        (archTraceCharacter (he.symm v).val
          (algebraMap F (he.symm v).val.Completion (r : F)) : ℂ) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 * (v.val.embedding (r : F)).re : ℂ)) := by
      have hv : (he.symm v).val = v.val := rfl
      change (archTraceCharacter v.val (algebraMap F v.val.Completion (r : F)) : ℂ) = _
      simp [archTraceCharacter_of_isComplex _ v.property, Circle.coe_exp]
      ring_nf
    simp_rw [hr, hc]
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    simp [PoissonArch.tracePairing, PoissonArch.minkowskiEmbedding, mixedEmbedding,
      Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [sLocalTraceCharacter_apply, sIntegerDiagonal_apply,
    sLocalDiagonal_infinite, sLocalDiagonal_finite] at h
  change Circle.coeHom ((∏ v : InfinitePlace F, archTraceCharacter v
      (algebraMap F v.Completion (r : F))) *
    ∏ v : S, localFiniteCharacter F v.val (algebraMap F (v.val.adicCompletion F) (r : F))) = 1 at h
  simp only [map_mul, map_prod, map_one, Circle.coeHom_apply] at h
  rw [ha] at h
  have hf (v : S) : FinitePlace.embedding v.val (r : F) =
      algebraMap F (v.val.adicCompletion F) (r : F) := rfl
  simpa [ScaleShift.rawPhase, diagonalHom, PoissonFinite.diagonal,
    PoissonArch.minkowskiEmbedding, hf] using h

theorem poisson_elementaryTensorFunction
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (g : 𝓢(PoissonArch.Space F, ℂ)) (k : S → ℤ) (t : sIntegerRing F S) :
    (∑' m : sIntegerRing F S,
      elementaryTensorFunction F S g k t (diagonalHom F S (m : F))) =
    ∑' h : sIntegerRing F S,
      fourierIntegral F S (fun v => localFiniteCharacter F v.val) μ
        (elementaryTensorFunction F S g k t) (diagonalHom F S (h : F)) := by
  rw [elementary_eq_tensor]
  have hp := ScaleShift.centered_ball_poisson F S hS _ μ
    (canonical_conductor F S) hnorm (canonical_diagonal_phase F S hS) g k t
  rw [← (ScaleShift.diagonalLatticeEquiv F S).tsum_eq,
    ← (ScaleShift.diagonalLatticeEquiv F S).tsum_eq] at hp
  exact hp

end DedekindZetaZeroFree.PoissonS

end
