module

public import DedekindZetaZeroFree.Adeles.Approximation.FiniteAdeleDensity
public import DedekindZetaZeroFree.Moments.Probes.PrincipalProbeAndSeparatedMellinSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.NormalizedProbe.PrincipalData

theorem finiteSf_Sinteger_diagonal_denseRange {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) :
    DenseRange (fun r : A.R => fun v : ↥A.Sf =>
      algebraMap F (v.val.adicCompletion F) (r : F)) := by
  exact PoissonSFiniteDensity.diagonal_denseRange F A.Sf

private theorem archPhase_eq_trace {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (x : InfiniteAdeleRing F) :
    ProbeAdditive.archPhase F x = ∏ w, (archTraceCharacter w (x w) : ℂ) := by
  simp only [archTraceCharacter_of_isComplex _ (A.complex_place _), Circle.coe_exp,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  rw [ProbeAdditive.archPhase, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro w hw
  ring

set_option backward.isDefEq.respectTransparency false in

theorem finiteTrace_eq_localTraceCharacter {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (ι : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A ι η hS) (v : ↥A.Sf) :
    P.finiteTrace v = ResidueTrace.localTraceCharacter v.val := by
  let f (y : (w : ↥A.Sf) → w.val.adicCompletion F) : ℂ :=
    ∏ w, (P.finiteTrace w (y w) : ℂ)
  let g (y : (w : ↥A.Sf) → w.val.adicCompletion F) : ℂ :=
    ∏ w, (ResidueTrace.localTraceCharacter w.val (y w) : ℂ)
  have hf : Continuous f := by
    apply continuous_finset_prod
    intro w hw
    exact continuous_subtype_val.comp ((P.continuousTrace w).comp (continuous_apply w))
  have hg : Continuous g := by
    apply continuous_finset_prod
    intro w hw
    exact continuous_subtype_val.comp
      ((ResidueTrace.continuous_localTraceCharacter w.val).comp (continuous_apply w))
  have heq : f = g := (finiteSf_Sinteger_diagonal_denseRange A).equalizer hf hg (by
    funext r
    have hp := P.traceCompatible r
    have hc := congrArg (fun z : Circle => (z : ℂ)) (A.eS_integer hS r)
    simp only [ProbeAdditive.TraceCompatible, ProbeAdditive.phase,
      sIntegerDiagonal_apply] at hp
    change ProbeAdditive.archPhase F (sLocalDiagonal F A.Sf (r : F)).1 *
      f (fun w => algebraMap F (w.val.adicCompletion F) (r : F)) = 1 at hp
    change (A.eS (sLocalDiagonal F A.Sf (r : F)) : ℂ) = (1 : ℂ) at hc
    change (((∏ w : InfinitePlace F, archTraceCharacter w (algebraMap F w.Completion (r : F))) *
      (∏ w : ↥A.Sf, ResidueTrace.localTraceCharacter w.val
        (algebraMap F (w.val.adicCompletion F) (r : F))) : Circle) : ℂ) = 1 at hc
    simp only [Circle.coe_mul] at hc
    change Circle.coeHom (∏ w : InfinitePlace F,
        archTraceCharacter w (algebraMap F w.Completion (r : F))) *
      Circle.coeHom (∏ w : ↥A.Sf, ResidueTrace.localTraceCharacter w.val
        (algebraMap F (w.val.adicCompletion F) (r : F))) = 1 at hc
    rw [map_prod, map_prod] at hc
    change (∏ w : InfinitePlace F, (archTraceCharacter w
      (algebraMap F w.Completion (r : F)) : ℂ)) *
      g (fun w => algebraMap F (w.val.adicCompletion F) (r : F)) = 1 at hc
    rw [← archPhase_eq_trace A] at hc
    have hn : ProbeAdditive.archPhase F (sLocalDiagonal F A.Sf (r : F)).1 ≠ 0 :=
      Complex.exp_ne_zero _
    exact mul_left_cancel₀ hn (hp.trans hc.symm))
  ext x
  let y : (w : ↥A.Sf) → w.val.adicCompletion F := Pi.single v x
  have h := congr_fun heq y
  have prod_single (e : (w : ↥A.Sf) → AddChar (w.val.adicCompletion F) Circle) :
      (∏ w : ↥A.Sf, (e w (y w) : ℂ)) = (e v x : ℂ) := by
    rw [Finset.prod_eq_single v]
    · simp [y]
    · intro w hw hwv
      simp [y, Pi.single_eq_of_ne hwv]
    · simp
  change (∏ w : ↥A.Sf, (P.finiteTrace w (y w) : ℂ)) =
    (∏ w : ↥A.Sf, (ResidueTrace.localTraceCharacter w.val (y w) : ℂ)) at h
  rw [prod_single, prod_single] at h
  exact h

theorem finiteTrace_ne_one {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (ι : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A ι η hS) (v : ↥A.Sf) :
    ∃ x : v.val.adicCompletion F, P.finiteTrace v x ≠ 1 := by
  rw [finiteTrace_eq_localTraceCharacter A ι η hS P v]
  letI := (ResidueTrace.baseEmbedding v.val).toAlgebra
  letI := ResidueTrace.localTrace_finite v.val
  obtain ⟨x, hx⟩ := Algebra.trace_surjective ℚ_[ResidueTrace.rationalPrimeBelow v.val]
    (v.val.adicCompletion F)
    (((ResidueTrace.rationalPrimeBelow v.val).1 : ℚ)⁻¹ :
      ℚ_[ResidueTrace.rationalPrimeBelow v.val])
  refine ⟨x, ?_⟩
  change rationalPadicCharacter (ResidueTrace.rationalPrimeBelow v.val)
    (Algebra.trace ℚ_[ResidueTrace.rationalPrimeBelow v.val]
      (v.val.adicCompletion F) x) ≠ 1
  rw [hx]
  exact rationalPadicCharacter_inv_prime_ne_one _

end DedekindZetaZeroFree.NormalizedProbe.PrincipalData

end
