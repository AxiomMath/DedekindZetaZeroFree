module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveRowBoxesAndSchurBounds
public import DedekindZetaZeroFree.Arithmetic.LocalFields.RootsOfUnityAndPowerClasses

@[expose] public section

namespace DedekindZetaZeroFree.TateSLocalComparison
noncomputable section
open scoped Classical NumberField BigOperators
open NumberField IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

private theorem archPhase_eq_archTraceCharacter_product (A : SArithmeticData F)
    (x : InfiniteAdeleRing F) :
    ProbeAdditive.archPhase F x = ∏ w, (archTraceCharacter w (x w) : ℂ) := by
  simp only [archTraceCharacter_of_isComplex _ (A.complex_place _), Circle.coe_exp,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  rw [ProbeAdditive.archPhase, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro w hw
  ring

private theorem archPhase_diagonal (A : SArithmeticData F) (t : F) :
    ProbeAdditive.archPhase F (sLocalDiagonal F A.Sf t).1 =
      ∏ w : InfinitePlace F, (archTraceCharacter w (algebraMap F w.Completion t) : ℂ) := by
  rw [archPhase_eq_archTraceCharacter_product F A]
  apply Finset.prod_congr rfl
  intro w hw
  rw [sLocalDiagonal_infinite]

private theorem sLocalTraceCharacter_sIntegerDiagonal_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 F))) (t : sIntegerRing F S) :
    sLocalTraceCharacter F S (sIntegerDiagonal F S t) = 1 := by

  have hfinite : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) = 1 :=
    fun v hv =>
      localFiniteCharacter_eq_one_of_mem_integers F v _
        ((mem_sIntegerRing_iff F S (t : F)).1 t.2 v hv)

  have hsub : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)))
      ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) :=
    Function.mulSupport_subset_iff'.2 fun v hv => hfinite v hv
  have hfin :
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F))) =
      ∏ v ∈ S, localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) :=
    finprod_eq_prod_of_mulSupport_subset _ hsub
  have hcoe :
      (∏ v : S, localFiniteCharacter F v.1 (algebraMap F (v.1.adicCompletion F) (t : F))) =
      ∏ v ∈ S, localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) :=
    (Finset.prod_subtype S (fun _ => Iff.rfl)
      (fun w => localFiniteCharacter F w (algebraMap F (w.adicCompletion F) (t : F)))).symm
  have hdiag := traceCharacter_diagonal_product_formula F (t : F)
  rw [sLocalTraceCharacter_apply]
  simp only [sIntegerDiagonal_apply, sLocalDiagonal_infinite, sLocalDiagonal_finite]
  rw [hcoe, ← hfin]
  exact hdiag

theorem compatible_phase_eq_trace (A : SArithmeticData F)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (htrace : ProbeAdditive.TraceCompatible F A.Sf e) :
    ∀ x, ProbeAdditive.phase F A.Sf e x = (sLocalTraceCharacter F A.Sf x : ℂ) := by
  let f (y : (w : ↥A.Sf) → w.val.adicCompletion F) : ℂ := ∏ w, (e w (y w) : ℂ)
  let g (y : (w : ↥A.Sf) → w.val.adicCompletion F) : ℂ :=
    ∏ w, (localFiniteCharacter F w.val (y w) : ℂ)
  have hf : Continuous f := by
    apply continuous_finset_prod
    intro w hw
    exact continuous_subtype_val.comp ((he w).comp (continuous_apply w))
  have hg : Continuous g := by
    apply continuous_finset_prod
    intro w hw
    exact continuous_subtype_val.comp
      ((continuous_localFiniteCharacter F w.val).comp (continuous_apply w))
  have heq : f = g := (PoissonSFiniteDensity.diagonal_denseRange F A.Sf).equalizer hf hg (by
    funext r
    have hp := htrace r
    have hc := congrArg (fun z : Circle => (z : ℂ))
      (sLocalTraceCharacter_sIntegerDiagonal_eq_one F A.Sf r)
    simp only [ProbeAdditive.TraceCompatible, ProbeAdditive.phase, sIntegerDiagonal_apply] at hp
    change ProbeAdditive.archPhase F (sLocalDiagonal F A.Sf (r : F)).1 *
      f (fun w => algebraMap F (w.val.adicCompletion F) (r : F)) = 1 at hp
    rw [sLocalTraceCharacter_apply] at hc
    simp only [sIntegerDiagonal_apply, sLocalDiagonal_infinite, sLocalDiagonal_finite] at hc
    change Circle.coeHom (∏ w : InfinitePlace F,
        archTraceCharacter w (algebraMap F w.Completion (r : F))) *
      Circle.coeHom (∏ w : ↥A.Sf,
        localFiniteCharacter F w.val (algebraMap F (w.val.adicCompletion F) (r : F))) = 1 at hc
    rw [map_prod, map_prod] at hc
    change (∏ w : InfinitePlace F,
        (archTraceCharacter w (algebraMap F w.Completion (r : F)) : ℂ)) *
      g (fun w => algebraMap F (w.val.adicCompletion F) (r : F)) = 1 at hc
    rw [← archPhase_diagonal F A] at hc
    have hn : ProbeAdditive.archPhase F (sLocalDiagonal F A.Sf (r : F)).1 ≠ 0 :=
      Complex.exp_ne_zero _
    exact mul_left_cancel₀ hn (hp.trans hc.symm))
  have hloc : ∀ (v : ↥A.Sf) (x : v.val.adicCompletion F),
      e v x = localFiniteCharacter F v.val x := by
    intro v x
    let y : (w : ↥A.Sf) → w.val.adicCompletion F := Pi.single v x
    have h := congr_fun heq y
    have prod_single (e' : (w : ↥A.Sf) → AddChar (w.val.adicCompletion F) Circle) :
        (∏ w : ↥A.Sf, (e' w (y w) : ℂ)) = (e' v x : ℂ) := by
      rw [Finset.prod_eq_single v]
      · simp [y]
      · intro w hw hwv
        simp [y, Pi.single_eq_of_ne hwv]
      · simp
    change (∏ w : ↥A.Sf, (e w (y w) : ℂ)) =
      (∏ w : ↥A.Sf, (localFiniteCharacter F w.val (y w) : ℂ)) at h
    rw [prod_single e, prod_single (fun w => localFiniteCharacter F w.val)] at h
    exact Circle.coe_injective h
  intro x
  have hcoe : (((∏ v : InfinitePlace F, archTraceCharacter v (x.1 v)) *
      (∏ v : ↥A.Sf, localFiniteCharacter F v.val (x.2 v)) : Circle) : ℂ) =
      (∏ v : InfinitePlace F, (archTraceCharacter v (x.1 v) : ℂ)) *
        (∏ v : ↥A.Sf, (localFiniteCharacter F v.val (x.2 v) : ℂ)) := by
    change Circle.coeHom (∏ v : InfinitePlace F, archTraceCharacter v (x.1 v)) *
      Circle.coeHom (∏ v : ↥A.Sf, localFiniteCharacter F v.val (x.2 v)) = _
    rw [map_prod, map_prod]
    rfl
  rw [ProbeAdditive.phase, sLocalTraceCharacter_apply, hcoe,
    ← archPhase_eq_archTraceCharacter_product F A x.1]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  rw [hloc]

end
end DedekindZetaZeroFree.TateSLocalComparison
