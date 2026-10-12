module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.TraceAnnihilator
public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerDiscreteness
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

noncomputable section
open scoped Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.ProbeFourierPoissonFoundation

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

abbrev finiteCharacter (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  fun v : S => localFiniteCharacter F v.val

abbrev finiteHaar (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  fun v : S => localNormalizedHaar F v.val

abbrev productHaar (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  PoissonS.productMeasure F S (finiteHaar F S)

abbrev phase (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  PoissonS.tracePhase F S (finiteCharacter F S)

abbrev fourier (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  PoissonS.fourierIntegral F S (finiteCharacter F S) (finiteHaar F S)

private theorem norm_le_one_iff (v : HeightOneSpectrum (RingOfIntegers F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [FinitePlace.norm_def]
  change (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤ 1 ↔ _
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  apply WithZeroMulInt.toNNReal_le_one_iff
  exact_mod_cast RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v

private theorem localNormalization_finiteHaar
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    PoissonS.LocalNormalization F S (finiteHaar F S) := by
  intro v
  have hset : {x : v.val.adicCompletion F | ‖x‖ ≤ 1} =
      (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)) := by
    ext x
    rw [Set.mem_setOf_eq, norm_le_one_iff F v.val x]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := F)
      (v := v.val)).symm
  rw [hset, localNormalizedHaar_integerRing]
  congr 1
  rw [PoissonS.integerVolume,
    FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F v.val,
    zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F v.val, localDifferentNorm,
    Nat.cast_pow, one_div]

private theorem productHaar_isAddHaarMeasure
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    (productHaar F S).IsAddHaarMeasure := by
  haveI : (PoissonArch.traceMeasure F).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume
      (ne_of_gt (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos F))) ENNReal.ofReal_ne_top
  haveI : SigmaFinite (PoissonArch.traceMeasure F) := inferInstance
  haveI : SigmaFinite (Measure.pi (finiteHaar F S)) := inferInstance
  unfold productHaar PoissonS.productMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem phase_eq_traceCharacter
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (x y : PoissonS.Space F S) :
    phase F S x y =
      (sLocalTraceCharacter F S
        ((PoissonS.localProductToSpace F S).symm x *
          (PoissonS.localProductToSpace F S).symm y) : ℂ) := by
  have harch (u v : InfiniteAdeleRing F) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u)
          (PoissonArch.infiniteAdeleToSpace F v) : ℂ)) =
        ∏ w : InfinitePlace F, (archTraceCharacter w (u w * v w) : ℂ) := by
    have htrace : PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u)
        (PoissonArch.infiniteAdeleToSpace F v) =
        ∑ w : InfinitePlace F, archTrace w (u w * v w) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
      unfold PoissonArch.tracePairing
      rw [PoissonArch.infiniteAdeleToSpace_coordinates,
        PoissonArch.infiniteAdeleToSpace_coordinates]
      dsimp only
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [archTrace_of_isReal w.val w.property, map_mul]
        rfl
      · rw [Finset.mul_sum]
        apply Fintype.sum_equiv
          (Equiv.subtypeEquivRight fun w : InfinitePlace F =>
            InfinitePlace.not_isReal_iff_isComplex).symm
        intro w
        change 2 * _ = archTrace w.val (u w.val * v w.val)
        rw [archTrace_of_isComplex w.val w.property, map_mul]
        rfl
    rw [htrace, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro w hw
    change _ = (Circle.exp (2 * Real.pi * archTrace w (u w * v w)) : ℂ)
    rw [Circle.coe_exp]
    push_cast
    ring_nf
  let u := (PoissonS.localProductToSpace F S).symm x
  let v := (PoissonS.localProductToSpace F S).symm y
  have hx : PoissonArch.infiniteAdeleToSpace F u.1 = x.1 :=
    congrArg Prod.fst ((PoissonS.localProductToSpace F S).apply_symm_apply x)
  have hy : PoissonArch.infiniteAdeleToSpace F v.1 = y.1 :=
    congrArg Prod.fst ((PoissonS.localProductToSpace F S).apply_symm_apply y)
  have hx2 : u.2 = x.2 := rfl
  have hy2 : v.2 = y.2 := rfl
  rw [sLocalTraceCharacter_apply]
  simp only [Circle.coe_mul, map_prod, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  unfold phase PoissonS.tracePhase
  rw [← hx, ← hy, harch]
  change _ = Circle.coeHom (∏ w : InfinitePlace F, archTraceCharacter w (u.1 w * v.1 w)) *
    Circle.coeHom (∏ w : S, localFiniteCharacter F w.val (u.2 w * v.2 w))
  rw [map_prod, map_prod]
  rfl

theorem productHaar_normalization
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    (productHaar F S).IsAddHaarMeasure ∧
    PoissonS.LocalNormalization F S (finiteHaar F S) ∧
    (∀ (f : PoissonS.Space F S → ℂ) (y : PoissonS.Space F S),
      fourier F S f y =
        ∫ x, f x * (sLocalTraceCharacter F S
          (-((PoissonS.localProductToSpace F S).symm x *
            (PoissonS.localProductToSpace F S).symm y)) : ℂ) ∂productHaar F S) := by
  refine ⟨productHaar_isAddHaarMeasure F S, localNormalization_finiteHaar F S, ?_⟩
  intro f y
  unfold fourier PoissonS.fourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← neg_mul, ← map_neg (PoissonS.localProductToSpace F S).symm,
    ← phase_eq_traceCharacter F S (-x) y]
  unfold phase PoissonS.tracePhase
  simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply,
    PoissonArch.tracePairing_eq_inner, inner_neg_left, Complex.ofReal_neg]
  rw [← mul_assoc]
  congr 2
  congr 1
  ring

end DedekindZetaZeroFree.ProbeFourierPoissonFoundation

end
