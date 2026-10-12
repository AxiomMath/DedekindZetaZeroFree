module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalCosetIndicators
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LocalBallCosetExpansion

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

local instance invCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance invCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

 def dualDepth (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) : ℤ :=
  -n - (localDifferentExponent F v : ℤ)

private theorem localSchwartz_mul_locallyConstant (v : HeightOneSpectrum (𝓞 F))
    (c f : v.adicCompletion F → ℂ) (hc : IsLocallyConstant c)
    (hf : f ∈ localSchwartz F v) :
    (fun y => c y * f y) ∈ localSchwartz F v :=
  ⟨hc.mul hf.1, hf.2.mul_left⟩

private theorem localFourierIntegral_modulation (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (m : ℤ) (x : v.adicCompletion F) :
    localFourierIntegral F v (fun y => (localFiniteCharacter F v (-b * y) : ℂ) *
        localCosetIndicator F v 0 (finiteCompletionBall F v m) y) x =
      localFourierIntegral F v
        (localCosetIndicator F v 0 (finiteCompletionBall F v m)) (b + x) := by
  rw [localFourierIntegral_apply, localFourierIntegral_apply]
  apply integral_congr_ae
  filter_upwards with y
  have hchar : (localFiniteCharacter F v (-b * y) : ℂ) *
        (localFiniteCharacter F v (-y * x) : ℂ) =
      (localFiniteCharacter F v (-y * (b + x)) : ℂ) := by
    have harg : (-b * y : v.adicCompletion F) + (-y * x) = -y * (b + x) := by ring
    rw [← harg, localFiniteCharacter_add, Circle.coe_mul]
  rw [← hchar]
  ring

private theorem localFourierIntegral_ballIndicator_mem (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (n : ℤ) :
    localFourierIntegral F v (localCosetIndicator F v b (finiteCompletionBall F v n)) ∈
      localSchwartz F v := by
  have hfun : localFourierIntegral F v
        (localCosetIndicator F v b (finiteCompletionBall F v n)) =
      fun y => (localBallMass F v n : ℂ) * (localFiniteCharacter F v (-b * y) : ℂ) *
        localCosetIndicator F v 0 (finiteCompletionBall F v (dualDepth F v n)) y := by
    funext y
    rw [localFourierIntegral_localCosetIndicator_ball F v n b y]
    simp only [dualDepth]
  rw [hfun]
  exact localSchwartz_mul_locallyConstant F v
    (fun y => (localBallMass F v n : ℂ) * (localFiniteCharacter F v (-b * y) : ℂ))
    (localCosetIndicator F v 0 (finiteCompletionBall F v (dualDepth F v n)))
    ((IsLocallyConstant.const _).mul (isLocallyConstant_localFiniteCharacter_neg_mul F v b))
    (localCosetIndicator_ball_mem_localSchwartz F v 0 _)

private theorem localFourierIntegral_sq_ballIndicator (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (n : ℤ) (x : v.adicCompletion F) :
    localFourierIntegral F v
        (localFourierIntegral F v (localCosetIndicator F v b (finiteCompletionBall F v n))) x =
      localCosetIndicator F v b (finiteCompletionBall F v n) (-x) := by
  have hstep : localFourierIntegral F v (localCosetIndicator F v b (finiteCompletionBall F v n)) =
      (localBallMass F v n : ℂ) •
        (fun y => (localFiniteCharacter F v (-b * y) : ℂ) *
          localCosetIndicator F v 0 (finiteCompletionBall F v (dualDepth F v n)) y) := by
    funext y
    rw [localFourierIntegral_localCosetIndicator_ball F v n b y]
    simp only [Pi.smul_apply, smul_eq_mul, dualDepth]
    ring
  rw [hstep, localFourierIntegral_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [localFourierIntegral_modulation F v b (dualDepth F v n) x]
  rw [localFourierIntegral_localCosetIndicator_ball F v (dualDepth F v n) 0 (b + x)]
  have hidx : -dualDepth F v n - (localDifferentExponent F v : ℤ) = n := by
    simp only [dualDepth]
    ring
  rw [hidx]
  have hphase : (localFiniteCharacter F v (-0 * (b + x)) : ℂ) = 1 := by simp
  simp only [hphase, mul_one]
  have hM : (localBallMass F v n : ℂ) * (localBallMass F v (dualDepth F v n) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, show localBallMass F v n * localBallMass F v (dualDepth F v n) = 1 by
      simpa only [dualDepth] using localBallMass_mul_dual F v n, Complex.ofReal_one]
  rw [← mul_assoc, hM, one_mul]
  rw [localCosetIndicator_apply, localCosetIndicator_apply]
  simp only [sub_zero]
  apply if_congr _ rfl rfl
  constructor
  · intro h
    have hh : -(b + x) ∈ finiteCompletionBall F v n := (finiteCompletionBall F v n).neg_mem h
    rwa [show -x - b = -(b + x) from by ring]
  · intro h
    have hh : -(b + x) ∈ finiteCompletionBall F v n := by
      rwa [show -x - b = -(b + x) from by ring] at h
    exact (finiteCompletionBall F v n).neg_mem_iff.mp hh

theorem localFourierIntegral_fourierIntegral
    (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ)
    (hf : f ∈ localSchwartz F v) (x : v.adicCompletion F) :
    localFourierIntegral F v (localFourierIntegral F v f) x = f (-x) := by
  obtain ⟨r, n, T, hrn, hsupp, hTsub, hdisj, hcover, hinv, hexp⟩ :=
    localSchwartz_finite_ball_coset_expansion F v f hf
  have hfsum : f = ∑ t ∈ T, f t • localCosetIndicator F v t (finiteCompletionBall F v n) := by
    funext y
    rw [hexp y]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hFTf : localFourierIntegral F v f =
      ∑ t ∈ T, f t •
        localFourierIntegral F v (localCosetIndicator F v t (finiteCompletionBall F v n)) := by
    conv_lhs => rw [hfsum]
    exact localFourierIntegral_finset_sum_smul F v T f
      (fun t => localCosetIndicator F v t (finiteCompletionBall F v n))
      (fun t _ => localCosetIndicator_ball_mem_localSchwartz F v t n)
  have hFT2 : localFourierIntegral F v (localFourierIntegral F v f) =
      ∑ t ∈ T, f t •
        localFourierIntegral F v
          (localFourierIntegral F v (localCosetIndicator F v t (finiteCompletionBall F v n))) := by
    conv_lhs => rw [hFTf]
    exact localFourierIntegral_finset_sum_smul F v T f
      (fun t => localFourierIntegral F v (localCosetIndicator F v t (finiteCompletionBall F v n)))
      (fun t _ => localFourierIntegral_ballIndicator_mem F v t n)
  rw [hFT2]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hexp (-x)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [localFourierIntegral_sq_ballIndicator F v t n x]

def localInverseFourierIntegral (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) : v.adicCompletion F → ℂ :=
  fun x => localFourierIntegral F v f (-x)

@[simp] theorem localInverseFourierIntegral_apply
    (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ)
    (x : v.adicCompletion F) :
    localInverseFourierIntegral F v f x = localFourierIntegral F v f (-x) := rfl

theorem localInverseFourierIntegral_fourierIntegral
    (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ)
    (hf : f ∈ localSchwartz F v) :
    localInverseFourierIntegral F v (localFourierIntegral F v f) = f := by
  funext x
  rw [localInverseFourierIntegral_apply, localFourierIntegral_fourierIntegral F v f hf]
  simp

end DedekindZetaZeroFree

end
